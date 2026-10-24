(* An operational lexical machine for Native's actual decoded expression
   grammar. Concurrent global updates cannot mutate private code or frames.
   Chez-to-machine simulation is an explicit remaining native obligation. *)
From Coq Require Import List String Relation_Operators.
From Buri Require Import Native.
Import ListNotations.
Module NativeRuntime.
Import Native.Native.
Inductive control := Enter (rho : env) (e : expr) | Deliver (v : value) | Fault (r : result).
Inductive frame :=
 | Choose (rho : env) (a b : expr)
 | Bind (rho : env) (name : string) (body : expr)
 | Conjoin (rho : env) (b : expr) | Disjoin (rho : env) (b : expr)
 | Arguments (rho : env) (name : string) (remaining : list expr) (reversed : list value).
Definition machine := (control * list frame)%type.
Definition apply (p : program) name vs stack : machine := match p name with
 | Some d => if Nat.eqb (List.length (params d)) (List.length vs)
   then (Enter (arguments (params d) vs) (body d),stack)
   else (Fault Unsupported,stack)
 | None => match name,vs with
   | "error",[owner;message] => (Fault (Raised owner message),stack)
   | _,_ => match primitive name vs with
     | Some v => (Deliver v,stack) | _ => (Fault Unsupported,stack) end end end.
Definition step (p : program) (state : machine) : option machine :=
 match state with
 | (Enter rho (Lit v),k) => Some (Deliver v,k)
 | (Enter rho (Var s),k) => Some (match rho s with Some v => Deliver v | _ => Fault Unsupported end,k)
 | (Enter rho (If c a b),k) => Some (Enter rho c,Choose rho a b::k)
 | (Enter rho (Let s a b),k) => Some (Enter rho a,Bind rho s b::k)
 | (Enter rho (And a b),k) => Some (Enter rho a,Conjoin rho b::k)
 | (Enter rho (Or a b),k) => Some (Enter rho a,Disjoin rho b::k)
 | (Enter rho (Call s []),k) => Some (apply p s [] k)
 | (Enter rho (Call s (a::args)),k) => Some (Enter rho a,Arguments rho s args []::k)
 | (Deliver v,Choose rho a b::k) => Some (Enter rho (match v with Boolean false => b | _ => a end),k)
 | (Deliver v,Bind rho s b::k) => Some (Enter (bind rho s v) b,k)
 | (Deliver v,Conjoin rho b::k) => Some (match v with Boolean false => Deliver (Boolean false) | _ => Enter rho b end,k)
 | (Deliver v,Disjoin rho b::k) => Some (match v with Boolean false => Enter rho b | _ => Deliver v end,k)
 | (Deliver v,Arguments rho s [] acc::k) => Some (apply p s (rev (v::acc)) k)
 | (Deliver v,Arguments rho s (a::args) acc::k) => Some (Enter rho a,Arguments rho s args (v::acc)::k)
 | _ => None end.
Definition transition p a b := step p a = Some b.
Definition reaches p := clos_refl_trans_1n machine (transition p).
Fixpoint execute fuel p m := match m with
 | (Deliver v,[]) => Returned v
 | (Fault (Returned _),_) => Unsupported
 | (Fault r,_) => r
 | _ => match fuel with
   | O => Exhausted
   | S n => match step p m with Some m' => execute n p m' | None => Unsupported end end end.
Definition invoke fuel ds name args := match lookup ds name with
 | Some d => if Nat.eqb (List.length (params d)) (List.length args)
   then execute fuel (lookup ds) (Enter (arguments (params d) args) (body d),[]) else Unsupported
 | _ => Unsupported end.
Theorem execute_trace : forall fuel p m v,
 execute fuel p m = Returned v -> reaches p m (Deliver v,[]).
Proof.
 induction fuel as [|n IH]; intros p [c k] v H; destruct c;
   destruct k as [|f k]; cbn [execute] in H; try discriminate;
   try (inversion H; subst; constructor);
   try (destruct r; discriminate).
 all: destruct (step p _) as [m'|] eqn:E; try discriminate;
   eapply rt1n_trans; [exact E|]; eapply IH; eauto.
Qed.
Theorem step_deterministic : forall p a b c,
 transition p a b -> transition p a c -> b = c.
Proof. unfold transition; congruence. Qed.
Theorem terminal_unique : forall p a b, reaches p a b -> forall c,
 reaches p a c -> step p b = None -> step p c = None -> b = c.
Proof.
 intros p a b H; induction H; intros c C B T.
 - inversion C; subst; auto. unfold transition in H; congruence.
 - inversion C; subst.
   + unfold transition in H; congruence.
   + assert (y = y0) by (eapply step_deterministic; eauto). subst; eauto.
Qed.
(* A world may contain arbitrary values/procedures and be replaced between
   any two machine instructions. It has no access to the capsule's cells. *)
Definition world := string -> option value.
Inductive interleaved (p : program) : (machine * world) -> (machine * world) -> Prop :=
 | Local : forall m m' w, transition p m m' -> interleaved p (m,w) (m',w)
 | Rebind : forall m w w', interleaved p (m,w) (m,w').
Definition concurrent_reaches p := clos_refl_trans_1n (machine * world) (interleaved p).
Theorem erase_rebindings : forall p a b,
 concurrent_reaches p a b -> reaches p (fst a) (fst b).
Proof.
 intros p a b H; induction H; [constructor|].
 inversion H; subst; cbn in *.
 - eapply rt1n_trans; eauto.
 - exact IHclos_refl_trans_1n.
Qed.
Theorem concurrent_output_unique : forall p start wa wb wc x y,
 concurrent_reaches p (start,wa) ((Deliver x,[]),wb) ->
 concurrent_reaches p (start,wa) ((Deliver y,[]),wc) -> x = y.
Proof.
 intros p start wa wb wc x y X Y.
 apply erase_rebindings in X; apply erase_rebindings in Y; cbn in X,Y.
 assert ((Deliver x,[]) = (Deliver y,[])) as E by
  (eapply terminal_unique; eauto; reflexivity).
 inversion E; reflexivity.
Qed.
(* Running a private machine step with any ambient world gives the same
   next private machine state. This includes the actual parsed helper bodies. *)
Theorem every_world_schedule_preserves_trace : forall p start finish w w',
 concurrent_reaches p (start,w) (finish,w') ->
 reaches p start finish.
Proof. intros; apply erase_rebindings in H; exact H. Qed.
End NativeRuntime.
