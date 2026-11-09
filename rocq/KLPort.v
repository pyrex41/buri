(* Per-port options on the KLambda semantics (E2E-06, E2E-37). KLSemantics.next is the agreed
   semantics, unchanged, and every theorem about it stands. `next_r R` is the same machine with
   the eight points listed in docs/SHEN-JIT.md open to a port, and `next_r_agreed` proves that
   the agreed options give exactly `next`, for every profile and configuration. So the options
   cannot alter what the Scheme and CL lanes rely on, and a drift of this copy from KLSemantics.v
   stops that proof.

   A port's options are part of the claim made about it. Nothing here relates any port to this
   semantics: that is what its refinement theorem has to do. *)
From Coq Require Import List ZArith NArith String Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics.
Import ListNotations.
Module KLPort.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.

Record port_rules := PortRules {
 (* 1. Integer results outside this range raise XPrim, in place of unbounded integers. *)
 int_range : option (Z * Z);
 (* 2. The string n->string makes of an integer, or None where it raises. The agreed rule makes a
    one-unit string of a scalar value; a byte-string port may make several bytes of one. *)
 char_text : Z -> option text;
 (* 3. Closures carry an identity, one location each, and = compares it. Two exceptions
    remain undefined under =: see `eq_opaque_r`. *)
 object_identity : bool;
 (* 4. A named call of the wrong argument count raises XArity; there is no VPartial. *)
 arity_errors : bool;
 (* 5. Whether defun of this name is allowed in this store; if not, it raises XBadDefinition. *)
 defun_allowed : store -> name -> bool;
 (* 6. Which clock names get-time asks the environment about; others raise before any request. *)
 time_kind_ok : text -> bool;
 (* 7. write-byte returns its byte whatever the environment answers. *)
 unchecked_writes : bool;
 (* 8. The catchable error this resource failure raises, if it is catchable. *)
 resource_exn : resource -> option exn }.

(* The agreed options: every one is what KLSemantics.v does. *)
Definition agreed_rules : port_rules := PortRules
 None (fun z => if scalar_ok z then Some [Z.to_N z] else None) false false (fun _ _ => true) (fun _ => true) false (fun _ => None).

(* ---------- 1: integer range ---------- *)
Definition in_range (R : port_rules) (z : Z) : bool := match int_range R with
 | None => true
 | Some (lo, hi) => (Z.leb lo z && Z.leb z hi)%bool end.

Definition rule_arith_r R P p (iop : Z -> Z -> Z) args s := match args with
 | [VNum (NInt x); VNum (NInt y)] =>
   if in_range R (iop x y) then rule_arith P p iop args s else dom p
 | _ => rule_arith P p iop args s end.

Definition rule_div_r R P args s := match args with
 | [VNum (NInt x); VNum (NInt y)] =>
   if negb (Z.eqb y 0) && Z.eqb (Z.rem x y) 0 && negb (in_range R (Z.quot x y))
   then dom PDiv else rule_div P args s
 | _ => rule_div P args s end.

(* ---------- 2: characters ---------- *)
Definition rule_n_to_string_r R args s := match args with
 | [VNum (NInt z)] => match char_text R z with Some t => ret (VStr t) s | None => dom PNToString end
 | _ => dom PNToString end.

(* ---------- 3: identity ---------- *)
(* A closure's identity is a location, kept under a name no parsed program can read: a body
   reads this name only if its own lambda binds it, which shadows the entry and leaves the
   identity below. *)
Definition id_key : name := [0%N; 105%N; 100%N].
Definition closure_id (rho : lenv) : option nat := match rho with
 | (k, VVec l) :: _ => if text_eqb k id_key then Some l else None
 | _ => None end.

Definition opaque_eq (a b : value) : option bool := match a, b with
 | VLam _ _ r1, VLam _ _ r2 | VFrozen _ r1, VFrozen _ r2 =>
   match closure_id r1, closure_id r2 with
   | Some x, Some y => Some (Nat.eqb x y)
   | _, _ => None end
 | VLam _ _ _, VFrozen _ _ | VFrozen _ _, VLam _ _ _ => Some false
 | _, _ => None end.

(* What = answers on two closures, partial applications or exceptions. An exception has no
   location to compare: `exn` has no room for one, so two exceptions stay undefined, which
   the ledger tracks as OB-JIT-DEV-IDENTITY. *)
Definition eq_opaque_r (R : port_rules) (a b : value) : option bool :=
 if object_identity R then opaque_eq a b else None.

Fixpoint eq_depth_r (R : port_rules) (P : profile) (h : list (list value)) (d : nat) {struct d}
  : value -> value -> option bool :=
 match d with
 | O => fun _ _ => None
 | S d' => fix go (a b : value) {struct a} : option bool :=
   match a, b with
   | VNum x, VNum y => Some (num_cmp P PEqual x y)
   | VSym x, VSym y | VStr x, VStr y => Some (text_eqb x y)
   | VBool x, VBool y => Some (Bool.eqb x y)
   | VNil, VNil => Some true
   | VCons a1 a2, VCons b1 b2 => match go a1 b1 with Some true => go a2 b2 | r => r end
   | VStream x, VStream y => Some (N.eqb x y)
   | VVec l1, VVec l2 => if Nat.eqb l1 l2 then Some true else
       match nth_error h l1, nth_error h l2 with
       | Some xs, Some ys => list_eq (eq_depth_r R P h d') xs ys
       | _, _ => None end
   | (VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _), _ => match b with
       | VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _ => eq_opaque_r R a b | _ => Some false end
   | _, (VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _) => Some false
   | _, _ => Some false end end.
Definition kl_eq_r R P h a b := eq_depth_r R P h (S (List.length h)) a b.

Definition rule_equal_r R P args s := match args with
 | [a; b] => match kl_eq_r R P (heap s) a b with
   | Some r => ret (VBool r) s | None => PDone (OWrong (kw "equality-undefined")) end
 | _ => dom PEqual end.

(* A new closure takes the next location, an empty cell of the heap. *)
Definition tagged_env (rho : lenv) (s : store) : lenv :=
 (id_key, VVec (List.length (heap s))) :: rho.
Definition with_cell (s : store) : store :=
 Store (heap s ++ [[]]) (gvals s) (gfuns s).

(* ---------- 6 and 7: clock and writes ---------- *)
Definition rule_get_time_r R P args s := match args with
 | [VSym k] => if time_kind_ok R k then rule_get_time P args s else dom PGetTime
 | _ => rule_get_time P args s end.

Definition rule_write_byte_r R args s :=
 if unchecked_writes R then match args with
 | [VNum (NInt b); VStream h] => if (Z.leb 0 b && Z.ltb b 256)%bool
   then PIO (QWrite h [Z.to_N b]) (fun _ => ORet (VNum (NInt b)) s)
   else dom PWriteByte
 | _ => dom PWriteByte end
 else rule_write_byte args s.

(* The primitive table: the agreed rule, except where an option applies. *)
Definition prim_rule_r (R : port_rules) (P : profile) (p : prim) (args : list value) (s : store) : presult :=
 match p with
 | PNToString => rule_n_to_string_r R args s
 | PEqual => rule_equal_r R P args s
 | PWriteByte => rule_write_byte_r R args s
 | PGetTime => rule_get_time_r R P args s
 | PAdd => rule_arith_r R P PAdd Z.add args s
 | PSub => rule_arith_r R P PSub Z.sub args s
 | PMul => rule_arith_r R P PMul Z.mul args s
 | PDiv => rule_div_r R P args s
 | _ => prim_rule P p args s end.

(* ---------- machine ---------- *)
Definition prim_move_r R P p args rest k s : move :=
 match prim_rule_r R P p args s with
 | PDone o => MTau (pout_config P o rest k s)
 | PIO q kont => MIO q (fun r => pout_config P (kont r) rest k s) end.

(* 4: a call that does not match the arity raises, when the port has no partial application. *)
Definition arity_mismatch (R : port_rules) (given want : nat) : bool :=
 arity_errors R && negb (Nat.eqb given want).

Definition call_named_r R P (g : name) (args : list value) (k : list frame) (s : store) : move :=
 match lookup g (gfuns s) with
 | None => MTau (Cfg (Throw (XUndefinedFun g)) k s)
 | Some (FUser ps body) =>
   if arity_mismatch R (List.length args) (List.length ps) then MTau (Cfg (Throw XArity) k s)
   else if Nat.ltb (List.length args) (List.length ps) then MTau (Cfg (Ret (VPartial g args)) k s)
   else MTau (continue_with P (skipn (List.length ps) args) k
                (Eval (combine ps (firstn (List.length ps) args)) body) s)
 | Some (FPrim p) =>
   if arity_mismatch R (List.length args) (prim_arity p) then MTau (Cfg (Throw XArity) k s)
   else if Nat.ltb (List.length args) (prim_arity p) then MTau (Cfg (Ret (VPartial g args)) k s)
   else prim_move_r R P p (firstn (prim_arity p) args) (skipn (prim_arity p) args) k s end.

Definition apply_value_r R P (f : value) (args : list value) (k : list frame) (s : store) : move :=
 match f, args with
 | VFrozen body rho, [] => MTau (Cfg (Eval rho body) k s)
 | VLam x body rho, a :: rest => MTau (continue_with P rest k (Eval ((x, a) :: rho) body) s)
 | VPartial g prev, _ => call_named_r R P g (prev ++ args) k s
 | VFrozen _ _, _ :: _ | VLam _ _ _, [] => MTau (Cfg (Throw XArity) k s)
 | _, _ => MTau (Cfg (Throw XNotCallable) k s) end.

Definition eval_move_r R P (rho : lenv) (e : expr) (k : list frame) (s : store) : move :=
 match e with
 | ELam x b => if object_identity R
     then MTau (Cfg (Ret (VLam x b (tagged_env rho s))) k (with_cell s))
     else MTau (Cfg (Ret (VLam x b rho)) k s)
 | EFreeze b => if object_identity R
     then MTau (Cfg (Ret (VFrozen b (tagged_env rho s))) k (with_cell s))
     else MTau (Cfg (Ret (VFrozen b rho)) k s)
 | EDefun f ps b =>
   if defun_allowed R s f then
     if nodupb ps then
       MTau (Cfg (Ret (VSym f)) k (Store (heap s) (gvals s) ((f, FUser ps b) :: gfuns s)))
     else MTau (Cfg (Throw XBadDefinition) k s)
   else MTau (Cfg (Throw XBadDefinition) k s)
 | ECall f [] => call_named_r R P f [] k s
 | _ => eval_move P rho e k s end.

Definition ret_move_r R P (v : value) (f : frame) (k : list frame) (s : store) : move :=
 match f with
 | KHead [] rho => apply_value_r R P v [] k s
 | KArgs fv done [] rho => apply_value_r R P fv (rev (v :: done)) k s
 | KCallArgs g done [] rho => call_named_r R P g (rev (v :: done)) k s
 | KApply args => apply_value_r R P v args k s
 | _ => ret_move P v f k s end.

(* 8: a resource failure the port makes catchable is an ordinary raise. *)
Definition next_r (R : port_rules) (P : profile) (c : config) : move :=
 match ctl c with
 | Eval rho e => eval_move_r R P rho e (kont c) (mem c)
 | Ret v => match kont c with [] => MFinal (Normal v) | f :: k => ret_move_r R P v f k (mem c) end
 | Throw x => match kont c with [] => MFinal (Error x) | f :: k => throw_move x f k (mem c) end
 | Fail r => match resource_exn R r with
   | Some x => MTau (Cfg (Throw x) (kont c) (mem c))
   | None => MFinal (ResourceOut r) end
 | Halted (Signal sg) => MFinal (Killed sg)
 | Halted Cancel => MFinal Cancelled
 | Wrong w => MWrong w end.

(* A real machine runs out of memory where this semantics counts nothing: profile limits are
   cells and frames, not bytes. So a port with catchable resources may raise at any evaluation
   or return. This is a permission of the source semantics, and a broad one: narrowing it to
   allocation and call points is tracked by OB-JIT-RESOURCES. *)
Definition running_state (c : config) : bool := match ctl c with
 | Eval _ _ | Ret _ => true | _ => false end.

Inductive step_r (R : port_rules) (P : profile) : config -> label -> config -> Prop :=
 | step_r_tau c c' : next_r R P c = MTau c' -> step_r R P c Tau c'
 | step_r_io c q kk r : next_r R P c = MIO q kk -> step_r R P c (Obs (EvIO q r)) (kk r)
 | step_r_resource c r x :
     running_state c = true -> resource_exn R r = Some x ->
     step_r R P c Tau (Cfg (Throw x) (kont c) (mem c)).

(* ---------- the agreed options are exactly the agreed semantics ---------- *)
Lemma eq_depth_r_agreed : forall P h d a b,
 eq_depth_r agreed_rules P h d a b = eq_depth P h d a b.
Proof.
 intros P h d. induction d as [|d IH]; intros a b; [reflexivity|].
 assert (L : forall xs ys, list_eq (eq_depth_r agreed_rules P h d) xs ys = list_eq (eq_depth P h d) xs ys).
 { induction xs as [|x xs IHx]; destruct ys as [|y ys]; cbn; try reflexivity.
   rewrite IH. destruct (eq_depth P h d x y) as [[|]|]; try reflexivity. apply IHx. }
 revert b. induction a; intro w; destruct w; cbn; try reflexivity.
 - change (match eq_depth_r agreed_rules P h (S d) a1 w1 with Some true => eq_depth_r agreed_rules P h (S d) a2 w2 | r => r end
     = match eq_depth P h (S d) a1 w1 with Some true => eq_depth P h (S d) a2 w2 | r => r end).
   rewrite IHa1, IHa2. reflexivity.
 - destruct (Nat.eqb l l0); [reflexivity|].
   destruct (nth_error h l), (nth_error h l0); try reflexivity. apply L.
Qed.

Lemma kl_eq_r_agreed : forall P h a b, kl_eq_r agreed_rules P h a b = kl_eq P h a b.
Proof. intros. apply eq_depth_r_agreed. Qed.

Lemma in_range_agreed : forall z, in_range agreed_rules z = true.
Proof. reflexivity. Qed.

Lemma rule_equal_agreed : forall P args s, rule_equal_r agreed_rules P args s = rule_equal P args s.
Proof.
 intros. unfold rule_equal_r, rule_equal.
 destruct args as [|a [|b [|c args]]]; try reflexivity. rewrite kl_eq_r_agreed. reflexivity.
Qed.
Lemma rule_get_time_agreed : forall P args s, rule_get_time_r agreed_rules P args s = rule_get_time P args s.
Proof. intros. unfold rule_get_time_r. destruct args as [|a [|b args]]; try reflexivity; destruct a; reflexivity. Qed.
Lemma rule_arith_agreed : forall P p iop args s, rule_arith_r agreed_rules P p iop args s = rule_arith P p iop args s.
Proof.
 intros. unfold rule_arith_r. destruct args as [|a args]; [reflexivity|].
 destruct a as [n| | | | | | | | | | |]; try reflexivity. destruct n; destruct args as [|b args]; try reflexivity;
 destruct b as [m| | | | | | | | | | |]; try reflexivity; destruct m; destruct args; reflexivity.
Qed.
Lemma rule_div_agreed : forall P args s, rule_div_r agreed_rules P args s = rule_div P args s.
Proof.
 intros. unfold rule_div_r. destruct args as [|a args]; [reflexivity|].
 destruct a as [n| | | | | | | | | | |]; try reflexivity. destruct n; destruct args as [|b args]; try reflexivity;
 destruct b as [m| | | | | | | | | | |]; try reflexivity; destruct m; destruct args; try reflexivity.
 rewrite in_range_agreed. cbn [negb]. rewrite andb_false_r. reflexivity.
Qed.
Lemma rule_n_to_string_agreed : forall args s, rule_n_to_string_r agreed_rules args s = rule_n_to_string args s.
Proof.
 intros args s. unfold rule_n_to_string_r, rule_n_to_string. cbn [char_text agreed_rules].
 destruct args as [|a [|b args]]; try reflexivity. destruct a; try reflexivity. destruct n; try reflexivity.
 destruct (scalar_ok z); reflexivity.
Qed.
Lemma rule_write_byte_agreed : forall args s, rule_write_byte_r agreed_rules args s = rule_write_byte args s.
Proof. reflexivity. Qed.

Lemma prim_rule_r_agreed : forall P p args s,
 prim_rule_r agreed_rules P p args s = prim_rule P p args s.
Proof.
 intros P p args s. destruct p; first
  [ reflexivity | apply rule_equal_agreed | apply rule_get_time_agreed
  | apply rule_arith_agreed | apply rule_div_agreed | apply rule_n_to_string_agreed ].
Qed.

Lemma prim_move_r_agreed : forall P p args rest k s,
 prim_move_r agreed_rules P p args rest k s = prim_move P p args rest k s.
Proof. intros. unfold prim_move_r, prim_move. rewrite prim_rule_r_agreed. reflexivity. Qed.

Lemma call_named_r_agreed : forall P g args k s,
 call_named_r agreed_rules P g args k s = call_named P g args k s.
Proof.
 intros. unfold call_named_r, call_named, arity_mismatch. cbn [arity_errors agreed_rules andb].
 destruct (lookup g (gfuns s)) as [[p|ps b]|]; try reflexivity.
 destruct (Nat.ltb (List.length args) (prim_arity p)); [reflexivity|]. apply prim_move_r_agreed.
Qed.

Lemma apply_value_r_agreed : forall P f args k s,
 apply_value_r agreed_rules P f args k s = apply_value P f args k s.
Proof.
 intros. destruct f; try reflexivity; destruct args; try reflexivity; apply call_named_r_agreed.
Qed.

Lemma eval_move_r_agreed : forall P rho e k s,
 eval_move_r agreed_rules P rho e k s = eval_move P rho e k s.
Proof.
 intros. destruct e; try reflexivity. destruct args; try reflexivity. apply call_named_r_agreed.
Qed.

Lemma ret_move_r_agreed : forall P v f k s,
 ret_move_r agreed_rules P v f k s = ret_move P v f k s.
Proof.
 intros. destruct f; cbn; try reflexivity;
 try apply apply_value_r_agreed; try apply call_named_r_agreed;
 match goal with
 | l : list expr |- _ => destruct l; try reflexivity; first [apply apply_value_r_agreed | apply call_named_r_agreed]
 end.
Qed.

(* The options cannot change the agreed semantics: for every profile and configuration. *)
Theorem next_r_agreed : forall P c, next_r agreed_rules P c = next P c.
Proof.
 intros P [ctl0 k s]. unfold next_r, next. cbn [ctl kont mem].
 destruct ctl0; try reflexivity.
 - apply eval_move_r_agreed.
 - destruct k; [reflexivity|]. apply ret_move_r_agreed.
Qed.

Theorem step_r_agreed : forall P c l c', step_r agreed_rules P c l c' <-> step P c l c'.
Proof.
 intros P c l c'. split; intro H.
 - inversion H; subst.
   + apply step_tau. rewrite <- next_r_agreed. assumption.
   + apply step_io. rewrite <- next_r_agreed. assumption.
   + discriminate.
 - inversion H; subst.
   + apply step_r_tau. rewrite next_r_agreed. assumption.
   + apply step_r_io. rewrite next_r_agreed. assumption.
Qed.

(* ---------- what the options say ---------- *)
Theorem range_raises : forall R P p iop x y s,
 in_range R (iop x y) = false ->
 rule_arith_r R P p iop [VNum (NInt x); VNum (NInt y)] s = dom p.
Proof. intros R P p iop x y s H. unfold rule_arith_r. rewrite H. reflexivity. Qed.

Theorem no_partial_application : forall R P g args k s ps b,
 arity_errors R = true -> lookup g (gfuns s) = Some (FUser ps b) ->
 List.length args <> List.length ps ->
 call_named_r R P g args k s = MTau (Cfg (Throw XArity) k s).
Proof.
 intros R P g args k s ps b A L N. unfold call_named_r, arity_mismatch. rewrite L, A. cbn.
 destruct (Nat.eqb (List.length args) (List.length ps)) eqn:E.
 - apply Nat.eqb_eq in E. contradiction.
 - reflexivity.
Qed.

Theorem defun_refused : forall R P rho f ps b k s,
 defun_allowed R s f = false ->
 eval_move_r R P rho (EDefun f ps b) k s = MTau (Cfg (Throw XBadDefinition) k s).
Proof. intros R P rho f ps b k s H. cbn. rewrite H. reflexivity. Qed.

Theorem unchecked_write_returns : forall R b h s r,
 unchecked_writes R = true -> (0 <= b < 256)%Z ->
 exists kk, rule_write_byte_r R [VNum (NInt b); VStream h] s = PIO (QWrite h [Z.to_N b]) kk /\
   kk r = ORet (VNum (NInt b)) s.
Proof.
 intros R b h s r U [L H]. unfold rule_write_byte_r. rewrite U.
 assert (E : (Z.leb 0 b && Z.ltb b 256)%bool = true).
 { apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; assumption. }
 rewrite E. eexists. split; reflexivity.
Qed.

Theorem catchable_resource : forall R P r x k s,
 resource_exn R r = Some x -> next_r R P (Cfg (Fail r) k s) = MTau (Cfg (Throw x) k s).
Proof. intros R P r x k s H. cbn. rewrite H. reflexivity. Qed.

(* Two closures made one after the other are different objects, and each equals itself. *)
Theorem closure_identity : forall R P h x b r1 r2,
 object_identity R = true ->
 kl_eq_r R P h (VLam x b ((id_key, VVec 0) :: r1)) (VLam x b ((id_key, VVec 0) :: r1)) = Some true /\
 kl_eq_r R P h (VLam x b ((id_key, VVec 0) :: r1)) (VLam x b ((id_key, VVec 1) :: r2)) = Some false.
Proof.
 intros R P h x b r1 r2 I. unfold kl_eq_r. cbn [eq_depth_r]. unfold eq_opaque_r. rewrite I.
 split; reflexivity.
Qed.

(* The machine is a function, so a port without catchable resources is deterministic. *)
Theorem step_r_deterministic_tau : forall R P c c1 c2,
 (forall r, resource_exn R r = None) ->
 step_r R P c Tau c1 -> step_r R P c Tau c2 -> c1 = c2.
Proof.
 intros R P c c1 c2 N H1 H2.
 inversion H1; subst; [|rewrite N in *; discriminate].
 inversion H2; subst; [|rewrite N in *; discriminate]. congruence.
Qed.
End KLPort.
