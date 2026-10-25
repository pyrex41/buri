(* Stateful semantics for the captured installer's first-order effectful code.
   Effects have explicit responses: no claim that a host response is truthful. *)
From Coq Require Import List String ZArith.
From Buri Require Import Native ObserverInput.
Import ListNotations.
Module ObserverEffects.
Import Native.Native.
Open Scope string_scope.
Inductive event := Arity (name count:value) | Compile (source:value) (response:result)
 | Activate (target:value) (response:result) | ReadRecords | WriteRecords (records:value)
 | WriteFile (path text:value) (response:result) | ReadFile (path text:value).
Record outcome := Out { answer:result; records:value; trace:list event }.
Definition computation := value -> outcome.
Definition return_result r : computation := fun st => Out r st [].
Definition ret v := return_result (Returned v).
Definition bind (m:computation) (k:value->computation) : computation := fun st =>
 let o:=m st in match answer o with
 | Returned v => let next:=k v (records o) in Out (answer next) (records next) (trace o ++ trace next)
 | _ => o end.
Definition effect r st es := Out r st es.
Definition dispatch (compiler activate:value->result) op vs : computation := fun st =>
 match op,vs with
 | "kl:length",[xs] => match elements xs with
   | Some xs => Out (Returned (Integer (Z.of_nat (List.length xs)))) st []
   | None => Out Unsupported st [] end
 | "kl:shen.store-arity",[name;count] => Out (Returned name) st [Arity name count]
 | "kl:_scm.kl->scheme",[source] => Out (compiler source) st [Compile source (compiler source)]
 | "eval",[target] => Out (activate target) st [Activate target (activate target)]
 | "kl:value",[Symbol "buri.observed"] => Out (Returned st) st [ReadRecords]
 | "kl:set",[Symbol "buri.observed";new] => Out (Returned new) new [WriteRecords new]
 | "begin",_ => Out (Returned (last vs Nil)) st []
 | _,_ => Out (external op vs) st [] end.
Fixpoint eval_with fuel (p:program) (operation:string->list value->computation) (rho:env) e : computation :=
 match fuel with
 | O => return_result Exhausted
 | S n =>
   let run:=eval_with n p operation in
   let many:=fix many es (k:list value -> computation) := match es with
    | [] => k []
    | a::rest => bind (run rho a) (fun v => many rest (fun vs => k (v::vs))) end in
   match e with
   | Lit v => ret v
   | Var s => match rho s with Some v => ret v | None => return_result Unsupported end
   | If c a b => bind (run rho c) (fun v => run rho (match v with Boolean false=>b|_=>a end))
   | Let s a b => bind (run rho a) (fun v => run (Native.bind rho s v) b)
   | And a b => bind (run rho a) (fun v => match v with Boolean false=>ret v|_=>run rho b end)
   | Or a b => bind (run rho a) (fun v => match v with Boolean false=>run rho b|_=>ret v end)
   | Call name es => many es (fun vs => match p name with
     | Some d => if Nat.eqb (List.length (params d)) (List.length vs)
       then run (arguments (params d) vs) (body d) else return_result Unsupported
     | None => operation name vs end)
   end end.
Definition eval fuel p compiler activate := eval_with fuel p (dispatch compiler activate).
Definition invoke fuel compiler activate name args : computation :=
 match lookup observer_program name with
 | Some d => if Nat.eqb (List.length (params d)) (List.length args)
   then eval fuel (lookup observer_program) compiler activate (arguments (params d) args) (body d)
   else return_result Unsupported
 | None => return_result Unsupported end.
Lemma elements_list : forall xs, elements (L xs) = Some xs.
Proof. induction xs; cbn [L fold_right elements]; [reflexivity|rewrite IHxs; reflexivity]. Qed.
Definition form name args body := L [Symbol "defun";name;L args;body].
Definition prefix name (args:list value) := [Arity name (Integer (Z.of_nat (List.length args)))].
Theorem captured_install_success : forall compiler activate name args body target result previous,
 compiler (form (Symbol name) args body) = Returned target ->
 activate target = Returned result ->
 invoke 30 compiler activate "kl:buri.install-observed" [form (Symbol name) args body] previous =
 Out (Returned (Symbol name))
   (Pair (L [form (Symbol name) args body;target]) previous)
   (prefix (Symbol name) args ++
    [Compile (form (Symbol name) args body) (Returned target);
     Activate target (Returned result);ReadRecords;
     WriteRecords (Pair (L [form (Symbol name) args body;target]) previous)]).
Proof.
 intros compiler activate name args body target result previous C A.
 match goal with |- _ = ?rhs => change (eval 30 (lookup observer_program) compiler activate
 (arguments ["V5962"] [form (Symbol name) args body])
 (Native.body (match lookup observer_program "kl:buri.install-observed" with Some d=>d |None=>Def [] (Lit Nil) end)) previous = rhs) end.
 pose proof (elements_list args) as LEN.
 vm_compute in LEN,C,A. vm_compute.
 rewrite LEN.
 rewrite C,A.
 reflexivity.
Qed.
Definition failed r := match r with Returned _ => False | _ => True end.
Theorem captured_compile_failure : forall compiler activate name args body failure previous,
 compiler (form (Symbol name) args body) = failure -> failed failure ->
 invoke 30 compiler activate "kl:buri.install-observed" [form (Symbol name) args body] previous =
 Out failure previous (prefix (Symbol name) args ++ [Compile (form (Symbol name) args body) failure]).
Proof.
 intros compiler activate name args body failure previous C F.
 pose proof (elements_list args) as LEN.
 vm_compute in LEN,C. vm_compute. rewrite LEN,C.
 destruct failure; try contradiction; reflexivity.
Qed.
Theorem captured_activation_failure : forall compiler activate name args body target failure previous,
 compiler (form (Symbol name) args body) = Returned target ->
 activate target = failure -> failed failure ->
 invoke 30 compiler activate "kl:buri.install-observed" [form (Symbol name) args body] previous =
 Out failure previous (prefix (Symbol name) args ++
 [Compile (form (Symbol name) args body) (Returned target);Activate target failure]).
Proof.
 intros compiler activate name args body target failure previous C A F.
 pose proof (elements_list args) as LEN.
 vm_compute in LEN,C,A. vm_compute. rewrite LEN,C,A.
 destruct failure; try contradiction; reflexivity.
Qed.
Theorem published_target_was_activated : forall compiler activate name args body target result previous,
 compiler (form (Symbol name) args body) = Returned target ->
 activate target = Returned result ->
 trace (invoke 30 compiler activate "kl:buri.install-observed" [form (Symbol name) args body] previous) =
 [Arity (Symbol name) (Integer (Z.of_nat (List.length args)));
 Compile (form (Symbol name) args body) (Returned target);Activate target (Returned result);
 ReadRecords;WriteRecords (Pair (L [form (Symbol name) args body;target]) previous)].
Proof. intros compiler activate name args body target result previous C A; rewrite captured_install_success with (target:=target) (result:=result) by assumption; reflexivity. Qed.
End ObserverEffects.
