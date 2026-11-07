(*
  Spike 10: a first rung of the CakeML route. A tiny KLambda fragment
  (integer and boolean literals, variables, if, let, +), a big-step semantics
  for it in HOL4, a code generator to CakeML source over one tagged value type,
  and a theorem that CakeML's own functional big-step semantics (evaluate)
  runs the generated code to a related value or raises the related exception.

  NOT Búri's KLSemantics: this is a fresh HOL4 definition of the same rules for
  this fragment. Relating it to rocq/KLSemantics.v is a trusted statement match.
  No calls, closures, tail calls, primitives beyond +, or store.
*)
Theory klfrag
Ancestors
  ast semanticPrimitives evaluate namespace namespaceProps
Libs
  preamble

(* ---------- source ---------- *)
Datatype:
  kexp = KNum int | KBool bool | KVar mlstring
       | KIf kexp kexp kexp | KLet mlstring kexp kexp | KAdd kexp kexp
End

Datatype:
  kval = KI int | KB bool
End

(* KErr: a KLambda error (message elided). KStuck: an unbound variable, which
   KLambda's parser would have read as a symbol; excluded by the theorem. *)
Datatype:
  kres = KOk kval | KErr | KStuck
End

(* Left to right, as KLambda requires. *)
Definition keval_def:
  keval env (KNum i) = KOk (KI i) ∧
  keval env (KBool b) = KOk (KB b) ∧
  keval env (KVar x) = (case ALOOKUP env x of SOME v => KOk v | NONE => KStuck) ∧
  keval env (KIf c a b) =
    (case keval env c of
     | KOk (KB T) => keval env a
     | KOk (KB F) => keval env b
     | KOk _ => KErr
     | r => r) ∧
  keval env (KLet x a b) =
    (case keval env a of
     | KOk v => keval ((x,v)::env) b
     | r => r) ∧
  keval env (KAdd a b) =
    (case keval env a of
     | KOk va =>
       (case keval env b of
        | KOk vb => (case (va, vb) of (KI i, KI j) => KOk (KI (i + j)) | _ => KErr)
        | r => r)
     | r => r)
End

(* ---------- code generator ---------- *)
Definition kerr_def:
  kerr = Raise (Con (SOME (Short «KlErr»)) [])
End

Definition pKI_def:
  pKI p = Pcon (SOME (Short «KI»)) [p]
End

Definition pKB_def:
  pKB b = Pcon (SOME (Short «KB»)) [Pcon (SOME (Short (if b then «True» else «False»))) []]
End

(* KAdd binds its operands in order with Let, so CakeML's right-to-left
   argument order is never observable. The names _a _b _i _j are reserved. *)
Definition cg_def:
  cg (KNum i) = Con (SOME (Short «KI»)) [Lit (IntLit i)] ∧
  cg (KBool b) = Con (SOME (Short «KB»)) [Con (SOME (Short (if b then «True» else «False»))) []] ∧
  cg (KVar x) = Var (Short x) ∧
  cg (KIf c a b) = Mat (cg c) [(pKB T, cg a); (pKB F, cg b); (Pany, kerr)] ∧
  cg (KLet x a b) = Let (SOME x) (cg a) (cg b) ∧
  cg (KAdd a b) =
    Let (SOME «_a») (cg a) (Let (SOME «_b») (cg b)
      (Mat (Var (Short «_a»))
        [(pKI (Pvar «_i»),
          Mat (Var (Short «_b»))
            [(pKI (Pvar «_j»),
              Con (SOME (Short «KI»)) [App (Arith Add IntT) [Var (Short «_i»); Var (Short «_j»)]]);
             (Pany, kerr)]);
         (Pany, kerr)]))
End

Definition reserved_def:
  reserved x ⇔ MEM x [«_a»; «_b»; «_i»; «_j»]
End

Definition vars_ok_def:
  vars_ok (KVar x) = ¬reserved x ∧
  vars_ok (KIf c a b) = (vars_ok c ∧ vars_ok a ∧ vars_ok b) ∧
  vars_ok (KLet x a b) = (¬reserved x ∧ vars_ok a ∧ vars_ok b) ∧
  vars_ok (KAdd a b) = (vars_ok a ∧ vars_ok b) ∧
  vars_ok _ = T
End

(* ---------- relations ---------- *)
(* The tagged value type, as a datatype the program declares:
   datatype kv = KI of int | KB of bool;  exception KlErr *)
Definition env_ok_def:
  env_ok (env : v sem_env) kt ke ⇔
    nsLookup env.c (Short «KI») = SOME (1, TypeStamp «KI» kt) ∧
    nsLookup env.c (Short «KB») = SOME (1, TypeStamp «KB» kt) ∧
    nsLookup env.c (Short «True») = SOME (0, TypeStamp «True» bool_type_num) ∧
    nsLookup env.c (Short «False») = SOME (0, TypeStamp «False» bool_type_num) ∧
    nsLookup env.c (Short «KlErr») = SOME (0, ExnStamp ke)
End

Definition v_rel_def:
  v_rel kt (KI i) v = (v = Conv (SOME (TypeStamp «KI» kt)) [Litv (IntLit i)]) ∧
  v_rel kt (KB b) v = (v = Conv (SOME (TypeStamp «KB» kt)) [Boolv b])
End

Definition env_rel_def:
  env_rel kt kenv (env : v sem_env) ⇔
    ∀x v. ALOOKUP kenv x = SOME v ∧ ¬reserved x ⇒
          ∃v'. nsLookup env.v (Short x) = SOME v' ∧ v_rel kt v v'
End

Definition res_rel_def:
  res_rel kt ke (KOk v) r = (∃v'. r = Rval [v'] ∧ v_rel kt v v') ∧
  res_rel kt ke KErr r = (r = Rerr (Rraise (Conv (SOME (ExnStamp ke)) []))) ∧
  res_rel kt ke KStuck r = F
End

(* ---------- the theorem ---------- *)
Theorem env_v_empty[simp,local]:
  ((env : v sem_env) with v := nsAppend (Bind [] []) env.v) = env
Proof
  rw [sem_env_component_equality] \\ Cases_on `env.v` \\ rw [nsAppend_def]
QED

Theorem fix_clock_same[simp,local]:
  fix_clock st (st, r) = (st, r)
Proof
  rw[fix_clock_def, state_component_equality]
QED

(* Every value a KLambda subterm can produce matches the case patterns
   without a type error, and the generated case analysis picks the right arm. *)
val pm_ss = [pKB_def, pKI_def, pmatch_def, env_ok_def, same_type_def, same_ctor_def,
             Boolv_def, can_pmatch_all_def, evaluate_def, kerr_def, do_con_check_def,
             build_conv_def, v_rel_def, res_rel_def, pat_bindings_def, nsOptBind_def,
             do_app_def, do_arith_def, check_type_def, the_Litv_IntLit_def,
             getOpClass_def, nsAppend_def, alist_to_ns_def, nsLookup_def, nsBind_def];

Theorem cg_correct:
  ∀e kenv env (st : 'ffi state) kt ke.
    keval kenv e ≠ KStuck ∧ vars_ok e ∧ env_ok env kt ke ∧ env_rel kt kenv env ⇒
    ∃r. evaluate st env [cg e] = (st, r) ∧ res_rel kt ke (keval kenv e) r
Proof
  Induct_on `e` \\ rpt gen_tac \\ strip_tac
  (* KNum *)
  >- gvs ([keval_def, cg_def] @ pm_ss)
  (* KBool *)
  >- (Cases_on `b` \\ gvs ([keval_def, cg_def] @ pm_ss))
  (* KVar *)
  >- (gvs [keval_def, vars_ok_def, AllCaseEqs()] \\ Cases_on `ALOOKUP kenv m`
      \\ gvs [env_rel_def] \\ first_x_assum drule_all \\ rw [] \\ simp ([cg_def] @ pm_ss))
  (* KIf *)
  >- (gvs [vars_ok_def, keval_def]
      \\ qpat_x_assum `∀kenv env st kt ke. keval kenv e ≠ KStuck ∧ _ ⇒ _`
           (qspecl_then [`kenv`, `env`, `st`, `kt`, `ke`] mp_tac)
      \\ Cases_on `keval kenv e` \\ gvs []
      >- (rw [] \\ simp [cg_def, Once evaluate_def] \\ Cases_on `k` \\ gvs pm_ss
          \\ Cases_on `b` \\ gvs pm_ss \\ first_x_assum irule \\ gvs [env_ok_def])
      \\ rw [] \\ simp [cg_def, Once evaluate_def] \\ gvs [res_rel_def])
  (* KLet *)
  >- (gvs [vars_ok_def, keval_def]
      \\ qpat_x_assum `∀kenv env st kt ke. keval kenv e ≠ KStuck ∧ _ ⇒ _`
           (qspecl_then [`kenv`, `env`, `st`, `kt`, `ke`] mp_tac)
      \\ Cases_on `keval kenv e` \\ gvs []
      >- (rw [] \\ simp [cg_def, Once evaluate_def, nsOptBind_def] \\ gvs [res_rel_def]
          \\ first_x_assum irule \\ gvs [env_ok_def, env_rel_def] \\ rw [] \\ gvs [])
      \\ rw [] \\ simp [cg_def, Once evaluate_def] \\ gvs [res_rel_def])
  (* KAdd *)
  \\ gvs [vars_ok_def, keval_def]
  \\ qpat_x_assum `∀kenv env st kt ke. keval kenv e ≠ KStuck ∧ _ ⇒ _`
       (qspecl_then [`kenv`, `env`, `st`, `kt`, `ke`] mp_tac)
  \\ Cases_on `keval kenv e` \\ gvs []
  >- (strip_tac \\ simp [cg_def, Once evaluate_def] \\ gvs [res_rel_def, nsOptBind_def]
      \\ first_x_assum (qspecl_then [`kenv`, `env with v := nsBind «_a» v' env.v`, `st`, `kt`, `ke`] mp_tac)
      \\ impl_tac
      >- (Cases_on `keval kenv e'` \\ gvs [AllCaseEqs(), env_ok_def, env_rel_def]
          \\ rpt strip_tac \\ gvs [reserved_def] \\ res_tac \\ simp [nsLookup_nsBind])
      \\ Cases_on `keval kenv e'` \\ gvs []
      >- (strip_tac \\ simp [Once evaluate_def, nsOptBind_def] \\ gvs [res_rel_def]
          \\ Cases_on `k` \\ Cases_on `k'` \\ Cases_on `env.v` \\ gvs pm_ss
          \\ gvs [env_ok_def, state_component_equality])
      \\ strip_tac \\ simp [Once evaluate_def, nsOptBind_def] \\ gvs [res_rel_def])
  \\ rw [] \\ simp [cg_def, Once evaluate_def] \\ gvs [res_rel_def]
QED
