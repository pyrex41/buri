(* Shen/JIT Phase 2, emit-spec: the continuation relation of the extended emission relation, with
   EVERY frame the emission families need, defined once here. JitLowerKont's KD, TK, KC and RK are
   copied with these changes:
   - the code's capture names cv and capture values caps are indices next to the code, so that a
     closure body's environment (MEnv') reads captured variables from caps;
   - the machine's handler list hs is an index, threaded through every frame, so that each KTrap
     frame of the source meets the handler its trap pushed (KD'_trap), in order;
   - the value relation is a Section variable V, and the heap fact a frame needs about a
     closure is a Section variable HeapClo, so that JitEmitInv instantiates them with VRh mu h and
     the machine's heap (VRh needs the heap, which grows);
   - the comparison of primitives goes through pmapx, every primitive stage 0 calls, without
     JitLowerRel's pguard (a family rule states its own guard);
   - Comp is JitEmitRel's.
   The frames, against what the families need (a family may not add one later: a missing frame
   stops the family and goes back through emit-spec):
     closure-entry return   RK'_call: the caller's code with its own cv and caps, and CCtx (its
                            slot 1 still holds its closure); a closure body returns through it
     handler                KD'_trap: the protected value in slot S, pop-handler, the handler's
                            code at its label (with or without exception), the shared continuation
     global-set, value      KD'_prim with pmapx PSet = B.PSet, pmapx PValue = B.PValue
     vector ops             KD'_prim with pmapx PAbsvector/PAddressGet/PAddressSet/PAbsvectorP
     dynamic-call window    KD'_head_call/_tail (head in window slot a+1), KD'_args_call/_tail
                            (argument i in slot a+2+i), KD'_hbind (apply-all and variable heads:
                            the head in a slot, the rest of a chain of one-argument applications)
     do                     KD'_do1/KD'_do1t (X's value dropped, Y next), KD'_do2/TK'_do2/RK'_do2
                            (the source's pending call of do on X's value is transparent)
   The KApply frame is related nowhere: emitted code never over-applies (erase makes EApp with at
   most one argument and VRh relates no partial application), and the handler's KApply [VExn x]
   lasts only within one simulation step (JitEmitInv.Out' O'_raise).
   Does NOT say: that these frames are enough for the families' simulations (each family's
   sim_X_statement in JitEmitInv is where that is proved), or anything about stability under
   writes, which JitLowerStable proves for the old frames and emit-sim must prove for these. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitProfile JitLowerRel JitLowerKont JitLowerCheck JitEmitRel.
Import ListNotations.
Module JitEmitKont.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics JitLowerRel.JitLowerRel JitLowerKont.JitLowerKont JitEmitRel.JitEmitRel.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.

(* Every primitive stage 0 calls, and what it is in the bytecode. eval-kl is a sealed call of
   shen-jit.eval-kl, not a primitive (lower.shen's norm). *)
Definition pmapx (p : prim) : option B.prim := match p with
 | PIntern => Some B.PIntern | PPos => Some B.PPos | PTlstr => Some B.PTlstr | PCn => Some B.PCn
 | PStr => Some B.PStr | PStringP => Some B.PStringp | PNToString => Some B.PNString
 | PStringToN => Some B.PStringN | PSet => Some B.PSet | PValue => Some B.PValue
 | PSimpleError => Some B.PSimpleError | PErrorToString => Some B.PErrorToString
 | PCons => Some B.PCons | PHd => Some B.PHd | PTl => Some B.PTl | PConsP => Some B.PConsp
 | PEqual => Some B.PEq | PEvalKL => None
 | PAbsvector => Some B.PAbsvector | PAddressSet => Some B.PSetAddress
 | PAddressGet => Some B.PGetAddress | PAbsvectorP => Some B.PAbsvectorp
 | PWriteByte => Some B.PWriteByte | PReadByte => Some B.PReadByte | POpen => Some B.POpen
 | PClose => Some B.PClose | PGetTime => Some B.PGetTime
 | PAdd => Some B.PAdd | PSub => Some B.PSub | PMul => Some B.PMul | PDiv => Some B.PDiv
 | PGt => Some B.PGt | PLt => Some B.PLt | PGe => Some B.PGe | PLe => Some B.PLe
 | PNumberP => Some B.PNumberp end.

Lemma pmapx_pmap : forall p q, pmap p = Some q -> pmapx p = Some q.
Proof. intros p q H; destruct p; cbn in H |- *; congruence. Qed.

(* The kernel's do, which the emitter lowers as value-X-then-Y (erase reads it back as a call). *)
Definition do_name : name := kw "do".

(* A chain of one-argument applications on a head: ((h A1) A2) ... *)
Fixpoint chain (h : expr) (ass : list (list expr)) : expr := match ass with
 | [] => h | as1 :: ass => chain (EApp h as1) ass end.

(* The handler's code after its label: (exception Top) then the handler with E in slot Top when the
   handler reads E, otherwise the handler alone (lower.shen's trap). The handler is quiet exactly
   when its code does not start with an exception instruction (JitBytecode's push-handler). *)
Definition quiet_of (rh : list B.instr) : bool := match rh with B.IException _ :: _ => false | _ => true end.

Section Kont.
Variable V : value -> B.val -> Prop.
(* HeapClo p c caps: the object at heap key p is a closure of code c with captures caps. *)
Variable HeapClo : positive -> B.code -> list B.val -> Prop.

(* The source environment against the frame: g's variables in their slots, and the variables the
   code captures (cv, numbered) in caps, except where g binds the name, as lower.shen's load-var
   looks in Env first. *)
Definition MEnv' (fp : N) (st : B.tree B.val) (cv : list name) (caps : list B.val) (g : env) (rho : lenv) : Prop :=
 (forall x s, lookup x g = Some s -> exists v v', lookup x rho = Some v /\ slotv st (fp + s) = Some v' /\ V v v') /\
 (forall i x, nth_error cv i = Some x -> lookup x g = None ->
   exists v v', lookup x rho = Some v /\ nth_error caps i = Some v' /\ V v v').

(* The code's closure is in slot 1, when the code captures anything. *)
Definition CCtx (c : B.code) (cv : list name) (caps : list B.val) (fp : N) (st : B.tree B.val) : Prop :=
 cv = [] \/ exists p, slotv st (fp + 1) = Some (B.VClo p) /\ HeapClo p c caps.

Inductive DoneR' (c : B.code) (fp : N) (st : B.tree B.val) : list value -> list B.operand -> Prop :=
 | DR'_nil : DoneR' c fp st [] []
 | DR'_cons v v' o vs os : read_o c fp st o = Some v' -> V v v' -> DoneR' c fp st vs os ->
     DoneR' c fp st (v :: vs) (o :: os).
Inductive ArgsAt' (st : B.tree B.val) : N -> list value -> Prop :=
 | AA'_nil a : ArgsAt' st a []
 | AA'_cons a v v' vs : slotv st a = Some v' -> V v v' -> ArgsAt' st (a + 1) vs -> ArgsAt' st a (v :: vs).
Inductive ParamAt' (fp : N) (st : B.tree B.val) (ms : list (N * N)) : N -> list value -> Prop :=
 | PA'_nil i : ParamAt' fp st ms i []
 | PA'_cons i v v' vs : slotv st (fp + loc ms i) = Some v' -> V v v' ->
     ParamAt' fp st ms (i + 1) vs -> ParamAt' fp st ms i (v :: vs).

(* Indices: code, capture names, capture values, frame pointer, stack, saved continuations,
   handlers, writable addresses, then as in JitLowerKont. *)
Inductive KD' : B.code -> list name -> list B.val -> N -> B.tree B.val -> list B.cont -> list B.handler ->
    (N -> Prop) -> B.operand -> list B.instr -> list frame -> Prop :=
 | KD'_ret c cv caps fp st cs hs w o r k : Sub w (fun a => fp <= a) -> RK' fp st cs hs k ->
     KD' c cv caps fp st cs hs w o (B.IReturn o :: r) k
 | KD'_jump c cv caps fp st cs hs w o e r r1 k : lbl c e = Some r1 -> KD' c cv caps fp st cs hs w o r1 k ->
     KD' c cv caps fp st cs hs w o (B.IJump e :: r) k
 | KD'_label c cv caps fp st cs hs w o l r k : KD' c cv caps fp st cs hs w o r k ->
     KD' c cv caps fp st cs hs w o (B.ILabel l :: r) k
 | KD'_let c cv caps fp st cs hs w d r x b rho k1 g top dst r2 w1 :
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top -> d < top ->
     Comp c cv ((x, d) :: g) top b dst r r2 -> Sub w w1 -> Above fp top w1 ->
     KC' c cv caps fp st cs hs w1 dst r2 k1 ->
     KD' c cv caps fp st cs hs w (B.OSlot d) r (KLet x b rho :: k1)
 | KD'_lett c cv caps fp st cs hs w d r x b rho k1 g top l r2 w1 :
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top -> d < top ->
     CompT c cv ((x, d) :: g) top b l r r2 -> Sub w w1 -> Above fp top w1 ->
     TK' c cv caps fp st cs hs w1 true l r2 k1 ->
     KD' c cv caps fp st cs hs w (B.OSlot d) r (KLet x b rho :: k1)
 | KD'_test c cv caps fp st cs hs w o l r k : TK' c cv caps fp st cs hs w true l r k ->
     KD' c cv caps fp st cs hs w o (B.IJumpIfFalse o l :: r) k
 (* A primitive's argument (JitLowerKont's KD_prim over pmapx, without pguard): global-set and
    value, the vector operations, and every other primitive. *)
 | KD'_prim c cv caps fp st cs hs w o r f p q vals es rho k1 g top ops dops d r1 w1 :
     prim_of_name f = Some p -> pmapx p = Some q ->
     (List.length vals + 1 + List.length es)%nat = prim_arity p ->
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top ->
     CompOps c cv g top es ops r (B.IPrim d q (rev dops ++ o :: ops) :: r1) ->
     DoneR' c fp st vals dops -> Forall (o_safe fp w) dops ->
     Forall (o_below top) dops -> o_below top o ->
     Sub w w1 -> Above fp top w1 -> w1 (fp + d) -> KD' c cv caps fp st cs hs w1 (B.OSlot d) r1 k1 ->
     KD' c cv caps fp st cs hs w o r (KCallArgs f vals es rho :: k1)
 | KD'_call c cv caps fp st cs hs w r f vals es rho k1 g a s d n i r1 w1 :
     not_prim_name f -> s = a + 2 + N.of_nat (List.length vals) ->
     n = N.of_nat (List.length vals + 1 + List.length es) ->
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g (s + 1) ->
     CompW c cv g (s + 1) es r (i :: r1) -> call_instr i d a (B.sym_of_text f) n ->
     ArgsAt' st (fp + a + 2) (rev vals) -> Sub w (fun x => fp + s <= x) ->
     Sub w w1 -> Above fp a w1 -> w1 (fp + d) -> KD' c cv caps fp st cs hs w1 (B.OSlot d) r1 k1 ->
     KD' c cv caps fp st cs hs w (B.OSlot s) r (KCallArgs f vals es rho :: k1)
 | KD'_tail c cv caps fp st cs hs w o r f vals es rho k1 g s t t0 ms n i r1 :
     not_prim_name f -> s = 2 + N.of_nat (List.length vals) ->
     n = N.of_nat (List.length vals + 1 + List.length es) -> n + 2 <= t0 -> t0 <= t ->
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g t ->
     CompTA c cv g (s + 1) t es ms r (i :: r1) -> tail_instr i 0 (B.sym_of_text f) n ->
     o = B.OSlot (loc ms s) -> loc ms s < t ->
     Forall (fun m => 2 <= fst m < s + 1 /\ n + 2 <= snd m < t) ms -> NoDup (map fst ms) ->
     (forall j, 2 <= j < s -> loc ms j = j \/ n + 2 <= loc ms j < t0) ->
     ParamAt' fp st ms 2 (rev vals) ->
     Sub w (fun x => x = fp + s \/ fp + t0 <= x) -> RK' fp st cs hs k1 ->
     KD' c cv caps fp st cs hs w o r (KCallArgs f vals es rho :: k1)
 (* handler: the protected expression's value is in slot s; pop-handler, then r1 (a jump to the
    end, or a return). The top handler is the one the trap pushed: this code, its label lH, this
    frame, these continuations. At lH, the handler body with E in slot top (after exception top)
    or, when the body does not read E, without it; its continuation is k1's, as r1's is. *)
 | KD'_trap c cv caps fp st cs hs w s r1 x hb rho k1 g top lH rh dst r2 w1 :
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top -> lbl c lH = Some rh ->
     ((exists rh', rh = B.IException top :: rh' /\ Comp c cv ((x, top) :: g) (top + 1) hb dst rh' r2) \/
      (quiet_of rh = true /\ Comp c cv g (top + 1) hb dst rh r2)) ->
     Sub w w1 -> Above fp top w1 -> KC' c cv caps fp st cs hs w1 dst r2 k1 ->
     KD' c cv caps fp st cs hs w1 (B.OSlot s) r1 k1 ->
     KD' c cv caps fp st cs (B.Handler c lH fp cs (quiet_of rh) :: hs) w (B.OSlot s) (B.IPopHandler :: r1)
       (KTrap (ELam x hb) rho :: k1)
 (* dynamic-call window, head: the head's value in slot a+1, then the arguments from a+2, then
    call-value (its result to d) or tail-call-value. *)
 | KD'_head_call c cv caps fp st cs hs w r args rho k1 g a s d n r1 w1 :
     s = a + 1 -> n = N.of_nat (List.length args) ->
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g (s + 1) ->
     CompW c cv g (s + 1) args r (B.ICallValue d a n :: r1) -> Sub w (fun x => fp + s <= x) ->
     Sub w w1 -> Above fp a w1 -> w1 (fp + d) -> KD' c cv caps fp st cs hs w1 (B.OSlot d) r1 k1 ->
     KD' c cv caps fp st cs hs w (B.OSlot s) r (KHead args rho :: k1)
 | KD'_head_tail c cv caps fp st cs hs w r args rho k1 g a s n r1 :
     s = a + 1 -> n = N.of_nat (List.length args) ->
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g (s + 1) ->
     CompW c cv g (s + 1) args r (B.ITailValue a n :: r1) -> Sub w (fun x => fp + s <= x) ->
     Sub w (fun x => fp <= x) -> RK' fp st cs hs k1 ->
     KD' c cv caps fp st cs hs w (B.OSlot s) r (KHead args rho :: k1)
 (* dynamic-call window, an argument: the head's value in a+1, the earlier ones from a+2, this
    one in s, the rest after it. *)
 | KD'_args_call c cv caps fp st cs hs w r fv fv' done rest rho k1 g a s d n r1 w1 :
     s = a + 2 + N.of_nat (List.length done) -> n = N.of_nat (List.length done + 1 + List.length rest) ->
     slotv st (fp + a + 1) = Some fv' -> V fv fv' -> ArgsAt' st (fp + a + 2) (rev done) ->
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g (s + 1) ->
     CompW c cv g (s + 1) rest r (B.ICallValue d a n :: r1) -> Sub w (fun x => fp + s <= x) ->
     Sub w w1 -> Above fp a w1 -> w1 (fp + d) -> KD' c cv caps fp st cs hs w1 (B.OSlot d) r1 k1 ->
     KD' c cv caps fp st cs hs w (B.OSlot s) r (KArgs fv done rest rho :: k1)
 | KD'_args_tail c cv caps fp st cs hs w r fv fv' done rest rho k1 g a s n r1 :
     s = a + 2 + N.of_nat (List.length done) -> n = N.of_nat (List.length done + 1 + List.length rest) ->
     slotv st (fp + a + 1) = Some fv' -> V fv fv' -> ArgsAt' st (fp + a + 2) (rev done) ->
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g (s + 1) ->
     CompW c cv g (s + 1) rest r (B.ITailValue a n :: r1) -> Sub w (fun x => fp + s <= x) ->
     Sub w (fun x => fp <= x) -> RK' fp st cs hs k1 ->
     KD' c cv caps fp st cs hs w (B.OSlot s) r (KArgs fv done rest rho :: k1)
 (* a head held in slot s (apply-all's head-slot, or a variable head): the code that follows is
    the chain of one-argument applications with the head as a fresh variable x in s. *)
 | KD'_hbind c cv caps fp st cs hs w s r x ass rho k1 g top dst r2 w1 :
     ~ In x (flat_map JitLowerCheck.JitLowerCheck.vars (List.concat ass)) -> ass <> [] ->
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top -> s < top ->
     Comp c cv ((x, s) :: g) top (chain (EVar x) ass) dst r r2 ->
     Sub w w1 -> Above fp top w1 -> KC' c cv caps fp st cs hs w1 dst r2 k1 ->
     KD' c cv caps fp st cs hs w (B.OSlot s) r (map (fun as1 => KHead as1 rho) ass ++ k1)
 (* do: X's value, dropped; Y next, as a value or as a test. *)
 | KD'_do1 c cv caps fp st cs hs w o r y rho k1 g top dst r2 w1 :
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top ->
     Comp c cv g top y dst r r2 -> Sub w w1 -> Above fp top w1 -> KC' c cv caps fp st cs hs w1 dst r2 k1 ->
     KD' c cv caps fp st cs hs w o r (KCallArgs do_name [] [y] rho :: k1)
 | KD'_do1t c cv caps fp st cs hs w o r y rho k1 g top l r2 w1 :
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top ->
     CompT c cv g top y l r r2 -> Sub w w1 -> Above fp top w1 -> TK' c cv caps fp st cs hs w1 true l r2 k1 ->
     KD' c cv caps fp st cs hs w o r (KCallArgs do_name [] [y] rho :: k1)
 (* do: Y's value goes where (do X Y)'s goes; the source's call of do on X's value is transparent. *)
 | KD'_do2 c cv caps fp st cs hs w o r v rho k1 : KD' c cv caps fp st cs hs w o r k1 ->
     KD' c cv caps fp st cs hs w o r (KCallArgs do_name [v] [] rho :: k1)

with TK' : B.code -> list name -> list B.val -> N -> B.tree B.val -> list B.cont -> list B.handler ->
    (N -> Prop) -> bool -> N -> list B.instr -> list frame -> Prop :=
 | TK'_if c cv caps fp st cs hs w l r a b rho k1 g top dst r2 r3 r4 w1 :
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top ->
     Comp c cv g top a dst r r2 -> lbl c l = Some r3 -> Comp c cv g top b dst r3 r4 ->
     Sub w w1 -> Above fp top w1 -> KC' c cv caps fp st cs hs w1 dst r2 k1 -> KC' c cv caps fp st cs hs w1 dst r4 k1 ->
     TK' c cv caps fp st cs hs w true l r (KIf a b rho :: k1)
 | TK'_cond c cv caps fp st cs hs w l r a rest rho k1 g top dst r2 r3 r4 w1 :
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top ->
     Comp c cv g top a dst r r2 -> lbl c l = Some r3 -> Comp c cv g top (ECond rest) dst r3 r4 ->
     Sub w w1 -> Above fp top w1 -> KC' c cv caps fp st cs hs w1 dst r2 k1 -> KC' c cv caps fp st cs hs w1 dst r4 k1 ->
     TK' c cv caps fp st cs hs w true l r (KCond a rest rho :: k1)
 | TK'_and c cv caps fp st cs hs w gd l r y rho k1 g top r2 w1 :
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top ->
     CompT c cv g top y l r r2 -> Sub w w1 -> Above fp top w1 ->
     TK' c cv caps fp st cs hs w1 gd l r2 k1 ->
     TK' c cv caps fp st cs hs w true l r (KAnd y rho :: k1)
 | TK'_andr c cv caps fp st cs hs w gd l r k1 w1 : Sub w w1 -> TK' c cv caps fp st cs hs w1 gd l r k1 ->
     TK' c cv caps fp st cs hs w true l r (KAndR :: k1)
 | TK'_or c cv caps fp st cs hs w gd l nx r1 y rho k1 g top r2 r3 w1 :
     MEnv' fp st cv caps g rho -> Prot g fp w -> EnvBelow g top ->
     lbl c nx = Some r2 -> CompT c cv g top y l r2 r3 -> Sub w w1 -> Above fp top w1 ->
     TK' c cv caps fp st cs hs w1 gd l r3 k1 -> TK' c cv caps fp st cs hs w1 gd l r1 k1 ->
     TK' c cv caps fp st cs hs w true nx r1 (KOr y rho :: k1)
 | TK'_orr c cv caps fp st cs hs w gd l r k1 w1 : Sub w w1 -> TK' c cv caps fp st cs hs w1 gd l r k1 ->
     TK' c cv caps fp st cs hs w true l r (KOrR :: k1)
 | TK'_jump c cv caps fp st cs hs w gd l e r r1 k : lbl c e = Some r1 -> TK' c cv caps fp st cs hs w gd l r1 k ->
     TK' c cv caps fp st cs hs w gd l (B.IJump e :: r) k
 | TK'_label c cv caps fp st cs hs w gd l x r k : TK' c cv caps fp st cs hs w gd l r k ->
     TK' c cv caps fp st cs hs w gd l (B.ILabel x :: r) k
 | TK'_value c cv caps fp st cs hs w l d kt kf r2 r4 k w1 :
     konst c kt = Some (B.VBool true) -> konst c kf = Some (B.VBool false) ->
     lbl c l = Some (B.IConst d kf :: r4) -> Sub w w1 -> w1 (fp + d) ->
     KD' c cv caps fp st cs hs w1 (B.OSlot d) r2 k -> KD' c cv caps fp st cs hs w1 (B.OSlot d) r4 k ->
     TK' c cv caps fp st cs hs w false l (B.IConst d kt :: r2) k
 | TK'_do2 c cv caps fp st cs hs w gd l r v rho k1 : TK' c cv caps fp st cs hs w gd l r k1 ->
     TK' c cv caps fp st cs hs w gd l r (KCallArgs do_name [v] [] rho :: k1)

with KC' : B.code -> list name -> list B.val -> N -> B.tree B.val -> list B.cont -> list B.handler ->
    (N -> Prop) -> dest -> list B.instr -> list frame -> Prop :=
 | KC'_ret c cv caps fp st cs hs w r k : Sub w (fun a => fp <= a) -> RK' fp st cs hs k ->
     KC' c cv caps fp st cs hs w DRet r k
 | KC'_slot c cv caps fp st cs hs w d r k : w (fp + d) -> KD' c cv caps fp st cs hs w (B.OSlot d) r k ->
     KC' c cv caps fp st cs hs w (DSlot d) r k

(* The function's own continuation: the caller's code, through a saved frame. The caller may be a
   closure body (closure-entry return): its capture names and values are its own, and its closure
   is still in its slot 1. Handlers are global: those below the callee's are the caller's. *)
with RK' : N -> B.tree B.val -> list B.cont -> list B.handler -> list frame -> Prop :=
 | RK'_top fp st : RK' fp st [] [] []
 | RK'_call fp st c cv caps r d a cs hs k w : a <= fp -> Above (fp - a) a w ->
     CCtx c cv caps (fp - a) st -> ~ w (fp - a + 1) ->
     KD' c cv caps (fp - a) st cs hs w (B.OSlot d) r k -> w (fp - a + d) ->
     RK' fp st (B.Cont c r d a :: cs) hs k
 | RK'_do2 fp st cs hs v rho k1 : RK' fp st cs hs k1 -> RK' fp st cs hs (KCallArgs do_name [v] [] rho :: k1).

Scheme KD'_m := Induction for KD' Sort Prop
 with TK'_m := Induction for TK' Sort Prop
 with KC'_m := Induction for KC' Sort Prop
 with RK'_m := Induction for RK' Sort Prop.
Combined Scheme K'_mut from KD'_m, TK'_m, KC'_m, RK'_m.
End Kont.

(* A KTrap frame is always matched by a handler: whatever the position, a continuation whose
   innermost frame is a KTrap has at least one handler installed (the one KD'_trap consumes, in
   this frame or a caller's). *)
Theorem trap_has_handler : forall V HC,
 (forall c cv caps fp st cs hs w o r k, KD' V HC c cv caps fp st cs hs w o r k ->
   forall h rho k1, k = KTrap h rho :: k1 -> hs <> []) /\
 (forall c cv caps fp st cs hs w gd l r k, TK' V HC c cv caps fp st cs hs w gd l r k ->
   forall h rho k1, k = KTrap h rho :: k1 -> hs <> []) /\
 (forall c cv caps fp st cs hs w dst r k, KC' V HC c cv caps fp st cs hs w dst r k ->
   forall h rho k1, k = KTrap h rho :: k1 -> hs <> []) /\
 (forall fp st cs hs k, RK' V HC fp st cs hs k -> forall h rho k1, k = KTrap h rho :: k1 -> hs <> []).
Proof.
 intros V HC. apply K'_mut; intros; subst; try discriminate; eauto.
 destruct ass; [contradiction|discriminate].
Qed.
End JitEmitKont.
