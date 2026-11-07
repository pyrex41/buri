(* Shen/JIT Phase 2: a checker that decides, for one code object and one KLambda definition, that
   the code is related to the definition by JitLowerRel.Comp. It follows the dispatch of
   src/lowerer/lower.shen's emission, so it accepts the code the lowerer makes for the constructs
   the relation admits, and rejects the rest; rejection says nothing either way.
   `check_fn_sound` makes acceptance a proof of CompFn, so JitLowerThm applies to accepted code. *)
From Coq Require Import List ZArith NArith PArith Bool String Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitFloat JitBytecode JitLowerRel.
Import ListNotations.
Module JitLowerCheck.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics JitLowerRel.JitLowerRel.
Module B := JitBytecode.JitBytecode.
Local Open Scope N_scope.

(* ---------- decisions ---------- *)
Fixpoint vrb (v : value) (w : B.val) : bool := match v, w with
 | VNum (NInt z), B.VFix y => Z.eqb z y
 | VNum (NFloat b), B.VReal c => N.eqb b c
 | VSym s, B.VSym p => Pos.eqb (B.sym_of_text s) p
 | VBool b, B.VBool c => Bool.eqb b c
 | VStr t, B.VStr u => text_eqb t u && Nat.eqb (List.length t) (List.length u)
 | VNil, B.VNil => true
 | VCons a d, B.VPair a' d' => vrb a a' && vrb d d'
 | _, _ => false end.
Lemma text_eqb_eq' : forall t u, text_eqb t u = true -> List.length t = List.length u -> t = u.
Proof.
 induction t as [|x t IH]; destruct u as [|y u]; cbn; intros H L; try discriminate; auto.
 apply andb_true_iff in H as [H1 H2]. apply N.eqb_eq in H1. subst. f_equal. apply IH; auto.
Qed.
Lemma vrb_sound : forall v w, vrb v w = true -> VR v w.
Proof.
 induction v; destruct w; intro H; cbn in H; try discriminate;
 try (destruct n; try discriminate;
      first [apply Z.eqb_eq in H; subst; constructor|apply N.eqb_eq in H; subst; constructor]).
 - apply Pos.eqb_eq in H; subst; constructor.
 - apply Bool.eqb_prop in H; subst; constructor.
 - apply andb_true_iff in H as [H1 H2]. apply Nat.eqb_eq in H2. rewrite (text_eqb_eq' _ _ H1 H2). constructor.
 - constructor.
 - apply andb_true_iff in H as [H1 H2]. constructor; auto.
Qed.

Fixpoint find_k (cs : list B.val) (v : value) (i : nat) : option N := match cs with
 | [] => None
 | w :: cs => if vrb v w then Some (N.of_nat i) else find_k cs v (S i) end.
Lemma find_k_sound : forall cs v i k, find_k cs v i = Some k ->
 exists w, nth_error cs (N.to_nat k - i) = Some w /\ VR v w /\ (i <= N.to_nat k)%nat.
Proof.
 induction cs as [|w cs IH]; intros v i k H; cbn in H; [discriminate|].
 destruct (vrb v w) eqn:E.
 - inversion H; subst. exists w. rewrite Nat2N.id, Nat.sub_diag. split; [reflexivity|split; [apply vrb_sound; auto|lia]].
 - destruct (IH v (S i) k H) as (w' & A & Bv & L). exists w'. split; [|split; auto; lia].
   replace (N.to_nat k - i)%nat with (S (N.to_nat k - S i)) by lia. exact A.
Qed.

Definition o_eqb (a b : B.operand) : bool := match a, b with
 | B.OSlot x, B.OSlot y => N.eqb x y | B.OConst x, B.OConst y => N.eqb x y | _, _ => false end.
Lemma o_eqb_eq : forall a b, o_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; intro H; try discriminate; apply N.eqb_eq in H; subst; auto. Qed.
Fixpoint os_eqb (a b : list B.operand) : bool := match a, b with
 | [], [] => true | x :: a, y :: b => o_eqb x y && os_eqb a b | _, _ => false end.
Lemma os_eqb_eq : forall a b, os_eqb a b = true -> a = b.
Proof.
 induction a; destruct b; cbn; intro H; try discriminate; auto.
 apply andb_true_iff in H as [H1 H2]. f_equal; [apply o_eqb_eq|apply IHa]; auto.
Qed.
Definition q_eqb (a b : B.prim) : bool := match a, b with
 | B.PAdd, B.PAdd | B.PSub, B.PSub | B.PMul, B.PMul | B.PGt, B.PGt | B.PLt, B.PLt | B.PGe, B.PGe
 | B.PLe, B.PLe | B.PCons, B.PCons | B.PHd, B.PHd | B.PTl, B.PTl | B.PConsp, B.PConsp
 | B.PNumberp, B.PNumberp | B.PStringp, B.PStringp | B.PRaiseCond, B.PRaiseCond => true
 | _, _ => false end.
Lemma q_eqb_eq : forall a b, q_eqb a b = true -> a = b.
Proof. destruct a, b; cbn; intro H; try discriminate; reflexivity. Qed.
Definition is_bool (w : option B.val) (b : bool) : bool := match w with
 | Some (B.VBool c) => Bool.eqb b c | _ => false end.
Lemma is_bool_eq : forall w b, is_bool w b = true -> w = Some (B.VBool b).
Proof. intros w b H. destruct w as [[]|]; cbn in H; try discriminate. apply Bool.eqb_prop in H; subst; reflexivity. Qed.

Fixpoint vars (e : expr) : list name := match e with
 | EVar x => [x]
 | ELet _ a b | EAnd a b | EOr a b | ETrap a b => vars a ++ vars b
 | EIf c a b => vars c ++ vars a ++ vars b
 | ECond cl => (fix go (l : list (expr * expr)) := match l with
     | [] => [] | (c, b) :: l => vars c ++ vars b ++ go l end) cl
 | EType a | ELam _ a | EFreeze a | EDefun _ _ a => vars a
 | EApp h args => vars h ++ (fix go (l : list expr) := match l with [] => [] | a :: l => vars a ++ go l end) args
 | ECall _ args => (fix go (l : list expr) := match l with [] => [] | a :: l => vars a ++ go l end) args
 | _ => [] end.
Definition reads (g : env) (es : list expr) (s : N) : bool :=
 existsb (fun x => slot_is (lookup x g) s) (flat_map vars es).

Definition is_tailcall (i : B.instr) (f : positive) (n : N) : bool := match i with
 | B.ITail a f' n' | B.ITailSealed a f' n' => N.eqb a 0 && Pos.eqb f f' && N.eqb n n' | _ => false end.
Definition is_call (i : B.instr) (d a : N) (f : positive) (n : N) : bool := match i with
 | B.ICall d' a' f' n' | B.ICallSealed d' a' f' n' => N.eqb d d' && N.eqb a a' && Pos.eqb f f' && N.eqb n n'
 | _ => false end.
Lemma is_tailcall_ok : forall i f n, is_tailcall i f n = true -> tail_instr i 0 f n.
Proof.
 intros i f n H. destruct i; cbn in H; try discriminate;
 repeat (apply andb_true_iff in H as [H ?]);
 repeat match goal with Hx : N.eqb _ _ = true |- _ => apply N.eqb_eq in Hx | Hx : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in Hx end;
 subst; [left|right]; reflexivity.
Qed.
Lemma is_call_ok : forall i d a f n, is_call i d a f n = true -> call_instr i d a f n.
Proof.
 intros i d a f n H. destruct i; cbn in H; try discriminate;
 repeat (apply andb_true_iff in H as [H ?]);
 repeat match goal with Hx : N.eqb _ _ = true |- _ => apply N.eqb_eq in Hx | Hx : Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in Hx end;
 subst; [left|right]; reflexivity.
Qed.

Fixpoint moves_prefix (ms : list (N * N)) (r : list B.instr) : option (list B.instr) := match ms, r with
 | [], r => Some r
 | (s, t) :: ms, B.IMove d u :: r => if N.eqb s d && N.eqb t u then moves_prefix ms r else None
 | _, _ => None end.
Lemma moves_prefix_ok : forall ms r r', moves_prefix ms r = Some r' ->
 r = map (fun m => B.IMove (fst m) (snd m)) ms ++ r'.
Proof.
 induction ms as [|[s t] ms IH]; intros r r' H; cbn in H; [inversion H; auto|].
 destruct r as [|[] r]; try discriminate.
 destruct (N.eqb s d && N.eqb t s0) eqn:E; [|discriminate].
 apply andb_true_iff in E as [E1 E2]. apply N.eqb_eq in E1; apply N.eqb_eq in E2; subst.
 cbn. f_equal. apply IH; auto.
Qed.

Section Check.
Variable c : B.code.

Definition lbl_ok (l : N) (r : list B.instr) : bool := match lbl c l with
 | Some r' => Nat.eqb (List.length r') (List.length r) | None => false end.

Fixpoint chk (n : nat) (g : env) (top : N) (e : expr) (dst : dest) (r : list B.instr) {struct n} : option (list B.instr) :=
 match n with O => None | S n =>
 let tst := chkT n in let op := chkOp n in
 match e with
 | EType a => chk n g top a dst r
 | ELet x a b => match a with
   | EVar y => match lookup y g with
     | Some s => chk n ((x, s) :: g) top b dst r
     | None => match chk n g (top + 1) a (DSlot top) r with
       | Some r1 => chk n ((x, top) :: g) (top + 1) b dst r1 | None => None end end
   | _ => match chk n g (top + 1) a (DSlot top) r with
     | Some r1 => chk n ((x, top) :: g) (top + 1) b dst r1 | None => None end end
 | EIf t a b => match tst g top t r with
   | None => None
   | Some (l, r1) => match dst with
     | DSlot d => match chk n g top a dst r1 with
       | Some (B.IJump e0 :: B.ILabel l' :: r3) =>
         if N.eqb l l' && lbl_ok l r3 then match chk n g top b dst r3 with
           | Some (B.ILabel e0' :: r') => if N.eqb e0 e0' && lbl_ok e0 r' then Some r' else None
           | _ => None end else None
       | _ => None end
     | DRet => match chk n g top a dst r1 with
       | Some (B.ILabel l' :: r3) => if N.eqb l l' && lbl_ok l r3 then chk n g top b dst r3 else None
       | _ => None end end end
 | ECond [] => match dst, r with
   | DSlot d, B.IPrim d' q [] :: r' => if N.eqb d d' && q_eqb B.PRaiseCond q then Some r' else None
   | DRet, _ => match op g top e r with
     | Some (o, _, B.IReturn o' :: r') => if o_eqb o o' then Some r' else None | _ => None end
   | _, _ => None end
 | ECond ((EBool true, x) :: _) => chk n g top x dst r
 | ECond ((t, a) :: rest) => match tst g top t r with
   | None => None
   | Some (l, r1) => match dst with
     | DSlot d => match chk n g top a dst r1 with
       | Some (B.IJump e0 :: B.ILabel l' :: r3) =>
         if N.eqb l l' && lbl_ok l r3 then match chk n g top (ECond rest) dst r3 with
           | Some (B.ILabel e0' :: r') => if N.eqb e0 e0' && lbl_ok e0 r' then Some r' else None
           | _ => None end else None
       | _ => None end
     | DRet => match chk n g top a dst r1 with
       | Some (B.ILabel l' :: r3) => if N.eqb l l' && lbl_ok l r3 then chk n g top (ECond rest) dst r3 else None
       | _ => None end end end
 | ECall f args => match prim_of_name f with
   | Some p => match pmap p, dst with
     | Some q, DSlot d =>
       if Nat.eqb (List.length args) (prim_arity p) && negb (Nat.eqb (List.length args) 0) then
         match chkOps n g top args r with
         | Some (ops, B.IPrim d' q' ops' :: r') =>
           if N.eqb d d' && q_eqb q q' && os_eqb ops ops' then Some r' else None
         | _ => None end
       else None
     | Some _, DRet => match op g top e r with
       | Some (o, _, B.IReturn o' :: r') => if o_eqb o o' then Some r' else None | _ => None end
     | None, _ => None end
   | None => let k := N.of_nat (List.length args) in match dst with
     | DSlot d => match chkW n g (top + 2) args r with
       | Some (i :: r') => if is_call i d top (B.sym_of_text f) k then Some r' else None
       | _ => None end
     | DRet => let t := N.max top (k + 2) in match chkTA n g 2 t args [] r with
       | Some (i :: r') => if is_tailcall i (B.sym_of_text f) k then Some r' else None
       | _ => None end end end
 | _ => match dst with
   | DRet => match op g top e r with
     | Some (o, _, B.IReturn o' :: r') => if o_eqb o o' then Some r' else None | _ => None end
   | DSlot d => match e with
     | EVar x => match lookup x g with
       | Some s => if N.eqb s d then Some r else match r with
         | B.IMove d' s' :: r' => if N.eqb d d' && N.eqb s s' then Some r' else None | _ => None end
       | None => None end
     | EAnd x y => match tst g top x r with
       | Some (l1, r1) => match tst g top y r1 with
         | Some (l, B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r') =>
           if N.eqb l1 l && N.eqb d d1 && N.eqb d d2 && N.eqb l l' && N.eqb e0 e0' && is_bool (konst c kt) true
              && is_bool (konst c kf) false && lbl_ok l (B.IConst d2 kf :: B.ILabel e0' :: r') && lbl_ok e0 r'
           then Some r' else None
         | _ => None end
       | None => None end
     | EOr x y => match tst g top x r with
       | Some (nx, B.IJump th :: B.ILabel nx' :: r2) =>
         if N.eqb nx nx' && lbl_ok nx r2 then match tst g top y r2 with
           | Some (l, B.ILabel th' :: B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r') =>
             if N.eqb th th' && N.eqb d d1 && N.eqb d d2 && N.eqb l l' && N.eqb e0 e0' && is_bool (konst c kt) true
                && is_bool (konst c kf) false && lbl_ok th (B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r')
                && lbl_ok l (B.IConst d2 kf :: B.ILabel e0' :: r') && lbl_ok e0 r'
             then Some r' else None
           | _ => None end else None
       | _ => None end
     | _ => match lit_val e, r with
       | Some v, B.IConst d' k :: r' => match konst c k with
         | Some w => if N.eqb d d' && vrb v w then Some r' else None | None => None end
       | _, _ => None end end end end end

with chkT (n : nat) (g : env) (top : N) (e : expr) (r : list B.instr) {struct n} : option (N * list B.instr) :=
 match n with O => None | S n =>
 match e with
 | EType a => chkT n g top a r
 | EAnd x y => match chkT n g top x r with
   | Some (l1, r1) => match chkT n g top y r1 with
     | Some (l2, r2) => if N.eqb l1 l2 then Some (l2, r2) else None | None => None end
   | None => None end
 | EOr x y => match chkT n g top x r with
   | Some (nx, B.IJump th :: B.ILabel nx' :: r2) =>
     if N.eqb nx nx' && lbl_ok nx r2 then match chkT n g top y r2 with
       | Some (l, B.ILabel th' :: r') => if N.eqb th th' && lbl_ok th r' then Some (l, r') else None
       | _ => None end else None
   | _ => None end
 | ELet x a b => match a with
   | EVar y => match lookup y g with
     | Some s => chkT n ((x, s) :: g) top b r
     | None => match chk n g (top + 1) a (DSlot top) r with
       | Some r1 => chkT n ((x, top) :: g) (top + 1) b r1 | None => None end end
   | _ => match chk n g (top + 1) a (DSlot top) r with
     | Some r1 => chkT n ((x, top) :: g) (top + 1) b r1 | None => None end end
 | _ => match chkOp n g top e r with
   | Some (o, _, B.IJumpIfFalse o' l :: r') => if o_eqb o o' then Some (l, r') else None
   | _ => None end end end

with chkOp (n : nat) (g : env) (top : N) (e : expr) (r : list B.instr) {struct n} : option (B.operand * N * list B.instr) :=
 match n with O => None | S n =>
 match e with
 | EType a => chkOp n g top a r
 | EVar x => match lookup x g with
   | Some s => if N.ltb s top then Some (B.OSlot s, top, r) else None
   | None => None end
 | _ => match lit_val e with
   | Some v => match find_k (B.code_consts c) v 0 with Some k => Some (B.OConst k, top, r) | None => None end
   | None => match chk n g (top + 1) e (DSlot top) r with
     | Some r1 => Some (B.OSlot top, top + 1, r1) | None => None end end end end

with chkOps (n : nat) (g : env) (top : N) (es : list expr) (r : list B.instr) {struct n} : option (list B.operand * list B.instr) :=
 match n with O => None | S n =>
 match es with
 | [] => Some ([], r)
 | e :: es => match chkOp n g top e r with
   | Some (o, top2, r1) => match chkOps n g top2 es r1 with
     | Some (os, r') => Some (o :: os, r') | None => None end
   | None => None end end end

with chkW (n : nat) (g : env) (s : N) (es : list expr) (r : list B.instr) {struct n} : option (list B.instr) :=
 match n with O => None | S n =>
 match es with
 | [] => Some r
 | e :: es => match chk n g (s + 1) e (DSlot s) r with
   | Some r1 => chkW n g (s + 1) es r1 | None => None end end end

with chkTA (n : nat) (g : env) (s t : N) (es : list expr) (ms : list (N * N)) (r : list B.instr) {struct n} : option (list B.instr) :=
 match n with O => None | S n =>
 match es with
 | [] => moves_prefix ms r
 | e :: es =>
   let other (_ : unit) :=
     if reads g es s then match chk n g (t + 1) e (DSlot t) r with
       | Some r1 => chkTA n g (s + 1) (t + 1) es ((s, t) :: ms) r1 | None => None end
     else match chk n g t e (DSlot s) r with
       | Some r1 => chkTA n (kill s g) (s + 1) t es ms r1 | None => None end in
   match e with
   | EVar x => match lookup x g with
     | Some u => if N.eqb u s then chkTA n g (s + 1) t es ms r else other tt
     | None => other tt end
   | _ => other tt end end end.

(* ---------- soundness ---------- *)
Definition suffix (r : list B.instr) := exists p, ins c = p ++ r.
Lemma suffix_tail : forall x r, suffix (x :: r) -> suffix r.
Proof. intros x r [p H]. exists (p ++ [x]). rewrite H, <- app_assoc. reflexivity. Qed.
Lemma app_same_len : forall (p q a b : list B.instr), p ++ a = q ++ b -> List.length p = List.length q -> a = b.
Proof.
 induction p as [|x p IH]; intros [|y q] a b H L; cbn in *; try discriminate; auto.
 inversion H; subst. eapply IH; eauto.
Qed.
Lemma suffix_eq : forall a b, suffix a -> suffix b -> List.length a = List.length b -> a = b.
Proof.
 intros a b [p Hp] [q Hq] L. rewrite Hp in Hq.
 assert (Lp : List.length p = List.length q) by (apply (f_equal (@List.length _)) in Hq; rewrite !app_length in Hq; lia).
 eapply app_same_len; eauto.
Qed.
Lemma find_label_suffix : forall l iss r, B.find_label l iss = Some r -> exists p, iss = p ++ r.
Proof.
 intros l iss. induction iss as [|i iss IH]; intros r H; [discriminate|].
 assert (Rest : B.find_label l iss = Some r -> exists p, i :: iss = p ++ r).
 { intro Hf. destruct (IH r Hf) as [p E]. exists (i :: p). rewrite E. reflexivity. }
 destruct i; cbn in H; try (apply Rest; exact H).
 destruct (N.eqb l0 l); [inversion H; subst; exists [B.ILabel l0]; reflexivity|apply Rest; exact H].
Qed.
Lemma lbl_ok_sound : forall l r, lbl_ok l r = true -> suffix r -> lbl c l = Some r.
Proof.
 intros l r H S. unfold lbl_ok in H. destruct (lbl c l) as [r'|] eqn:E; [|discriminate].
 apply Nat.eqb_eq in H. f_equal. apply suffix_eq; auto. apply (find_label_suffix l). exact E.
Qed.

Lemma suffix_cons : forall x r, suffix (x :: r) -> suffix r.
Proof. exact suffix_tail. Qed.

Ltac sat_suffix := repeat match goal with
 | H : suffix (_ :: ?r) |- _ => lazymatch goal with _ : suffix r |- _ => fail | _ => pose proof (suffix_cons _ _ H) end
 end.

Ltac dm H := match type of H with
 | context [match ?x with _ => _ end] => let E := fresh "E" in destruct x eqn:E
 end.

Ltac clean := repeat match goal with
 | H : None = Some _ |- _ => discriminate H
 | H : Some _ = None |- _ => discriminate H
 | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
 | H : (_, _) = (_, _) |- _ => injection H; clear H; intros; subst
 | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H as [? ?]
 | H : N.eqb _ _ = true |- _ => apply N.eqb_eq in H; subst
 | H : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in H
 | H : N.ltb _ _ = true |- _ => apply N.ltb_lt in H
 | H : negb _ = true |- _ => apply negb_true_iff in H
 | H : Nat.eqb _ _ = false |- _ => apply Nat.eqb_neq in H
 | H : o_eqb _ _ = true |- _ => apply o_eqb_eq in H; subst
 | H : os_eqb _ _ = true |- _ => apply os_eqb_eq in H; subst
 | H : q_eqb _ _ = true |- _ => apply q_eqb_eq in H; subst
 | H : false = true |- _ => discriminate H
 | H : N.eqb _ _ = false |- _ => apply N.eqb_neq in H
 end.

Ltac crush H := cbn [chk chkT chkOp chkOps chkW chkTA] in H; repeat (dm H; clean; try discriminate); clean.

Ltac use IC IT IO IOs IW ITA := repeat match goal with
  | H : chk _ _ _ _ _ _ = Some _, S : suffix _ |- _ => let A := fresh in let B0 := fresh in
      destruct (IC _ _ _ _ _ _ H S) as [A B0]; clear H
  | H : chkT _ _ _ _ _ = Some (_, _), S : suffix _ |- _ => let A := fresh in let B0 := fresh in
      destruct (IT _ _ _ _ _ _ H S) as [A B0]; clear H
  | H : chkOp _ _ _ _ _ = Some (_, _, _), S : suffix _ |- _ => let A := fresh in let B0 := fresh in
      destruct (IO _ _ _ _ _ _ _ H S) as [A B0]; clear H
  | H : chkOps _ _ _ _ _ = Some (_, _), S : suffix _ |- _ => let A := fresh in let B0 := fresh in
      destruct (IOs _ _ _ _ _ _ H S) as [A B0]; clear H
  | H : chkW _ _ _ _ _ = Some _, S : suffix _ |- _ => let A := fresh in let B0 := fresh in
      destruct (IW _ _ _ _ _ H S) as [A B0]; clear H
  | H : chkTA _ _ _ _ _ _ _ = Some _, S : suffix _ |- _ => let A := fresh in let B0 := fresh in
      destruct (ITA _ _ _ _ _ _ _ H S) as [A B0]; clear H
  | H : lbl_ok ?l ?r = true, S : suffix ?r |- _ => apply (lbl_ok_sound l r H) in S; clear H
  | H : is_bool _ _ = true |- _ => apply is_bool_eq in H
  | H : vrb _ _ = true |- _ => apply vrb_sound in H
  | H : is_call _ _ _ _ _ = true |- _ => apply is_call_ok in H
  | H : is_tailcall _ _ _ = true |- _ => apply is_tailcall_ok in H
  | H : moves_prefix _ _ = Some _ |- _ => apply moves_prefix_ok in H
  | _ => progress sat_suffix
  end.

Theorem chk_sound : forall n,
 (forall g top e dst r r', chk n g top e dst r = Some r' -> suffix r -> Comp c g top e dst r r' /\ suffix r') /\
 (forall g top e r l r', chkT n g top e r = Some (l, r') -> suffix r -> CompT c g top e l r r' /\ suffix r') /\
 (forall g top e r o top2 r', chkOp n g top e r = Some (o, top2, r') -> suffix r -> CompOp c g top e o top2 r r' /\ suffix r') /\
 (forall g top es r os r', chkOps n g top es r = Some (os, r') -> suffix r -> CompOps c g top es os r r' /\ suffix r') /\
 (forall g s es r r', chkW n g s es r = Some r' -> suffix r -> CompW c g s es r r' /\ suffix r') /\
 (forall g s t es ms r r', chkTA n g s t es ms r = Some r' -> suffix r -> CompTA c g s t es ms r r' /\ suffix r').
Proof.
 induction n as [|n IH]; [repeat split; intros; discriminate|].
 destruct IH as (IC & IT & IO & IOs & IW & ITA).
 refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
 - (* chk *) intros g top e dst r r' H S. destruct e; crush H; use IC IT IO IOs IW ITA.
   all: try (split; [econstructor; eauto|eauto]; fail).
   all: try (split; [eapply C_tail; eauto; lia|eauto]; fail).
   split; [|assumption]. eapply C_prim; [exact E|exact E0|exact H0|intro Ea; subst; exact (H1 eq_refl)|exact H].
 - (* chkT *) intros g top e r l r' H S. destruct e; crush H; use IC IT IO IOs IW ITA.
   all: try (split; [econstructor; eauto|eauto]; fail).
   all: try (split; [eapply T_leaf; eauto|eauto]; fail).
 - (* chkOp *) intros g top e r o top2 r' H S. destruct e; crush H; use IC IT IO IOs IW ITA.
   all: try (split; [econstructor; eauto|eauto]; fail).
   all: match goal with F : find_k _ _ 0 = Some _ |- _ =>
     destruct (find_k_sound _ _ _ _ F) as (w & W1 & W2 & W3); rewrite Nat.sub_0_r in W1;
     split; [eapply O_lit; [eassumption|exact W1|exact W2]|assumption] end.
 - (* chkOps *) intros g top es r os r' H S. destruct es; crush H; use IC IT IO IOs IW ITA.
   all: try (split; [econstructor; eauto|eauto]; fail).
 - (* chkW *) intros g s es r r' H S. destruct es; crush H; use IC IT IO IOs IW ITA.
   all: try (split; [econstructor; eauto|eauto]; fail).
 - (* chkTA *) intros g s t es ms r r' H S. destruct es; crush H; use IC IT IO IOs IW ITA.
   all: try (split; [econstructor; eauto|eauto]; fail).
   all: try (split; [eapply TA_same; eauto|eauto]; fail).
   all: try (split; [eapply TA_temp; eauto|eauto]; fail).
   all: try (split; [eapply TA_direct; eauto|eauto]; fail).
   all: match goal with M : ?r = map _ ?ms ++ ?r' |- _ =>
     subst r; split; [constructor|destruct S as [p0 Hp]; exists (p0 ++ map (fun m => B.IMove (fst m) (snd m)) ms); rewrite Hp, <- app_assoc; reflexivity] end.
Qed.
End Check.

(* Fuel bounds the checker's recursion; running out only rejects. *)
Definition fuel : nat := 4096.
Definition check_fn (c : B.code) (ps : list name) (b : expr) : bool :=
 match chk c fuel (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins c) with
 | Some _ => true | None => false end.

Lemma chk_fn_sound : forall c n ps b,
 match chk c n (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins c) with Some _ => true | None => false end = true ->
 CompFn c ps b.
Proof.
 intros c n ps b H.
 destruct (chk c n (bind ps 2) (2 + N.of_nat (List.length ps)) b DRet (B.code_ins c)) as [r'|] eqn:E; [|discriminate].
 exists r'. refine (proj1 (proj1 (chk_sound c n) _ _ _ _ _ _ E _)). exists []. reflexivity.
Qed.

(* Acceptance is a proof that the code is a lowering of the definition, in the sense JitLowerThm uses. *)
Theorem check_fn_sound : forall c ps b, check_fn c ps b = true -> CompFn c ps b.
Proof. intros c ps b. unfold check_fn. generalize fuel. intro n. apply chk_fn_sound. Qed.
End JitLowerCheck.
