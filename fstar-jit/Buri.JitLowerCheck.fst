(* Port of rocq/JitLowerCheck.v: a checker deciding, for one code object and one KLambda
   definition, that the code is related to the definition by JitLowerRel.comp; and its soundness.
   Encoding: the checker's mutual fixpoints recurse on fuel `n` (decreases n) as in Rocq.
   Rocq's `vars` local fixpoints are mutual functions. Soundness (check_fn_sound) produces a
   derivation of `comp`: in F* the soundness proof is a total function returning the
   derivation, where Rocq builds a Prop proof by tactics. *)
module Buri.JitLowerCheck
open Buri.Lib
open Buri.Observation
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.JitLowerRel
module B = Buri.JitBytecode

(* ---------- decisions ---------- *)
let rec vrb (v : value) (w : B.val_) : bool = match v, w with
  | VNum (NInt z), B.VFix y -> z = y
  | VNum (NFloat b), B.VReal c -> b = c
  | VSym s, B.VSym p -> B.sym_of_text s = p
  | VBool b, B.VBool c -> b = c
  | VStr t, B.VStr u -> text_eqb t u && length t = length u
  | VNil, B.VNil -> true
  | VCons a d, B.VPair a' d' -> vrb a a' && vrb d d'
  | _, _ -> false

let rec find_k (cs : list B.val_) (v : value) (i : nat) : option nat = match cs with
  | [] -> None
  | w :: cs -> if vrb v w then Some i else find_k cs v (i + 1)

let o_eqb (a b : B.operand) : bool = match a, b with
  | B.OSlot x, B.OSlot y -> x = y | B.OConst x, B.OConst y -> x = y | _, _ -> false
let rec os_eqb (a b : list B.operand) : bool = match a, b with
  | [], [] -> true | x :: a, y :: b -> o_eqb x y && os_eqb a b | _, _ -> false
let q_eqb (a b : B.prim) : bool = match a, b with
  | B.PAdd, B.PAdd | B.PSub, B.PSub | B.PMul, B.PMul | B.PGt, B.PGt | B.PLt, B.PLt | B.PGe, B.PGe
  | B.PLe, B.PLe | B.PCons, B.PCons | B.PHd, B.PHd | B.PTl, B.PTl | B.PConsp, B.PConsp
  | B.PNumberp, B.PNumberp | B.PStringp, B.PStringp | B.PRaiseCond, B.PRaiseCond -> true
  | _, _ -> false
let is_bool (w : option B.val_) (b : bool) : bool = match w with
  | Some (B.VBool c) -> b = c | _ -> false

let rec vars (e : expr) : Tot (list name) (decreases e) = match e with
  | EVar x -> [x]
  | ELet _ a b | EAnd a b | EOr a b | ETrap a b -> app (vars a) (vars b)
  | EIf c a b -> app (vars c) (app (vars a) (vars b))
  | ECond cl -> vars_cl cl
  | EType a | ELam _ a | EFreeze a | EDefun _ _ a -> vars a
  | EApp h args -> app (vars h) (vars_l args)
  | ECall _ args -> vars_l args
  | _ -> []
and vars_cl (l : list (expr & expr)) : Tot (list name) (decreases l) = match l with
  | [] -> [] | (c, b) :: l' -> app (vars c) (app (vars b) (vars_cl l'))
and vars_l (l : list expr) : Tot (list name) (decreases l) = match l with
  | [] -> [] | a :: l' -> app (vars a) (vars_l l')

let reads (g : env) (es : list expr) (s : nat) : bool =
  existsb (fun x -> slot_is (lookup x g) s) (flat_map vars es)

let is_tailcall (i : B.instr) (f : pos) (n : nat) : bool = match i with
  | B.ITail a f' n' | B.ITailSealed a f' n' -> a = 0 && f = f' && n = n' | _ -> false
let is_call (i : B.instr) (d a : nat) (f : pos) (n : nat) : bool = match i with
  | B.ICall d' a' f' n' | B.ICallSealed d' a' f' n' -> d = d' && a = a' && f = f' && n = n'
  | _ -> false

let rec moves_prefix (ms : list (nat & nat)) (r : list B.instr) : option (list B.instr) = match ms, r with
  | [], r -> Some r
  | (s, t) :: ms, B.IMove d u :: r -> if s = d && t = u then moves_prefix ms r else None
  | _, _ -> None

let lbl_ok (c : B.code) (l : nat) (r : list B.instr) : bool = match lbl c l with
  | Some r' -> length r' = length r | None -> false

let chain_head (c : B.code) (d : nat) (p : prim) (args : list expr) : option (value & expr) =
  if 2 + B.code_arity c <= d then (match p, args with
    | PCons, [a; ECall f2 a2] -> (match lit_val a, prim_of_name f2 with
      | Some v, Some PCons -> Some (v, ECall f2 a2) | _, _ -> None)
    | _, _ -> None)
  else None
let konst_vr (c : B.code) (v : value) (k : nat) : bool = match konst c k with Some w -> vrb v w | None -> false
let chain_tail (c : B.code) (d : nat) (v : value) (r : list B.instr) : option (list B.instr) =
  match r with
  | B.IPrim d' q [B.OConst k; B.OSlot d2] :: r' ->
    if d = d' && d = d2 && q_eqb B.PCons q && konst_vr c v k then Some r' else None
  | _ -> None

let rec chk (c : B.code) (n : nat) (g : env) (top : nat) (e : expr) (dst : dest) (r : list B.instr)
  : Tot (option (list B.instr)) (decreases n) =
  if n = 0 then None else
  let n : nat = n - 1 in
  match e with
  | EType a -> chk c n g top a dst r
  | ELet x a b -> (match a with
    | EVar y -> (match lookup y g with
      | Some s -> chk c n ((x, s) :: g) top b dst r
      | None -> (match chk c n g (top + 1) a (DSlot top) r with
        | Some r1 -> chk c n ((x, top) :: g) (top + 1) b dst r1 | None -> None))
    | _ -> (match chk c n g (top + 1) a (DSlot top) r with
      | Some r1 -> chk c n ((x, top) :: g) (top + 1) b dst r1 | None -> None))
  | EIf t a b -> (match chkT c n g top t r with
    | None -> None
    | Some (l, r1) -> (match dst with
      | DSlot d -> (match chk c n g top a dst r1 with
        | Some (B.IJump e0 :: B.ILabel l' :: r3) ->
          if l = l' && lbl_ok c l r3 then (match chk c n g top b dst r3 with
            | Some (B.ILabel e0' :: r') -> if e0 = e0' && lbl_ok c e0 r' then Some r' else None
            | _ -> None) else None
        | _ -> None)
      | DRet -> (match chk c n g top a dst r1 with
        | Some (B.ILabel l' :: r3) -> if l = l' && lbl_ok c l r3 then chk c n g top b dst r3 else None
        | _ -> None)))
  | ECond [] -> (match dst, r with
    | DSlot d, B.IPrim d' q [] :: r' -> if d = d' && q_eqb B.PRaiseCond q then Some r' else None
    | DRet, _ -> (match chkOp c n g top e r with
      | Some (o, _, B.IReturn o' :: r') -> if o_eqb o o' then Some r' else None | _ -> None)
    | _, _ -> None)
  | ECond ((EBool true, x) :: _) -> chk c n g top x dst r
  | ECond ((t, a) :: rest) -> (match chkT c n g top t r with
    | None -> None
    | Some (l, r1) -> (match dst with
      | DSlot d -> (match chk c n g top a dst r1 with
        | Some (B.IJump e0 :: B.ILabel l' :: r3) ->
          if l = l' && lbl_ok c l r3 then (match chk c n g top (ECond rest) dst r3 with
            | Some (B.ILabel e0' :: r') -> if e0 = e0' && lbl_ok c e0 r' then Some r' else None
            | _ -> None) else None
        | _ -> None)
      | DRet -> (match chk c n g top a dst r1 with
        | Some (B.ILabel l' :: r3) -> if l = l' && lbl_ok c l r3 then chk c n g top (ECond rest) dst r3 else None
        | _ -> None)))
  | ECall f args -> (match prim_of_name f with
    | Some p -> (match pmap p, dst with
      | Some q, DSlot d -> (match chain_head c d p args with
        | Some (v, e2) -> (match chk c n g top e2 (DSlot d) r with
          | Some r1 -> chain_tail c d v r1 | None -> None)
        | None ->
          if length args = prim_arity p && not (length args = 0) then
            (match chkOps c n g top args r with
             | Some (ops, B.IPrim d' q' ops' :: r') ->
               if d = d' && q_eqb q q' && os_eqb ops ops' then Some r' else None
             | _ -> None)
          else None)
      | Some _, DRet -> (match chkOp c n g top e r with
        | Some (o, _, B.IReturn o' :: r') -> if o_eqb o o' then Some r' else None | _ -> None)
      | None, _ -> None)
    | None -> let k = length args in (match dst with
      | DSlot d -> (match chkW c n g (top + 2) args r with
        | Some (i :: r') -> if is_call i d top (B.sym_of_text f) k then Some r' else None
        | _ -> None)
      | DRet -> let t = nmax top (k + 2) in (match chkTA c n g 2 t args [] r with
        | Some (i :: r') -> if is_tailcall i (B.sym_of_text f) k then Some r' else None
        | _ -> None)))
  | _ -> (match dst with
    | DRet -> (match chkOp c n g top e r with
      | Some (o, _, B.IReturn o' :: r') -> if o_eqb o o' then Some r' else None | _ -> None)
    | DSlot d -> (match e with
      | EVar x -> (match lookup x g with
        | Some s -> if s = d then Some r else (match r with
          | B.IMove d' s' :: r' -> if d = d' && s = s' then Some r' else None | _ -> None)
        | None -> None)
      | EAnd x y -> (match chkT c n g top x r with
        | Some (l1, r1) -> (match chkT c n g top y r1 with
          | Some (l, B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r') ->
            if l1 = l && d = d1 && d = d2 && l = l' && e0 = e0' && is_bool (konst c kt) true
               && is_bool (konst c kf) false && lbl_ok c l (B.IConst d2 kf :: B.ILabel e0' :: r') && lbl_ok c e0 r'
            then Some r' else None
          | _ -> None)
        | None -> None)
      | EOr x y -> (match chkT c n g top x r with
        | Some (nx, B.IJump th :: B.ILabel nx' :: r2) ->
          if nx = nx' && lbl_ok c nx r2 then (match chkT c n g top y r2 with
            | Some (l, B.ILabel th' :: B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r') ->
              if th = th' && d = d1 && d = d2 && l = l' && e0 = e0' && is_bool (konst c kt) true
                 && is_bool (konst c kf) false && lbl_ok c th (B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r')
                 && lbl_ok c l (B.IConst d2 kf :: B.ILabel e0' :: r') && lbl_ok c e0 r'
              then Some r' else None
            | _ -> None) else None
        | _ -> None)
      | _ -> (match lit_val e, r with
        | Some v, B.IConst d' k :: r' -> (match konst c k with
          | Some w -> if d = d' && vrb v w then Some r' else None | None -> None)
        | _, _ -> None)))

and chkT (c : B.code) (n : nat) (g : env) (top : nat) (e : expr) (r : list B.instr)
  : Tot (option (nat & list B.instr)) (decreases n) =
  if n = 0 then None else
  let n : nat = n - 1 in
  match e with
  | EType a -> chkT c n g top a r
  | EAnd x y -> (match chkT c n g top x r with
    | Some (l1, r1) -> (match chkT c n g top y r1 with
      | Some (l2, r2) -> if l1 = l2 then Some (l2, r2) else None | None -> None)
    | None -> None)
  | EOr x y -> (match chkT c n g top x r with
    | Some (nx, B.IJump th :: B.ILabel nx' :: r2) ->
      if nx = nx' && lbl_ok c nx r2 then (match chkT c n g top y r2 with
        | Some (l, B.ILabel th' :: r') -> if th = th' && lbl_ok c th r' then Some (l, r') else None
        | _ -> None) else None
    | _ -> None)
  | ELet x a b -> (match a with
    | EVar y -> (match lookup y g with
      | Some s -> chkT c n ((x, s) :: g) top b r
      | None -> (match chk c n g (top + 1) a (DSlot top) r with
        | Some r1 -> chkT c n ((x, top) :: g) (top + 1) b r1 | None -> None))
    | _ -> (match chk c n g (top + 1) a (DSlot top) r with
      | Some r1 -> chkT c n ((x, top) :: g) (top + 1) b r1 | None -> None))
  | _ -> (match chkOp c n g top e r with
    | Some (o, _, B.IJumpIfFalse o' l :: r') -> if o_eqb o o' then Some (l, r') else None
    | _ -> None)

and chkOp (c : B.code) (n : nat) (g : env) (top : nat) (e : expr) (r : list B.instr)
  : Tot (option (B.operand & nat & list B.instr)) (decreases n) =
  if n = 0 then None else
  let n : nat = n - 1 in
  match e with
  | EType a -> chkOp c n g top a r
  | EVar x -> (match lookup x g with
    | Some s -> if s < top then Some (B.OSlot s, top, r) else None
    | None -> None)
  | _ -> (match lit_val e with
    | Some v -> (match find_k (B.code_consts c) v 0 with Some k -> Some (B.OConst k, top, r) | None -> None)
    | None -> (match chk c n g (top + 1) e (DSlot top) r with
      | Some r1 -> Some (B.OSlot top, top + 1, r1) | None -> None))

and chkOps (c : B.code) (n : nat) (g : env) (top : nat) (es : list expr) (r : list B.instr)
  : Tot (option (list B.operand & list B.instr)) (decreases n) =
  if n = 0 then None else
  let n : nat = n - 1 in
  match es with
  | [] -> Some ([], r)
  | e :: es -> (match chkOp c n g top e r with
    | Some (o, top2, r1) -> (match chkOps c n g top2 es r1 with
      | Some (os, r') -> Some (o :: os, r') | None -> None)
    | None -> None)

and chkW (c : B.code) (n : nat) (g : env) (s : nat) (es : list expr) (r : list B.instr)
  : Tot (option (list B.instr)) (decreases n) =
  if n = 0 then None else
  let n : nat = n - 1 in
  match es with
  | [] -> Some r
  | e :: es -> (match chk c n g (s + 1) e (DSlot s) r with
    | Some r1 -> chkW c n g (s + 1) es r1 | None -> None)

and chkTA (c : B.code) (n : nat) (g : env) (s t : nat) (es : list expr) (ms : list (nat & nat)) (r : list B.instr)
  : Tot (option (list B.instr)) (decreases n) =
  if n = 0 then None else
  let n : nat = n - 1 in
  match es with
  | [] -> moves_prefix ms r
  | e :: es ->
    let other (_ : unit) : option (list B.instr) =
      if reads g es s then (match chk c n g (t + 1) e (DSlot t) r with
        | Some r1 -> chkTA c n g (s + 1) (t + 1) es ((s, t) :: ms) r1 | None -> None)
      else (match chk c n g t e (DSlot s) r with
        | Some r1 -> chkTA c n (kill s g) (s + 1) t es ms r1 | None -> None) in
    (match e with
     | EVar x -> (match lookup x g with
       | Some u -> if u = s then chkTA c n g (s + 1) t es ms r else other ()
       | None -> other ())
     | _ -> other ())

let fuel : nat = 4096
let check_fn (c : B.code) (ps : list name) (b : expr) : bool =
  match chk c fuel (bind ps 2) (2 + length ps) b DRet (B.code_ins c) with
  | Some _ -> true | None -> false

(* ---------- soundness ---------- *)
let rec text_eqb_eq' (t u : text)
  : Lemma (requires text_eqb t u = true /\ length t = length u) (ensures t == u) =
  match t, u with
  | _ :: t', _ :: u' -> text_eqb_eq' t' u'
  | _ -> ()

let rec vrb_sound (v : value) (w : B.val_) : Pure (vr v w) (requires vrb v w = true) (ensures fun _ -> True) =
  match v, w with
  | VNum (NInt z), B.VFix y -> VR_int z
  | VNum (NFloat b), B.VReal c -> VR_real b
  | VSym s, B.VSym p -> VR_sym s
  | VBool b, B.VBool c -> VR_bool b
  | VStr t, B.VStr u -> text_eqb_eq' t u; VR_str t
  | VNil, B.VNil -> VR_nil
  | VCons a d, B.VPair a' d' -> VR_cons a a' d d' (vrb_sound a a') (vrb_sound d d')

(* find_k: the constant found is related to v. *)
let rec find_k_sound (cs : list B.val_) (v : value) (i : nat) (k : nat)
  : Pure (w : B.val_ & vr v w)
    (requires find_k cs v i == Some k)
    (ensures fun (| w, _ |) -> i <= k /\ nth_error cs (k - i) == Some w) (decreases cs) =
  match cs with
  | w :: cs' -> if vrb v w then (| w, vrb_sound v w |) else find_k_sound cs' v (i + 1) k

let o_eqb_eq (a b : B.operand) : Lemma (requires o_eqb a b = true) (ensures a == b) = ()
let rec os_eqb_eq (a b : list B.operand) : Lemma (requires os_eqb a b = true) (ensures a == b) =
  match a, b with _ :: a', _ :: b' -> os_eqb_eq a' b' | _ -> ()
let q_eqb_eq (a b : B.prim) : Lemma (requires q_eqb a b = true) (ensures a == b) = ()
let is_bool_eq (w : option B.val_) (b : bool) : Lemma (requires is_bool w b = true) (ensures w == Some (B.VBool b)) = ()
let is_tailcall_ok (i : B.instr) (f : pos) (n : nat)
  : Lemma (requires is_tailcall i f n = true) (ensures tail_instr i 0 f n) = ()
let is_call_ok (i : B.instr) (d a : nat) (f : pos) (n : nat)
  : Lemma (requires is_call i d a f n = true) (ensures call_instr i d a f n) = ()
let rec moves_prefix_ok (ms : list (nat & nat)) (r r' : list B.instr)
  : Lemma (requires moves_prefix ms r == Some r') (ensures r == app (moves ms) r') =
  match ms, r with
  | (s, t) :: ms', B.IMove d u :: r1 -> moves_prefix_ok ms' r1 r'
  | _ -> ()

let suffix (c : B.code) (r : list B.instr) : prop = exists (p : list B.instr). ins c == app p r
let suffix_tail (c : B.code) (x : B.instr) (r : list B.instr)
  : Lemma (requires suffix c (x :: r)) (ensures suffix c r) =
  eliminate exists (p : list B.instr). ins c == app p (x :: r)
  with (app_assoc p [x] r; assert (ins c == app (app p [x]) r))
let suffix_app (c : B.code) (x r : list B.instr)
  : Lemma (requires suffix c (app x r)) (ensures suffix c r) =
  eliminate exists (p : list B.instr). ins c == app p (app x r)
  with (app_assoc p x r; assert (ins c == app (app p x) r))
let rec app_same_len (p q a b : list B.instr)
  : Lemma (requires app p a == app q b /\ length p = length q) (ensures a == b) =
  match p, q with
  | _ :: p', _ :: q' -> app_same_len p' q' a b
  | _ -> ()
let suffix_eq (c : B.code) (a b : list B.instr)
  : Lemma (requires suffix c a /\ suffix c b /\ length a = length b) (ensures a == b) =
  eliminate exists (p q : list B.instr). ins c == app p a /\ ins c == app q b
  with (app_length p a; app_length q b; app_same_len p q a b)
let rec find_label_suffix (l : nat) (iss r : list B.instr)
  : Lemma (requires B.find_label l iss == Some r) (ensures exists p. iss == app p r) =
  match iss with
  | i :: iss' ->
    (match i with
     | B.ILabel x -> if x = l then assert (iss == app [i] r)
       else (find_label_suffix l iss' r;
             eliminate exists p. iss' == app p r
             with assert (iss == app (i :: p) r))
     | _ -> find_label_suffix l iss' r;
             eliminate exists p. iss' == app p r
             with assert (iss == app (i :: p) r))
let lbl_ok_sound (c : B.code) (l : nat) (r : list B.instr)
  : Lemma (requires lbl_ok c l r = true /\ suffix c r) (ensures lbl c l == Some r) =
  match lbl c l with
  | Some r' -> find_label_suffix l (ins c) r'; suffix_eq c r' r

(* Each function below follows its checker case by case and returns the derivation; a branch where
   the checker answers None cannot be reached, which SMT discharges. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let rec chk_sound (c : B.code) (n0 : nat) (g : env) (top : nat) (e : expr) (dst : dest) (r r' : list B.instr)
  : Pure (comp c g top e dst r r')
    (requires chk c n0 g top e dst r == Some r' /\ suffix c r) (ensures fun _ -> suffix c r') (decreases n0) =
  let n : nat = n0 - 1 in
  match e with
  | EType a -> C_type g top a dst r r' (chk_sound c n g top a dst r r')
  | ELet x a b ->
    let general (_ : squash (chk c n g (top + 1) a (DSlot top) r <> None /\
                             chk c n0 g top e dst r == (match chk c n g (top + 1) a (DSlot top) r with
                               | Some r1 -> chk c n ((x, top) :: g) (top + 1) b dst r1 | None -> None)))
      : Pure (comp c g top e dst r r') (requires True) (ensures fun _ -> suffix c r') =
      let Some r1 = chk c n g (top + 1) a (DSlot top) r in
      let da = chk_sound c n g (top + 1) a (DSlot top) r r1 in
      C_let g top x a b dst r r1 r' da (chk_sound c n ((x, top) :: g) (top + 1) b dst r1 r') in
    (match a with
     | EVar y -> (match lookup y g with
       | Some s -> C_alias g top x y s b dst r r' () (chk_sound c n ((x, s) :: g) top b dst r r')
       | None -> general ())
     | _ -> general ())
  | EIf t a b ->
    let Some (l, r1) = chkT c n g top t r in
    let dt = chkT_sound c n g top t r l r1 in
    (match dst with
     | DSlot d ->
       let Some (B.IJump e0 :: B.ILabel l' :: r3) = chk c n g top a dst r1 in
       let da = chk_sound c n g top a dst r1 (B.IJump e0 :: B.ILabel l' :: r3) in
       suffix_tail c (B.IJump e0) (B.ILabel l' :: r3); suffix_tail c (B.ILabel l') r3;
       lbl_ok_sound c l r3;
       let Some (B.ILabel e0' :: r'') = chk c n g top b dst r3 in
       let db = chk_sound c n g top b dst r3 (B.ILabel e0' :: r'') in
       suffix_tail c (B.ILabel e0') r'';
       lbl_ok_sound c e0 r';
       C_if_slot g top t a b d l e0 r r1 r3 r' dt da () db ()
     | DRet ->
       let Some (B.ILabel l' :: r3) = chk c n g top a dst r1 in
       let da = chk_sound c n g top a dst r1 (B.ILabel l' :: r3) in
       suffix_tail c (B.ILabel l') r3;
       lbl_ok_sound c l r3;
       let db = chk_sound c n g top b dst r3 r' in
       C_if_ret g top t a b l r r1 r3 r' dt da () db)
  | ECond [] -> (match dst, r with
    | DSlot d, B.IPrim d' q [] :: r1 -> q_eqb_eq B.PRaiseCond q; suffix_tail c (B.IPrim d' q []) r1;
      C_cond_nil g top d r'
    | DRet, _ ->
      let Some (o, top2, B.IReturn o' :: r1) = chkOp c n g top e r in
      let dop = chkOp_sound c n g top e r o top2 (B.IReturn o' :: r1) in
      suffix_tail c (B.IReturn o') r1;
      C_ret g top e o top2 r r' dop)
  | ECond ((EBool true, x) :: rest) -> C_cond_true g top x rest dst r r' (chk_sound c n g top x dst r r')
  | ECond ((t, a) :: rest) ->
    let Some (l, r1) = chkT c n g top t r in
    let dt = chkT_sound c n g top t r l r1 in
    (match dst with
     | DSlot d ->
       let Some (B.IJump e0 :: B.ILabel l' :: r3) = chk c n g top a dst r1 in
       let da = chk_sound c n g top a dst r1 (B.IJump e0 :: B.ILabel l' :: r3) in
       suffix_tail c (B.IJump e0) (B.ILabel l' :: r3); suffix_tail c (B.ILabel l') r3;
       lbl_ok_sound c l r3;
       let Some (B.ILabel e0' :: r'') = chk c n g top (ECond rest) dst r3 in
       let db = chk_sound c n g top (ECond rest) dst r3 (B.ILabel e0' :: r'') in
       suffix_tail c (B.ILabel e0') r'';
       lbl_ok_sound c e0 r';
       C_cond_slot g top t a rest d l e0 r r1 r3 r' dt da () db ()
     | DRet ->
       let Some (B.ILabel l' :: r3) = chk c n g top a dst r1 in
       let da = chk_sound c n g top a dst r1 (B.ILabel l' :: r3) in
       suffix_tail c (B.ILabel l') r3;
       lbl_ok_sound c l r3;
       let db = chk_sound c n g top (ECond rest) dst r3 r' in
       C_cond_ret g top t a rest l r r1 r3 r' dt da () db)
  | ECall f args -> (match prim_of_name f with
    | Some p -> (match pmap p, dst with
      | Some q, DSlot d -> (match chain_head c d p args with
        | Some (v, e2) ->
          let PCons, [a; ECall f2 a2] = p, args in
          let Some r1 = chk c n g top e2 (DSlot d) r in
          let de = chk_sound c n g top e2 (DSlot d) r r1 in
          let B.IPrim d' q' [B.OConst k; B.OSlot d2] :: r'' = r1 in
          let Some w = konst c k in
          q_eqb_eq B.PCons q';
          suffix_tail c (B.IPrim d' q' [B.OConst k; B.OSlot d2]) r'';
          C_chain g top f a e2 v w k d r r' () () () (vrb_sound v w) de
        | None ->
          let Some (ops, B.IPrim d' q' ops' :: r1) = chkOps c n g top args r in
          let dops = chkOps_sound c n g top args r ops (B.IPrim d' q' ops' :: r1) in
          q_eqb_eq q q'; os_eqb_eq ops ops';
          suffix_tail c (B.IPrim d' q' ops') r1;
          C_prim g top f p q args ops d r r' () () () () dops)
      | Some _, DRet ->
        let Some (o, top2, B.IReturn o' :: r1) = chkOp c n g top e r in
        let dop = chkOp_sound c n g top e r o top2 (B.IReturn o' :: r1) in
        suffix_tail c (B.IReturn o') r1;
        C_ret g top e o top2 r r' dop)
    | None -> let k = length args in (match dst with
      | DSlot d ->
        let Some (i :: r1) = chkW c n g (top + 2) args r in
        let dw = chkW_sound c n g (top + 2) args r (i :: r1) in
        is_call_ok i d top (B.sym_of_text f) k;
        suffix_tail c i r1;
        C_call g top f args d k i r r' () () dw ()
      | DRet -> let t = nmax top (k + 2) in
        let Some (i :: r1) = chkTA c n g 2 t args [] r in
        let dta = chkTA_sound c n g 2 t args [] r (i :: r1) in
        is_tailcall_ok i (B.sym_of_text f) k;
        suffix_tail c i r1;
        C_tail g top f args k t i r r' () () () () dta ()))
  | _ -> (match dst with
    | DRet ->
      let Some (o, top2, B.IReturn o' :: r1) = chkOp c n g top e r in
      let dop = chkOp_sound c n g top e r o top2 (B.IReturn o' :: r1) in
      suffix_tail c (B.IReturn o') r1;
      C_ret g top e o top2 r r' dop
    | DSlot d -> (match e with
      | EVar x -> (match lookup x g with
        | Some s -> if s = d then C_same g top x d r ()
          else (let B.IMove d' s' :: r1 = r in suffix_tail c (B.IMove d' s') r1; C_move g top x s d r' () ())
        | None -> false_elim ())
      | EAnd x y ->
        let Some (l1, r1) = chkT c n g top x r in
        let dx = chkT_sound c n g top x r l1 r1 in
        let Some (l, B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'') = chkT c n g top y r1 in
        let tl = B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'' in
        let dy = chkT_sound c n g top y r1 l tl in
        is_bool_eq (konst c kt) true; is_bool_eq (konst c kf) false;
        suffix_tail c (B.IConst d1 kt) (B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'');
        suffix_tail c (B.IJump e0) (B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'');
        suffix_tail c (B.ILabel l') (B.IConst d2 kf :: B.ILabel e0' :: r'');
        suffix_tail c (B.IConst d2 kf) (B.ILabel e0' :: r'');
        suffix_tail c (B.ILabel e0') r'';
        lbl_ok_sound c l (B.IConst d2 kf :: B.ILabel e0' :: r''); lbl_ok_sound c e0 r'';
        C_and g top x y d l e0 kt kf r r1 r' dx dy () () () ()
      | EOr x y ->
        let Some (nx, B.IJump th :: B.ILabel nx' :: r2) = chkT c n g top x r in
        let dx = chkT_sound c n g top x r nx (B.IJump th :: B.ILabel nx' :: r2) in
        suffix_tail c (B.IJump th) (B.ILabel nx' :: r2); suffix_tail c (B.ILabel nx') r2;
        lbl_ok_sound c nx r2;
        let Some (l, B.ILabel th' :: B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'') = chkT c n g top y r2 in
        let tl = B.ILabel th' :: B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'' in
        let dy = chkT_sound c n g top y r2 l tl in
        is_bool_eq (konst c kt) true; is_bool_eq (konst c kf) false;
        suffix_tail c (B.ILabel th') (B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'');
        suffix_tail c (B.IConst d1 kt) (B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'');
        suffix_tail c (B.IJump e0) (B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'');
        suffix_tail c (B.ILabel l') (B.IConst d2 kf :: B.ILabel e0' :: r'');
        suffix_tail c (B.IConst d2 kf) (B.ILabel e0' :: r'');
        suffix_tail c (B.ILabel e0') r'';
        lbl_ok_sound c th (B.IConst d1 kt :: B.IJump e0 :: B.ILabel l' :: B.IConst d2 kf :: B.ILabel e0' :: r'');
        lbl_ok_sound c l (B.IConst d2 kf :: B.ILabel e0' :: r''); lbl_ok_sound c e0 r'';
        C_or g top x y d l nx th e0 kt kf r r2 r' dx () dy () () () () ()
      | _ ->
        let Some v = lit_val e in
        let B.IConst d' k :: r1 = r in
        let Some w = konst c k in
        suffix_tail c (B.IConst d' k) r1;
        C_lit g top e v w d k r' () () (vrb_sound v w)))

and chkT_sound (c : B.code) (n0 : nat) (g : env) (top : nat) (e : expr) (r : list B.instr) (l : nat) (r' : list B.instr)
  : Pure (compT c g top e l r r')
    (requires chkT c n0 g top e r == Some (l, r') /\ suffix c r) (ensures fun _ -> suffix c r') (decreases n0) =
  let n : nat = n0 - 1 in
  match e with
  | EType a -> T_type g top a l r r' (chkT_sound c n g top a r l r')
  | EAnd x y ->
    let Some (l1, r1) = chkT c n g top x r in
    let dx = chkT_sound c n g top x r l1 r1 in
    T_and g top x y l r r1 r' dx (chkT_sound c n g top y r1 l r')
  | EOr x y ->
    let Some (nx, B.IJump th :: B.ILabel nx' :: r2) = chkT c n g top x r in
    let dx = chkT_sound c n g top x r nx (B.IJump th :: B.ILabel nx' :: r2) in
    suffix_tail c (B.IJump th) (B.ILabel nx' :: r2); suffix_tail c (B.ILabel nx') r2;
    lbl_ok_sound c nx r2;
    let Some (l2, B.ILabel th' :: r'') = chkT c n g top y r2 in
    let dy = chkT_sound c n g top y r2 l2 (B.ILabel th' :: r'') in
    suffix_tail c (B.ILabel th') r'';
    lbl_ok_sound c th r';
    T_or g top x y l nx th r r2 r' dx () dy ()
  | ELet x a b ->
    let general (_ : squash (chk c n g (top + 1) a (DSlot top) r <> None /\
                             chkT c n0 g top e r == (match chk c n g (top + 1) a (DSlot top) r with
                               | Some r1 -> chkT c n ((x, top) :: g) (top + 1) b r1 | None -> None)))
      : Pure (compT c g top e l r r') (requires True) (ensures fun _ -> suffix c r') =
      let Some r1 = chk c n g (top + 1) a (DSlot top) r in
      let da = chk_sound c n g (top + 1) a (DSlot top) r r1 in
      T_let g top x a b l r r1 r' da (chkT_sound c n ((x, top) :: g) (top + 1) b r1 l r') in
    (match a with
     | EVar y -> (match lookup y g with
       | Some s -> T_alias g top x y s b l r r' () (chkT_sound c n ((x, s) :: g) top b r l r')
       | None -> general ())
     | _ -> general ())
  | _ ->
    let Some (o, top2, B.IJumpIfFalse o' l0 :: r1) = chkOp c n g top e r in
    let dop = chkOp_sound c n g top e r o top2 (B.IJumpIfFalse o' l0 :: r1) in
    suffix_tail c (B.IJumpIfFalse o' l0) r1;
    T_leaf g top e o top2 l r r' dop

and chkOp_sound (c : B.code) (n0 : nat) (g : env) (top : nat) (e : expr) (r : list B.instr)
  (o : B.operand) (top2 : nat) (r' : list B.instr)
  : Pure (compOp c g top e o top2 r r')
    (requires chkOp c n0 g top e r == Some (o, top2, r') /\ suffix c r) (ensures fun _ -> suffix c r') (decreases n0) =
  let n : nat = n0 - 1 in
  match e with
  | EType a -> O_type g top a o top2 r r' (chkOp_sound c n g top a r o top2 r')
  | EVar x -> let Some s = lookup x g in O_var g top x s r () ()
  | _ -> (match lit_val e with
    | Some v ->
      let Some k = find_k (B.code_consts c) v 0 in
      let (| w, dv |) = find_k_sound (B.code_consts c) v 0 k in
      O_lit g top e v w k r () () dv
    | None -> O_val g top e r r' (chk_sound c n g (top + 1) e (DSlot top) r r'))

and chkOps_sound (c : B.code) (n0 : nat) (g : env) (top : nat) (es : list expr) (r : list B.instr)
  (os : list B.operand) (r' : list B.instr)
  : Pure (compOps c g top es os r r')
    (requires chkOps c n0 g top es r == Some (os, r') /\ suffix c r) (ensures fun _ -> suffix c r') (decreases n0) =
  let n : nat = n0 - 1 in
  match es with
  | [] -> Os_nil g top r
  | e :: es' ->
    let Some (o, top2, r1) = chkOp c n g top e r in
    let dop = chkOp_sound c n g top e r o top2 r1 in
    let Some (os', r2) = chkOps c n g top2 es' r1 in
    Os_cons g top e es' o os' top2 r r1 r' dop (chkOps_sound c n g top2 es' r1 os' r')

and chkW_sound (c : B.code) (n0 : nat) (g : env) (s : nat) (es : list expr) (r r' : list B.instr)
  : Pure (compW c g s es r r')
    (requires chkW c n0 g s es r == Some r' /\ suffix c r) (ensures fun _ -> suffix c r') (decreases n0) =
  let n : nat = n0 - 1 in
  match es with
  | [] -> W_nil g s r
  | e :: es' ->
    let Some r1 = chk c n g (s + 1) e (DSlot s) r in
    let de = chk_sound c n g (s + 1) e (DSlot s) r r1 in
    W_cons g s e es' r r1 r' de (chkW_sound c n g (s + 1) es' r1 r')

and chkTA_sound (c : B.code) (n0 : nat) (g : env) (s t : nat) (es : list expr) (ms : list (nat & nat))
  (r r' : list B.instr)
  : Pure (compTA c g s t es ms r r')
    (requires chkTA c n0 g s t es ms r == Some r' /\ suffix c r) (ensures fun _ -> suffix c r') (decreases n0) =
  let n : nat = n0 - 1 in
  match es with
  | [] -> moves_prefix_ok ms r r'; suffix_app c (moves ms) r'; TA_nil g s t ms r'
  | e :: es' ->
    let other (_ : squash (chkTA c n0 g s t es ms r ==
        (if reads g es' s then (match chk c n g (t + 1) e (DSlot t) r with
          | Some r1 -> chkTA c n g (s + 1) (t + 1) es' ((s, t) :: ms) r1 | None -> None)
         else (match chk c n g t e (DSlot s) r with
          | Some r1 -> chkTA c n (kill s g) (s + 1) t es' ms r1 | None -> None))))
      : Pure (compTA c g s t es ms r r') (requires True) (ensures fun _ -> suffix c r') =
      if reads g es' s then begin
        let Some r1 = chk c n g (t + 1) e (DSlot t) r in
        let de = chk_sound c n g (t + 1) e (DSlot t) r r1 in
        TA_temp g s t e es' ms r r1 r' de (chkTA_sound c n g (s + 1) (t + 1) es' ((s, t) :: ms) r1 r')
      end else begin
        let Some r1 = chk c n g t e (DSlot s) r in
        let de = chk_sound c n g t e (DSlot s) r r1 in
        TA_direct g s t e es' ms r r1 r' de (chkTA_sound c n (kill s g) (s + 1) t es' ms r1 r')
      end in
    (match e with
     | EVar x -> (match lookup x g with
       | Some u -> if u = s then TA_same g s t x es' ms r r' () (chkTA_sound c n g (s + 1) t es' ms r r')
         else other ()
       | None -> other ())
     | _ -> other ())
#pop-options

let check_fn_sound (c : B.code) (ps : list name) (b : expr)
  : Lemma (requires check_fn c ps b = true) (ensures compFn c ps b) =
  let Some r' = chk c fuel (bind ps 2) (2 + length ps) b DRet (B.code_ins c) in
  assert (ins c == app [] (B.code_ins c));
  let d = chk_sound c fuel (bind ps 2) (2 + length ps) b DRet (B.code_ins c) r' in
  assert (inhabited (comp c (bind ps 2) (2 + length ps) b DRet (B.code_ins c) r'))
