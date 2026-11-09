(* Port of rocq/JitLowerStage0.v: translation validation of stage 0 output. Each definition's form
   (<file>.forms) and code object (<file>.sbc) are decoded here from generic trees, and
   JitLowerCheck decides whether the code is related to the definition. The trees come from a
   trusted tokenizer (stage0_to_fstar.py, the F* twin of tests/shen-jit/stage0_to_rocq.py). *)
module Buri.JitLowerStage0
open Buri.Lib
open Buri.KLSyntax
open Buri.KLValue
open Buri.KLSemantics
open Buri.JitLowerRel
open Buri.JitLowerCheck
module B = Buri.JitBytecode

type sx = | XSym : s:string -> sx | XInt : z:int -> sx | XReal : b:nat -> sx | XStr : t:list nat -> sx
          | XList : l:list sx -> sx

let rec to_value (x : sx) : Tot value (decreases x) = match x with
  | XSym s -> if s = "true" then VBool true else if s = "false" then VBool false
              else VSym (of_string s)
  | XInt z -> VNum (NInt z) | XReal b -> VNum (NFloat b) | XStr t -> VStr t
  | XList l -> to_value_list l
and to_value_list (l : list sx) : Tot value (decreases l) = match l with
  | [] -> VNil | a :: d -> VCons (to_value a) (to_value_list d)
let rec to_val (x : sx) : Tot B.val_ (decreases x) = match x with
  | XSym s -> if s = "true" then B.VBool true else if s = "false" then B.VBool false
              else B.VSym (B.sym s)
  | XInt z -> B.VFix z | XReal b -> B.VReal b | XStr t -> B.VStr t
  | XList l -> to_val_list l
and to_val_list (l : list sx) : Tot B.val_ (decreases l) = match l with
  | [] -> B.VNil | a :: d -> B.VPair (to_val a) (to_val_list d)

(* Rocq writes XList's case as fold_right over the list; these say the mutual forms are that. *)
let rec to_value_list_fold (l : list sx)
  : Lemma (to_value_list l == fold_right (fun a d -> VCons (to_value a) d) VNil l) =
  match l with [] -> () | _ :: d -> to_value_list_fold d
let rec to_val_list_fold (l : list sx)
  : Lemma (to_val_list l == fold_right (fun a d -> B.VPair (to_val a) d) B.VNil l) =
  match l with [] -> () | _ :: d -> to_val_list_fold d

type verdict = | Accepted : f:name -> verdict | Rejected : f:name -> verdict | Unparsed

let judge (form sbc : sx) : verdict =
  match parse [] (to_value form), to_val sbc with
  | Some (EDefun f ps b), B.VPair (B.VSym _) (B.VPair (B.VSym g) (B.VPair code B.VNil)) ->
    if not (B.sym_of_text f = g) then Unparsed else
    (match B.build_code B.prim_tree 64 code with
     | B.LOk c ->
       if B.code_arity c = length ps
          && (match B.code_entry c with None -> true | Some _ -> false)
          && check_fn c ps b
       then Accepted f else Rejected f
     | B.LErr _ -> Rejected f)
  | _, _ -> Unparsed

let rec judge_all (fs ss : list sx) : list verdict = match fs, ss with
  | f :: fs, s :: ss -> judge f s :: judge_all fs ss
  | [], [] -> []
  | _, _ -> [Unparsed]

let tally (fs ss : list sx) : nat & nat & nat & list name =
  fold_right #(nat & nat & nat & list name) #verdict (fun v acc -> let (a, r, u, names) = acc in match v with
    | Accepted f -> (a + 1, r, u, f :: names)
    | Rejected _ -> (a, r + 1, u, names)
    | Unparsed -> (a, r, u + 1, names)) (0, 0, 0, []) (judge_all fs ss)

let counts (fs ss : list sx) : nat & nat & nat =
  let (a, r, u, _) = tally fs ss in (a, r, u)
