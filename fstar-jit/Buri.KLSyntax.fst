(* Port of rocq/KLSyntax.v: the canonical KLambda surface and resolved syntax. *)
module Buri.KLSyntax
open Buri.Lib
open Buri.Observation

type name = text
let rec text_eqb (a b : text) : bool =
  match a, b with
  | [], [] -> true
  | x :: a, y :: b -> x = y && text_eqb a b
  | _, _ -> false

let rec text_eqb_eq (a b : text) : Lemma (text_eqb a b = true <==> a == b) =
  match a, b with
  | _ :: a', _ :: b' -> text_eqb_eq a' b'
  | _ -> ()
let text_eqb_refl (a : text) : Lemma (text_eqb a a = true) = text_eqb_eq a a
let text_eqb_neq (a b : text) : Lemma (text_eqb a b = false <==> ~(a == b)) = text_eqb_eq a b

(* Exact integers, and binary64 bit patterns. *)
type num = | NInt of int | NFloat of nat

type prim =
  | PIntern
  | PPos | PTlstr | PCn | PStr | PStringP | PNToString | PStringToN
  | PSet | PValue
  | PSimpleError | PErrorToString
  | PCons | PHd | PTl | PConsP
  | PEqual | PEvalKL
  | PAbsvector | PAddressSet | PAddressGet | PAbsvectorP
  | PWriteByte | PReadByte | POpen | PClose
  | PGetTime
  | PAdd | PSub | PMul | PDiv | PGt | PLt | PGe | PLe | PNumberP

let all_prims : list prim =
  [PIntern; PPos; PTlstr; PCn; PStr; PStringP; PNToString; PStringToN; PSet; PValue;
   PSimpleError; PErrorToString; PCons; PHd; PTl; PConsP; PEqual; PEvalKL;
   PAbsvector; PAddressSet; PAddressGet; PAbsvectorP; PWriteByte; PReadByte; POpen; PClose;
   PGetTime; PAdd; PSub; PMul; PDiv; PGt; PLt; PGe; PLe; PNumberP]
(* Rocq: destruct p; cbn; tauto. Here: SMT, with enough fuel to unroll the 36-element list. *)
#push-options "--fuel 37 --ifuel 1 --z3rlimit 20"
let all_prims_complete (p : prim) : Lemma (mem_l p all_prims) = ()
#pop-options

let prim_name (p : prim) : string = match p with
  | PIntern -> "intern" | PPos -> "pos" | PTlstr -> "tlstr" | PCn -> "cn" | PStr -> "str"
  | PStringP -> "string?" | PNToString -> "n->string" | PStringToN -> "string->n"
  | PSet -> "set" | PValue -> "value" | PSimpleError -> "simple-error"
  | PErrorToString -> "error-to-string" | PCons -> "cons" | PHd -> "hd" | PTl -> "tl"
  | PConsP -> "cons?" | PEqual -> "=" | PEvalKL -> "eval-kl" | PAbsvector -> "absvector"
  | PAddressSet -> "address->" | PAddressGet -> "<-address" | PAbsvectorP -> "absvector?"
  | PWriteByte -> "write-byte" | PReadByte -> "read-byte" | POpen -> "open" | PClose -> "close"
  | PGetTime -> "get-time" | PAdd -> "+" | PSub -> "-" | PMul -> "*" | PDiv -> "/"
  | PGt -> ">" | PLt -> "<" | PGe -> ">=" | PLe -> "<=" | PNumberP -> "number?"

let prim_arity (p : prim) : nat = match p with
  | PIntern | PTlstr | PStr | PStringP | PNToString | PStringToN | PValue | PSimpleError
  | PErrorToString | PHd | PTl | PConsP | PEvalKL | PAbsvector | PAbsvectorP | PReadByte
  | PClose | PGetTime | PNumberP -> 1
  | PPos | PCn | PSet | PCons | PEqual | PAddressGet | PWriteByte | POpen
  | PAdd | PSub | PMul | PDiv | PGt | PLt | PGe | PLe -> 2
  | PAddressSet -> 3

type special = | SIf | SAnd | SOr | SCond | STrapError | SDefun | SLambda | SLet | SFreeze | SType
let all_specials = [SIf; SAnd; SOr; SCond; STrapError; SDefun; SLambda; SLet; SFreeze; SType]
#push-options "--fuel 11 --ifuel 1"
let all_specials_complete (s : special) : Lemma (mem_l s all_specials) = ()
#pop-options
let special_name (s : special) : string = match s with
  | SIf -> "if" | SAnd -> "and" | SOr -> "or" | SCond -> "cond" | STrapError -> "trap-error"
  | SDefun -> "defun" | SLambda -> "lambda" | SLet -> "let" | SFreeze -> "freeze" | SType -> "type"

(* NoDup over strings, decided: a boolean check, then its meaning. *)
let rec memb_str (x : string) (r : list string) : bool =
  match r with [] -> false | y :: r' -> y = x || memb_str x r'
let rec nodup_str (l : list string) : bool =
  match l with [] -> true | x :: r -> not (memb_str x r) && nodup_str r
let rec memb_str_ok (x : string) (r : list string) : Lemma (memb_str x r = false ==> ~(mem_l x r)) =
  match r with [] -> () | _ :: r' -> memb_str_ok x r'
let rec nodup_str_ok (l : list string) : Lemma (nodup_str l = true ==> nodup_l l) =
  match l with [] -> () | x :: r -> memb_str_ok x r; nodup_str_ok r

let canonical_kl_surface ()
  : Lemma (length all_prims = 36 /\ length all_specials = 10 /\
           nodup_l (app (map prim_name all_prims) (map special_name all_specials))) =
  assert_norm (length all_prims = 36);
  assert_norm (length all_specials = 10);
  assert_norm (nodup_str (app (map prim_name all_prims) (map special_name all_specials)) = true);
  nodup_str_ok (app (map prim_name all_prims) (map special_name all_specials))

(* Resolved KLambda syntax. *)
type expr =
  | ENum : n:num -> expr
  | EStr : t:text -> expr
  | ESym : s:name -> expr
  | EBool : b:bool -> expr
  | ENil : expr
  | EVar : x:name -> expr
  | ELam : x:name -> body:expr -> expr
  | ELet : x:name -> a:expr -> body:expr -> expr
  | EIf : c:expr -> a:expr -> b:expr -> expr
  | EAnd : a:expr -> b:expr -> expr
  | EOr : a:expr -> b:expr -> expr
  | ECond : clauses:list (expr & expr) -> expr
  | ETrap : body:expr -> handler:expr -> expr
  | EFreeze : body:expr -> expr
  | EType : e:expr -> expr
  | EDefun : f:name -> params:list name -> body:expr -> expr
  | EApp : head:expr -> args:list expr -> expr
  | ECall : f:name -> args:list expr -> expr

let special_of (e : expr) : option special = match e with
  | EIf _ _ _ -> Some SIf | EAnd _ _ -> Some SAnd | EOr _ _ -> Some SOr
  | ECond _ -> Some SCond | ETrap _ _ -> Some STrapError | EDefun _ _ _ -> Some SDefun
  | ELam _ _ -> Some SLambda | ELet _ _ _ -> Some SLet | EFreeze _ -> Some SFreeze
  | EType _ -> Some SType | _ -> None
