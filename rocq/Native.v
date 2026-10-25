(* First-order pure Scheme execution for captured constructors and private
   helpers. Library operations are explicit mathematical contracts, not a
   theorem about the Chez implementation of those operations. *)
From Coq Require Import List String ZArith Bool Ascii DecimalString.
From Buri Require Import Wire NativeValidation EncoderFrontend.
Import ListNotations.
Open Scope string_scope.
Module Native.
Inductive value :=
 | Nil | Symbol (s : string) | Text (s : string) | Integer (z : Z)
 | Fraction (n : Z) (d : positive) | Inexact (token : Z)
 | Boolean (b : bool) | Pair (a b : value) | Character (c : ascii)
 | Handle (id : nat).
Fixpoint same a b := match a,b with
 | Nil,Nil => true
 | Symbol s,Symbol t | Text s,Text t => String.eqb s t
 | Integer n,Integer m | Inexact n,Inexact m => Z.eqb n m
 | Fraction n d,Fraction m e => Z.eqb (n * Z.pos e) (m * Z.pos d)
 | Boolean x,Boolean y => Bool.eqb x y
 | Pair a b,Pair c d => same a c && same b d
 | Character c,Character d => Ascii.eqb c d
 | Handle n,Handle m => Nat.eqb n m
 | _,_ => false end.
Definition L := fold_right Pair Nil.
Fixpoint elements v := match v with
 | Nil => Some []
 | Pair h t => match elements t with Some xs => Some (h::xs) | _ => None end
 | _ => None end.
Fixpoint names vs := match vs with
 | [] => Some []
 | Symbol s::vs => match names vs with Some ss => Some (s::ss) | _ => None end
 | _ => None end.
Definition spelling z := NilZero.string_of_int (Z.to_int z).
Definition numeric v := match v with Integer _ | Fraction _ _ | Inexact _ => true | _ => false end.
Definition integral v := match v with
 | Integer _ | Inexact _ => true
 | Fraction n d => Z.eqb (Z.rem n (Z.pos d)) 0
 | _ => false end.
Definition exact v := match v with Integer _ | Fraction _ _ => true | _ => false end.
Definition ratio n d := match d with
 | Zpos p => if Z.eqb (Z.rem n d) 0 then Some (Integer (Z.quot n d)) else Some (Fraction n p)
 | _ => None end.
Definition primitive op args : option value := match op,args with
 | "cons",[a;b] => Some (Pair a b)
 | "list",xs => Some (L xs)
 | "car",[Pair a _] => Some a
 | "cdr",[Pair _ b] => Some b
 | "pair?",[x] => Some (Boolean (match x with Pair _ _ => true | _ => false end))
 | "null?",[x] => Some (Boolean (match x with Nil => true | _ => false end))
 | "eq?",[Symbol s;Symbol t] => Some (Boolean (String.eqb s t))
 | "eq?",[Symbol _;_] | "eq?",[_;Symbol _] => Some (Boolean false)
 | "eqv?",[Integer n;Integer m] => Some (Boolean (Z.eqb n m))
 | "equal?",[a;b] => Some (Boolean (same a b))
 | "number?",[x] => Some (Boolean (numeric x))
 | "integer?",[x] => Some (Boolean (integral x))
 | "exact?",[x] => Some (Boolean (exact x))
 | "boolean?",[x] => Some (Boolean (match x with Boolean _ => true | _ => false end))
 | "string?",[x] => Some (Boolean (match x with Text _ => true | _ => false end))
 | "symbol?",[x] => Some (Boolean (match x with Symbol _ => true | _ => false end))
 | "symbol->string",[Symbol s] => Some (Text s)
 | "number->string",[Integer z;Integer 10] => Some (Text (spelling z))
 | "/",[Integer x;Integer y] => ratio x y
 | "floor",[Integer z] => Some (Integer z)
 | "floor",[Fraction n d] => Some (Integer (Z.div n (Z.pos d)))
 | "+",[Integer x;Integer y] => Some (Integer (x+y))
 | "-",[Integer x;Integer y] => Some (Integer (x-y))
 | "*",[Integer x;Integer y] => Some (Integer (x*y))
 | ">=",[Integer x;Integer y] => Some (Boolean (Z.geb x y))
 | "<",[Integer x;Integer y] => Some (Boolean (Z.ltb x y))
 | "string-append",[Text a;Text b] => Some (Text (a++b))
 | "string-length",[Text s] => Some (Integer (Z.of_nat (String.length s)))
 | "string-ref",[Text s;Integer z] =>
   if Z.leb 0 z then match String.get (Z.to_nat z) s with Some c => Some (Character c) | _ => None end else None
 | "string",[Character c] => Some (Text (String c EmptyString))
 | "char->integer",[Character c] => Some (Integer (Z.of_nat (nat_of_ascii c)))
 | "substring",[Text s;Integer a;Integer b] =>
   if (Z.leb 0 a && Z.leb a b && Z.leb b (Z.of_nat (String.length s)))%bool
   then Some (Text (substring (Z.to_nat a) (Z.to_nat (b-a)) s)) else None
 | _,_ => None end.
Inductive expr := Lit (v : value) | Var (s : string) | If (c a b : expr)
 | Let (s : string) (a b : expr) | And (a b : expr) | Or (a b : expr)
 | Call (s : string) (args : list expr).
Record definition := Def { params : list string; body : expr }.
Definition program := string -> option definition.
Definition env := string -> option value.
Definition bind (rho : env) s v := fun t => if String.eqb t s then Some v else rho t.
Fixpoint arguments ps vs : env := match ps,vs with
 | p::ps,v::vs => bind (arguments ps vs) p v | _,_ => fun _ => None end.
Fixpoint decode fuel v := match fuel with
 | O => None
 | S n =>
   let many := fix many xs := match xs with
    | [] => Some [] | x::xs => match decode n x,many xs with Some e,Some es => Some (e::es) | _,_ => None end end in
   match v with
   | Text _ | Integer _ | Boolean _ => Some (Lit v)
   | Symbol s => Some (Var s)
   | _ => match elements v with
     | Some [Symbol "quote";x] => Some (Lit x)
     | Some [Symbol "if";c;a;b] => match decode n c,decode n a,decode n b with
       | Some c,Some a,Some b => Some (If c a b) | _,_,_ => None end
     | Some [Symbol "let";bs;b] => match elements bs with
       | Some [binding] => match elements binding,decode n b with
         | Some [Symbol s;a],Some b => match decode n a with Some a => Some (Let s a b) | _ => None end
         | _,_ => None end
       | _ => None end
     | Some [Symbol "let*";bs;b] => match elements bs,decode n b with
       | Some xs,Some body =>
         (fix bindings xs := match xs with
           | [] => Some body
           | x::xs => match elements x,bindings xs with
             | Some [Symbol s;a],Some b => match decode n a with Some a => Some (Let s a b) | _ => None end
             | _,_ => None end end) xs
       | _,_ => None end
     | Some (Symbol "cond"::clauses) =>
       (fix cases cs := match cs with
         | [] => None
         | c::cs => match elements c with
           | Some [Boolean true;b] => match cs with [] => decode n b | _ => None end
           | Some [c;b] => match decode n c,decode n b,cases cs with
             | Some c,Some b,Some rest => Some (If c b rest) | _,_,_ => None end
           | _ => None end end) clauses
     | Some (Symbol "and"::xs) => match many xs with
       | Some es => Some (match (fold_right (fun a tail => Some (match tail with
         | None => a | Some b => And a b end)) None es) with
         | Some e => e | None => Lit (Boolean true) end) | _ => None end
     | Some (Symbol "or"::xs) => match many xs with
       | Some es => Some (fold_right Or (Lit (Boolean false)) es) | _ => None end
     | Some (Symbol s::xs) => match many xs with Some es => Some (Call s es) | _ => None end
     | _ => None end end end.
Inductive result := Returned (v : value) | Raised (owner message : value) | Exhausted | Unsupported.
(* Shared dispatch preserves the exact primitive/error contract in both engines. *)
Definition external op vs := match op,vs with
 | "error",[owner;message] => Raised owner message
 | _,_ => match primitive op vs with Some v => Returned v | _ => Unsupported end end.
Inductive arguments_result := Values (vs : list value) | ArgumentFailure (r : result).
Fixpoint eval fuel (p : program) (rho : env) e : result := match fuel with
 | O => Exhausted
 | S n =>
   let many := fix many es := match es with
     | [] => Values []
     | e::es => match eval n p rho e with
       | Returned v => match many es with Values vs => Values (v::vs) | ArgumentFailure r => ArgumentFailure r end
       | r => ArgumentFailure r end end in
   match e with
   | Lit v => Returned v
   | Var s => match rho s with Some v => Returned v | _ => Unsupported end
   | If c a b => match eval n p rho c with
     | Returned (Boolean false) => eval n p rho b
     | Returned _ => eval n p rho a
     | other => other end
   | Let s a b => match eval n p rho a with Returned v => eval n p (bind rho s v) b | other => other end
   | And a b => match eval n p rho a with
     | Returned (Boolean false) => Returned (Boolean false)
     | Returned _ => eval n p rho b | other => other end
   | Or a b => match eval n p rho a with
     | Returned (Boolean false) => eval n p rho b
     | Returned v => Returned v | other => other end
   | Call s es => match many es with
     | Values vs => match p s with
       | Some d => if Nat.eqb (List.length (params d)) (List.length vs)
         then eval n p (arguments (params d) vs) (body d) else Unsupported
       | None => external s vs end
     | ArgumentFailure r => r end
   end end.
(* Typed transport; unlike the earlier syntax tree, native booleans cannot be
   confused with symbols. Runtime fractions/characters/handles are not syntax. *)
Fixpoint untag fuel d := match fuel with
 | O => None
 | S n => match d with
   | Wire.Cons (Wire.Atom false "nil") Wire.Nil => Some Nil
   | Wire.Cons (Wire.Atom false "sym") (Wire.Cons (Wire.Atom false s) Wire.Nil) => Some (Symbol s)
   | Wire.Cons (Wire.Atom false "text") (Wire.Cons bytes Wire.Nil) =>
     match EncoderFrontend.byte_string bytes with Some s => Some (Text s) | _ => None end
   | Wire.Cons (Wire.Atom false "num") (Wire.Cons (Wire.Atom true s) Wire.Nil) =>
     match NativeValidation.integer s with Some z => Some (Integer z) | _ => None end
   | Wire.Cons (Wire.Atom false "bool") (Wire.Cons (Wire.Atom true "0") Wire.Nil) => Some (Boolean false)
   | Wire.Cons (Wire.Atom false "bool") (Wire.Cons (Wire.Atom true "1") Wire.Nil) => Some (Boolean true)
   | Wire.Cons (Wire.Atom false "pair") (Wire.Cons a (Wire.Cons b Wire.Nil)) =>
     match untag n a,untag n b with Some a,Some b => Some (Pair a b) | _,_ => None end
   | _ => None end end.
Definition decode_definition fuel d := match elements d with
 | Some [Symbol "define";Pair (Symbol name) args;b] => match elements args,decode fuel b with
   | Some ps,Some e => match names ps with Some ps => Some (name,Def ps e) | _ => None end
   | _,_ => None end | _ => None end.
Fixpoint definitions fuel xs := match xs with
 | [] => Some []
 | x::xs => match decode_definition fuel x,definitions fuel xs with
   | Some d,Some ds => Some (d::ds) | _,_ => None end end.
Fixpoint lookup (ds : list (string * definition)) name := match ds with
 | [] => None | (s,d)::ds => if String.eqb name s then Some d else lookup ds name end.
Definition run fuel ds name args := match lookup ds name with
 | Some d => if Nat.eqb (List.length (params d)) (List.length args)
   then eval fuel (lookup ds) (arguments (params d) args) (body d) else Unsupported
 | _ => Unsupported end.
End Native.
