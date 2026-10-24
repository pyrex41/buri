(* Independent, rejecting reader for the closed source profile used by the
   encoder. No comments, escapes, improper lists, reader macros or eval. This
   validates this source artifact; it is not a proof of Shen's native reader. *)
From Coq Require Import List String Ascii Bool.
From Buri Require Import EncoderFrontend EncoderSource Encoder.
Import ListNotations.
Module SourceReader.
Module F := EncoderFrontend.EncoderFrontend.
Open Scope string_scope.
Inductive token := Open | Close | Square | EndSquare | Atom (s:string) | Quoted (s:string).
Definition space c := orb (Ascii.eqb c " "%char)
 (orb (Ascii.eqb c (ascii_of_nat 10)) (orb (Ascii.eqb c (ascii_of_nat 13)) (Ascii.eqb c (ascii_of_nat 9)))).
Definition delimiter c := orb (space c)
 (orb (Ascii.eqb c "("%char) (orb (Ascii.eqb c ")"%char)
 (orb (Ascii.eqb c "["%char) (orb (Ascii.eqb c "]"%char) (Ascii.eqb c (ascii_of_nat 34)))))).
Fixpoint word s := match s with
 | EmptyString => (EmptyString,EmptyString)
 | String c rest => if delimiter c then (EmptyString,s)
   else let '(a,b) := word rest in (String c a,b) end.
Fixpoint quoted s := match s with
 | EmptyString => None
 | String c rest => if Ascii.eqb c (ascii_of_nat 34) then Some (EmptyString,rest)
   else match quoted rest with Some (a,b) => Some (String c a,b) | _ => None end end.
Fixpoint lex fuel s := match fuel with
 | O => None
 | S n => match s with
   | EmptyString => Some []
   | String c rest => if space c then lex n rest
     else if Ascii.eqb c "("%char then option_map (cons Open) (lex n rest)
     else if Ascii.eqb c ")"%char then option_map (cons Close) (lex n rest)
     else if Ascii.eqb c "["%char then option_map (cons Square) (lex n rest)
     else if Ascii.eqb c "]"%char then option_map (cons EndSquare) (lex n rest)
     else if Ascii.eqb c (ascii_of_nat 34) then match quoted rest with
       | Some (a,b) => option_map (cons (Quoted a)) (lex n b) | _ => None end
     else let '(a,b) := word s in match a with
       | EmptyString => None | _ => option_map (cons (Atom a)) (lex n b) end
   end end.
Definition atom s := match F.small_nat s with Some n => F.Num n | _ => F.Sym s end.
Fixpoint one fuel ts := match fuel with
 | O => None
 | S n => match ts with
   | Atom s::rest => Some (atom s,rest)
   | Quoted s::rest => Some (F.TextNode s,rest)
   | Open::rest => group n false rest
   | Square::rest => group n true rest
   | _ => None end end
with group fuel square ts := match fuel with
 | O => None
 | S n => match ts with
   | Close::rest => if square then None else Some (F.Nil,rest)
   | EndSquare::rest => if square then Some (F.Nil,rest) else None
   | _ => match one n ts with
     | Some (a,rest) => match group n square rest with
       | Some (b,rest') => Some (F.Pair a b,rest') | _ => None end
     | _ => None end end end.
Fixpoint all fuel ts := match ts with
 | [] => Some []
 | _ => match fuel with O => None | S n => match one n ts with
   | Some (a,rest) => option_map (cons a) (all n rest) | _ => None end end end.
Definition read s := match lex (S (String.length s)) s with
 | Some ts => all (S (List.length ts)) ts | _ => None end.
(* Source bodies use the same explicit admitted primitive contracts as Encoder.
   This syntax is built structurally, without invoking the source renderer. *)
Definition list := fold_right F.Pair F.Nil.
Definition app name xs := list (F.Sym name::xs).
Definition unary name x := app name [x].
Definition binary name x y := app name [x;y].
Definition unused := F.Num 0.
Fixpoint syntax names e := match e with
 | Encoder.Lit (Encoder.Text s) => F.TextNode s
 | Encoder.Lit (Encoder.Number n) => F.Num n
 | Encoder.Lit _ => F.Sym "unsupported-literal"
 | Encoder.Fail s => unary "simple-error" (F.TextNode s)
 | Encoder.Var i => F.Sym (nth i names "unbound")
 | Encoder.If c a b => app "if" [syntax names c;syntax names a;syntax names b]
 | Encoder.Let a b => app "let" [F.Sym "Local";syntax names a;syntax ("Local"::names) b]
 | Encoder.Call f a b => app (Encoder.function_name f)
     (match f with Encoder.Byte => [syntax names a;syntax names b] | _ => [syntax names a] end)
 | Encoder.Op op a b => let a:=syntax names a in let b:=syntax names b in
   match op with
   | Encoder.Cat => binary "cn" a b
   | Encoder.Zero => binary "=" a (F.Num 0)
   | Encoder.Half => unary "floor" (binary "/" a (F.Num 2))
   | Encoder.Even => binary "=" a (binary "*" b (F.Num 2))
   | Encoder.Prev => binary "-" a (F.Num 1)
   | Encoder.Empty => binary "=" a (F.TextNode "")
   | Encoder.Code => unary "string->n" (binary "pos" a (F.Num 0))
   | Encoder.Tail => unary "tlstr" a
   | Encoder.ByteRange => binary "and" (binary ">=" a (F.Num 0)) (binary "<" a (F.Num 256))
   | Encoder.IsNil => binary "=" a F.Nil
   | Encoder.IsPair => unary "cons?" a
   | Encoder.Head => unary "hd" a
   | Encoder.Rest => unary "tl" a
   | Encoder.IsNumber => unary "buri.exact-integer?" a
   | Encoder.IsSymbol => unary "symbol?" a
   | Encoder.Spelling => unary "str" a end end.
Definition definition f := app "define"
 (F.Sym (Encoder.function_name f)::map F.Sym (Encoder.parameters f) ++
   [F.Sym "->";syntax (Encoder.parameters f) (Encoder.body f)])%list.
Definition forms := [app "tc" [F.Sym "-"];definition Encoder.Byte;
 definition Encoder.Str;definition Encoder.Datum].
Theorem encoder_source_parsed : read encoder_source_text = Some forms.
Proof. vm_compute. reflexivity. Qed.
Example unterminated_string : read """abc" = None.
Proof. reflexivity. Qed.
Example unmatched_list : read "(abc" = None.
Proof. reflexivity. Qed.
Example crossed_delimiters : read "([)]" = None.
Proof. reflexivity. Qed.
Example extra_closer : read "(abc))" = None.
Proof. reflexivity. Qed.
End SourceReader.
