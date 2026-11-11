(* Shen/JIT Phase 2, D00: what the store D of the front-end rules contains, and which store facts
   the front rules (inline, thaw, protect, do, bind!, constant folding) may use.

   DECISION: (A), a LOWERED store. For a definition, D lists (F, FUser ps e_F) for the callees its
   rewrites rely on, where e_F = JitNorm.erase ps n_F is the erased normal form that stage 0's
   lowerer produced for F (the .norm witness). D_compiled' (below) is then the per-definition EMIT
   check on each callee: F's own stage 0 code object against e_F, which is what the src-free emit
   judge (JitNormStage0.judge_core) already decides. F's own front links are NOT needed for the
   caller's theorem.

   Why (A). Com's FunRel (JitLowerStep) makes the body a store holds for F the body F's code is
   CompFn-related to, and StoreHas D makes D's body for F the store's. So D_compiled (JitKRef) asks
   check_fn of F's real stage 0 code against D's body. That code is the lowering of the INLINED
   normal form, not of F's source body, for every definition with an inlining marker (528 of 955).
   The src judge rejects all 528 (T02: "no accepted definition carries a marker"), so under (B) no
   callee with front rewrites can ever meet D_compiled against the stage 0 machine. Under (A) the
   check is the emit judge on e_F, which Comp extensions can meet (T02 `emit` column: 133 today, 573
   at baseline A31, 953 at B35; T02's text forecasts 955 with every option taken).

   What (A) costs. The claim is about running in the store of lowered bodies. That is already
   what call_preservation_src_statement's "Does NOT say" records ("Under Com's FunRel every
   function s defines is accepted code, so the callees b0 calls are the LOWERED bodies"); (A) adds
   no new gap, it names the one that is there. And the inline rule can no longer compare the
   inlined body with the callee's SOURCE body (lower.shen inlines `(shen-jit.inline-body F)`, F's
   source body, normalised again in the caller): it must relate the inlined normal body N to e_F,
   another normal form of the same source. F's own norm link (KRef ps b_F e_F) does not give that
   without transitivity and the reverse refinement, neither of which KRef has. So the inline fact
   is a syntactic relation of N to e_F: `inl_site` below, alpha-equivalence plus three named
   extensions, each matching one lower.shen mechanism.

   Census (Python, NOT proof; tests run by D00 on the T02 capture, norm witness set sha256
   e45add983f619559649a087a3c8a2c9e4f1fd3061be5d95996d33449a1b69dd1 in C order, script
   spikes/pass-split/d00_inline_census.py sha256
   5384700da7e3fc1caf47e3a4c9d94d0b8246ec395e81146697466ada50efff90, per-definition classes in
   spikes/pass-split/d00_inline_sites.tsv sha256
   f6306ddedd6c3b697c7c05bbf1e53e1b9be595b597130638f8c2450bd5531243).
   Every inlining marker (let stage0.lower.inlining (const F) N) in the 955 witnesses, compared
   with F's own witness body:
     5430 inline sites, 181 distinct callees, 528 definitions with a marker:
     - 5360 alpha-equivalent (marker included; up to renaming of bound names);
     -   30 integer-literal substitution (inline-numbers): 24 plain, 6 also folding + (callee
            `vector`), so they need fold-arith's store fact (interface item 2 below);
     -   22 thaw-with (inline-frozen), callee `when`;
     -   18 depth cut: N calls G where e_F inlines G (inline depth limit 2), callees
            `shen.locked?`/`shen.unlock`, so D must also hold G;
     - 0 unexplained. share never made a difference (inline bodies have no share chain).
   Per definition (all sites of the definition covered), cumulatively:
     alpha 915, + integer substitution without folding 939, + folding 945, + thaw-with 946,
     + depth cut 955 (of 955).

   T02's forecasts (spikes/pass-split/FEATURES.md, verbatim, census): rows direct/D-src/D-low/D-inl
     row 0 (current Comp)          111 / 46 / 46 / 111
     A31 (baseline, all families)  564 / 235 / 235 / 564
     B35 (every decision item)     953 / 500 / 500 / 953
   T02's D-src assumes each callee validates THROUGH the front end; (B)'s FunRel forbids that (a
   source body in the store needs code CompFn-related to the source body itself), so D-src
   overstates (B). The faithful (B) number, D00 census at the end state (every feature and family
   admitted): about 725 of 955 definitions have a marker closure whose callees need no front family
   (45 of the 181 inlined callees need one: inline 41, fold-cons 5, cond 2, thaw-sugar 2; approximate,
   since a callee whose only rewrite is fold-cons erases back to its source and could count); under
   (A) the same end state predicts 955 (T02's every-option forecast, given the inline relation's
   four classes; with alpha alone, 915).
   These are predictions. Progress is unchanged: 111 of 955 stage 0 definitions validated (src).

   ALLOWED STORE FACTS (each a named Definition below; nothing else about the store may be used by
   a front-end rule's soundness proof):
   - D_has_inline_callee D F ps e_F : F's lowered body is in D (inline rule, and the depth-cut
     callee G). Stated over D, so it is a StoreHas consequence in every SRel store.
   - D_has_kernel_thaw, D_has_kernel_protect, D_has_kernel_do : the kernel's sys.kl bodies, which
     erase to their source bodies (EApp (EVar v) [], EVar v, EVar v2), so (A) and (B) agree on them.
     thaw's own D_compiled' needs apply-dynamic, which Comp does not admit today (see D_COMPILED'
     TODAY below).
   - D_cons_prim s : cons resolves to the primitive. NOT a D entry: (cons, FPrim PCons) in D would
     break D_wf (cons is not sealed). The front rule fold-cons needs no store fact, since a folded
     pair erases back to the cons chain (JitNorm.erase_not_injective_fold); the emit rule gets
     D_cons_prim from Com's fr_name (D_cons_prim_of_Com, proved).
   - D_prims_fold D : (+, FPrim PAdd) and (-, FPrim PSub) in D, for fold-arith and for the 6
     folding inline sites. Interface item 2.
   - D_has_bind D : shen.bind!'s lowered body e_B. The bind rule (bound-now) binds fresh names
     directly to X, Y and B (no parameter lets) and puts E where e_B thaws its fourth parameter:
     `bind_site` runs inl_eq on e_B with the renaming seeded by bind!'s first three parameters
     paired with those fresh names, SFrozen E for the fourth, and letdo for the kernel's unused
     `let` (so it also needs D_has_kernel_do). bound-now does not copy e_B: it normalises its own
     template, (do (shen.bindv a1 a2 a3) (let r E (if (= r false) (shen.unwind a1 a3 r) r))), so
     the inline rule inlines bindv and unwind in it, exactly as norm inlined them in bind!'s own
     source body to give e_B; neither side has a call to shen.bindv or shen.unwind (Example
     bind_real_inlined), and inl_eq relates the two inlined regions by congruence and renaming.
     Test on real data (NOT proof; Rocq vm_compute of bind_report over the decoded table, witness
     set e45add98..., the --D smoke data): 37 of 37 bound-now sites, in 6 definitions
     (shen.system-S-h 18, shen.primitive 3, shen.l-rules 1, shen.myassume 6, shen.p-hyps 6,
     shen.variancy-signature 3), are accepted by bind_site (fold = false) against their D_of store.
     The 37 match the (const shen.bindv) markers in those 6 definitions, 18+3+1+6+6+3, so the
     extractor missed none; 25 sites have a literal (freeze E) and 12 come from let-frozen. The
     site's arguments are read back from the expansion (bind_args), so what is tested is N against
     e_B, not the normalisation of the arguments. Example site_bind_real pins one (shen.l-rules).
   - D_has_port_deref_eq, D_has_port_unify : shen-jit.deref=, shen-jit.unify=, shen-jit.unify=! (port
     KL defuns, src/port/shen-jit.kl, stage 0's shen-jit.forms). These rules replace kernel
     functions (= on shen.deref, is/is!) by DIFFERENT port functions; their soundness is a semantic
     equivalence with a real proof (deref='s same? shortcut answers true on two identical NaN cells
     where = answers false), not a store shape and not alpha. T02 counts 0 firings of cut-deref.
     D_of puts them in a definition's D exactly when its normal form calls one of them by name
     (port_used: deref= alone; unify= and unify=! together, since D_has_port_unify asks both), so
     D_has_port_* is reachable for a D built by D_of. Their D_compiled' is false today (below).
   - D_has_port_bindv, D_has_port_unwind : shen.bindv and shen.unwind (port defuns, arity 3, stage
     0 rows). They are ordinary inline callees: the facts are D_has_inline_callee for F = shen.bindv
     and F = shen.unwind, named because they are the port defuns bind! relies on. D_of DOES add
     them, through the marker closure (mclose), wherever a marker names them: every bound-now site
     carries one marker for each (its template's calls were inlined), shen.overbind,
     shen-jit.unify= and shen-jit.unify=! inline bindv directly, and shen-jit.undo inlines unwind.
     D_holders on the real table (test, Rocq vm_compute): bindv is in the D of 10 definitions
     (shen.bind!, shen.overbind, shen-jit.unify=, shen-jit.unify=! and the 6 with bound-now sites);
     unwind in the D of 8 (shen.bind!, shen-jit.undo and the same 6). shen.bind! is in the D of
     exactly those 6 (unchanged by the let-frozen shape added to kernel_used).
     Which checker owns which marker: inside a bound-now expansion the bindv and unwind regions are
     bind_site's (matched against e_B's own inlined regions, using no fact about either callee);
     F-inline must not count them again as inline sites. Elsewhere
     they are inline sites (shen.overbind, the unify forms, shen-jit.undo, and bind!'s own body),
     checked by inl_site with D_has_inline_callee.
   - Consequences for a D built by D_of (stated so review sees them): D_prims_fold NEVER holds of
     it, since + and - are primitives with no stage 0 row (interface item 2), so the fold-enabled
     inline sites (fold = true) and fold-arith cannot use a D_of store until item 2 is settled;
     D_cons_prim is about the store, not D, and holds under Com.
   - D_COMPILED' TODAY (test, NOT proof: Rocq vm_compute of D_compiled' on single-entry Ds built by
     D_low from the decoded table, against the table's code objects, witness set e45add98...):
     true for do and protect; FALSE for thaw (apply-dynamic, see above), shen-jit.deref=,
     shen-jit.unify=, shen-jit.unify=!, shen.bind!, shen.bindv and shen.unwind (reasons not
     diagnosed here). So every D_of store holding any of those fails D_compiled' at this commit:
     the 6 definitions with bound-now sites, the 10 holding bindv, the 8 holding unwind, and every D holding
     thaw or a port defun. Making them pass is Comp's work (the emit families), not D's.

   INTERFACE ITEMS (1, 2; not changed here, JitKRef.v is the KRef track's interface) AND A NOTE (3):
   1. fresh names. JitKRef.fresh_ok ns (b0 :: D_bodies D) is FALSE under (A): lowered bodies bind
      stage0.lower.argN (Example fresh_ok_lowered_fails below). The premise the front rules use is
      fresh_front: b0 plus the callees' SOURCE bodies (inlining brings their names in, as source).
      The D_bodies form of the premise is not that premise; whoever states the final theorem must
      take fresh_front (or b0 alone, if alpha makes callee names irrelevant).
   2. prims in D. D_wf asks every D name to be in `sealed`; stage 0's sealed list is the 955
      names it defines, which has no primitive. D_prims_fold therefore needs `sealed` to also list
      + and - (jit_rules' defun refusal is unchanged by that, as is_fixed_name already refuses
      them, but only pointwise), or SRel to carry a primitive-resolution invariant.
   3. Depth cut runs the call on the target side and the inlined region on the source side, so its
      soundness uses aeq_sound_statement with the region's body as e0 and e_G as e (inl_eq checks
      the body scoped in G's parameters), and the call in the store, which D_has_inline_callee
      gives for G.

   Stated, NOT proved here (owner F-inline): aeq_sound_statement, inline_site_sound_statement,
   bind_site_sound_statement. inl_site was NOT run on real inline sites (only the Examples); the
   Python census above classifies them, Rocq has not checked them (UNKNOWN).
   Proved here: D_compiled'_spec, D_compiled'_D_compiled, D_cons_prim_of_Com, dedup_nodup,
   D_of_nodup, D_of_wf; and Examples pinning the checkers (tests, not evidence of anything general).
   No axioms, nothing Admitted. *)
From Coq Require Import List ZArith NArith PArith Bool String.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLPort JitBytecode JitLowerRel JitLowerStep JitLowerCheck JitKRef JitLowerStage0 JitNorm JitNormStage0.
Import ListNotations.
Module JitFrontD.
Import KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics.
Import JitLowerRel.JitLowerRel JitLowerCheck.JitLowerCheck JitLowerStage0.JitLowerStage0 JitNorm.JitNorm JitNormStage0.JitNormStage0.
Module B := JitBytecode.JitBytecode.
Module K := JitKRef.JitKRef.

(* ======================= the table: decoded stage 0 data ======================= *)
(* One stage 0 definition: its form (source body), lower.shen's normal form (the .norm witness),
   that normal form erased (the lowered body), and its code object. The trees come from the
   trusted tokenizer (tests/shen-jit/stage0_to_rocq.py --D, OB-JIT-LOWER-READER); everything else
   is decided here, as JitNormStage0.judge_core decodes. *)
Record row := Row { r_name : name; r_params : list name; r_src : expr; r_nf : nexpr; r_low : expr; r_code : B.code }.

Definition decode_row (form norm sbc : sx) : option row :=
 match parse [] (to_value form), to_val sbc with
 | Some (EDefun f ps b), B.VPair (B.VSym _) (B.VPair (B.VSym g) (B.VPair code B.VNil)) =>
   if negb (Pos.eqb (B.sym_of_text f) g) then None else
   match decode_entry norm with
   | Some (f', ps', n) =>
     if negb (text_eqb f f' && names_eqb ps ps') then None else
     match erase ps n, B.build_code B.prim_tree 64 code with
     | Some e, B.LOk c => Some (Row f ps b n e c)
     | _, _ => None end
   | None => None end
 | _, _ => None end.

(* The rows that decode; None when the three lists differ in length. A row that does not decode is
   left out, so a definition that needs it gets no D (D_of is None). *)
Fixpoint rows_of (fs ns ss : list sx) : option (list row) := match fs, ns, ss with
 | [], [], [] => Some []
 | f :: fs, n :: ns, s :: ss => match rows_of fs ns ss with
   | Some rs => Some (match decode_row f n s with Some r => r :: rs | None => rs end)
   | None => None end
 | _, _, _ => None end.

Definition find_row (rows : list row) (f : name) : option row := find (fun r => text_eqb (r_name r) f) rows.
Definition codes (rows : list row) : list (name * B.code) := map (fun r => (r_name r, r_code r)) rows.

(* ---------- which names a definition's D holds ---------- *)
(* The callees named by inlining markers, at any depth. *)
Fixpoint markers (n : nexpr) : list name :=
 let all := fix all (l : list nexpr) : list name := match l with
   | [] => [] | a :: l => markers a ++ all l end in
 match n with
 | NConst _ | NVar _ => []
 | NLet x v b => (if is_marker_name x then match v with NConst (VSym f) => [f] | _ => [] end else [])
                 ++ markers v ++ markers b
 | NIf c a b => markers c ++ markers a ++ markers b
 | NAnd a b | NOr a b | NDo a b | NApply1 a b | NTrap a _ b => markers a ++ markers b
 | NLambda _ b | NFreeze b | NApply0 b => markers b
 | NPrim _ l | NCall _ l => all l end.

(* Names a source body calls. (thaw X), (protect X), (do X Y) and (shen.bind! ...) are named
   calls in KLSemantics.parse. *)
Fixpoint calls (e : expr) : list name := match e with
 | ECall f args => f :: (fix go (l : list expr) : list name := match l with
     | [] => [] | a :: l => calls a ++ go l end) args
 | ELam _ b | EFreeze b | EType b | EDefun _ _ b => calls b
 | ELet _ a b | EAnd a b | EOr a b | ETrap a b => calls a ++ calls b
 | EIf c a b => calls c ++ calls a ++ calls b
 | ECond cl => (fix go (l : list (expr * expr)) : list name := match l with
     | [] => [] | (c, b) :: l => calls c ++ calls b ++ go l end) cl
 | EApp h args => calls h ++ (fix go (l : list expr) : list name := match l with
     | [] => [] | a :: l => calls a ++ go l end) args
 | _ => [] end.

Definition thaw_name : name := kw "thaw".
Definition protect_name : name := kw "protect".
Definition bind_name : name := kw "shen.bind!".
Definition plus_name : name := kw "+".
Definition minus_name : name := kw "-".
Definition deref_eq_name : name := kw "shen-jit.deref=".
Definition unify_name : name := kw "shen-jit.unify=".
Definition unify_bang_name : name := kw "shen-jit.unify=!".
Definition bindv_name : name := kw "shen.bindv".
Definition unwind_name : name := kw "shen.unwind".
Definition kernel_names : list name := [do_name; thaw_name; protect_name].

(* Whether some subterm satisfies P. *)
Fixpoint ex_sub (P : expr -> bool) (e : expr) : bool :=
 P e || match e with
 | ECall _ args => (fix go (l : list expr) : bool := match l with
     | [] => false | a :: l => ex_sub P a || go l end) args
 | ELam _ b | EFreeze b | EType b | EDefun _ _ b => ex_sub P b
 | ELet _ a b | EAnd a b | EOr a b | ETrap a b => ex_sub P a || ex_sub P b
 | EIf c a b => ex_sub P c || ex_sub P a || ex_sub P b
 | ECond cl => (fix go (l : list (expr * expr)) : bool := match l with
     | [] => false | (c, b) :: l => ex_sub P c || ex_sub P b || go l end) cl
 | EApp h args => ex_sub P h || (fix go (l : list expr) : bool := match l with
     | [] => false | a :: l => ex_sub P a || go l end) args
 | _ => false end.

(* The two shapes bound-now rewrites (lower.shen): (shen.bind! X Y B (freeze E)) directly, and
   (let G (freeze E) Body) with (shen.bind! X Y B G) in Body, through let-frozen/frozen-in (which
   fires only under a size and use-count condition, so this over-approximates it). On stage 0, 25 of
   the 37 bound-now sites are the first shape and 12 the second; each of the 6 definitions with a
   site also has the first, so the second only matters for completeness. Any other (shen.bind! ...)
   call (bind's, with a variable last argument) brings no shen.bind! into D. *)
Definition frozen_bind (e : expr) : bool := match e with
 | ECall f [_; _; _; EFreeze _] => text_eqb f bind_name | _ => false end.
Definition bind_on_var (x : name) (e : expr) : bool := match e with
 | ECall f [_; _; _; EVar y] => text_eqb f bind_name && text_eqb x y | _ => false end.
Definition let_frozen_bind (e : expr) : bool := match e with
 | ELet x (EFreeze _) b => ex_sub (bind_on_var x) b | _ => false end.

(* thaw, protect and do are rewritten wherever called; shen.bind! only in a bound-now shape. *)
Definition kernel_used (b : expr) : list name :=
 filter (fun k => existsb (text_eqb k) (calls b)) kernel_names ++
 (if ex_sub (fun e => frozen_bind e || let_frozen_bind e) b then [bind_name] else []).

(* Whether a normal form has a do node: from the source, from an inlined callee's body (shen.unwind's
   (do ...)) or from bound-now. The emit rule for do and inl_eq's letdo case need the kernel's do. *)
Fixpoint has_do (n : nexpr) : bool :=
 let all := fix all (l : list nexpr) : bool := match l with
   | [] => false | a :: l => has_do a || all l end in
 match n with
 | NConst _ | NVar _ => false
 | NDo _ _ => true
 | NIf c a b => has_do c || has_do a || has_do b
 | NAnd a b | NOr a b | NApply1 a b | NLet _ a b | NTrap a _ b => has_do a || has_do b
 | NLambda _ b | NFreeze b | NApply0 b => has_do b
 | NPrim _ l | NCall _ l => all l end.

(* The transitive closure of marker edges through the table: the callees inlined, the callees
   inlined into those (which is where a depth-cut callee is), and so on. `fuel` bounds the work;
   if it ran out the closure would be smaller and the inline checker would reject, never accept
   more. *)
Fixpoint mclose (fuel : nat) (rows : list row) (todo acc : list name) : list name :=
 match fuel with O => acc | S fuel => match todo with
 | [] => acc
 | f :: todo => if existsb (text_eqb f) acc then mclose fuel rows todo acc
   else mclose fuel rows (todo ++ match find_row rows f with Some r => markers (r_nf r) | None => [] end) (acc ++ [f])
 end end.
Definition mfuel (rows : list row) (todo : list name) : nat :=
 S (List.length todo + fold_left (fun a r => a + S (List.length (markers (r_nf r)))) rows 0).

Fixpoint dedup (l : list name) : list name := match l with
 | [] => [] | x :: l => x :: filter (fun y => negb (text_eqb x y)) (dedup l) end.

(* Whether a normal form calls a name satisfying p (a named call, NCall). *)
Fixpoint has_ncall (p : name -> bool) (n : nexpr) : bool :=
 let all := fix all (l : list nexpr) : bool := match l with
   | [] => false | a :: l => has_ncall p a || all l end in
 match n with
 | NConst _ | NVar _ => false
 | NCall f l => p f || all l
 | NPrim _ l => all l
 | NIf c a b => has_ncall p c || has_ncall p a || has_ncall p b
 | NAnd a b | NOr a b | NDo a b | NApply1 a b | NLet _ a b | NTrap a _ b => has_ncall p a || has_ncall p b
 | NLambda _ b | NFreeze b | NApply0 b => has_ncall p b end.

(* The port defuns the port rules (cut-deref, unified-now) introduce, when the normal form calls
   them: their facts are D_has_port_deref_eq and D_has_port_unify, which asks for both unify forms. *)
Definition port_used (n : nexpr) : list name :=
 (if has_ncall (text_eqb deref_eq_name) n then [deref_eq_name] else []) ++
 (if has_ncall (fun f => text_eqb f unify_name || text_eqb f unify_bang_name) n
  then [unify_name; unify_bang_name] else []).

Definition D_names (rows : list row) (r : row) : list name :=
 let ms := markers (r_nf r) in
 dedup ((if has_do (r_nf r) then [do_name] else []) ++ kernel_used (r_src r) ++ port_used (r_nf r)
        ++ mclose (mfuel rows ms) rows ms []).

(* ---------- the D constructor ---------- *)
(* Each name with its row's LOWERED body. None if a name has no decoded row. *)
Fixpoint D_low (rows : list row) (ns : list name) : option (list (name * fundef)) := match ns with
 | [] => Some []
 | f :: ns => match find_row rows f, D_low rows ns with
   | Some r, Some d => Some ((f, FUser (r_params r) (r_low r)) :: d)
   | _, _ => None end end.

Definition D_of (rows : list row) (f : name) : option (list (name * fundef)) :=
 match find_row rows f with Some r => D_low rows (D_names rows r) | None => None end.

(* The same callees with their SOURCE bodies: what the fresh-name premise must cover. *)
Fixpoint D_src (rows : list row) (ns : list name) : list expr := match ns with
 | [] => []
 | f :: ns => match find_row rows f with Some r => r_src r :: D_src rows ns | None => D_src rows ns end end.

(* Interface item 1: the fresh-name premise the front rules use. *)
Definition fresh_front (ns : name) (rows : list row) (b0 : expr) (names : list name) : bool :=
 K.fresh_ok ns (b0 :: D_src rows names).

(* ======================= D_compiled' ======================= *)
(* Every user definition in D is code the emission relation accepts, with the shape FunRel's
   fr_user needs (arity, no entry point): the emit judge on each callee's lowered body. *)
Definition D_compiled' (D : list (name * fundef)) (cs : list (name * B.code)) : bool :=
 forallb (fun p => match snd p with
   | FUser ps b => match lookup (fst p) cs with
     | Some c => (N.eqb (B.code_arity c) (N.of_nat (List.length ps))
                  && match B.code_entry c with None => true | Some _ => false end
                  && check_fn c ps b)%bool
     | None => false end
   | FPrim _ => true end) D.

Definition D_compiled'_spec_statement : Prop := forall D cs,
 D_compiled' D cs = true -> forall f ps b, In (f, FUser ps b) D ->
 exists c, lookup f cs = Some c /\ B.code_arity c = N.of_nat (List.length ps) /\ B.code_entry c = None /\ CompFn c ps b.

Theorem D_compiled'_spec : D_compiled'_spec_statement.
Proof.
 intros D cs H f ps b I. unfold D_compiled' in H. rewrite forallb_forall in H.
 specialize (H _ I). cbn in H. destruct (lookup f cs) as [c|]; [|discriminate].
 apply andb_true_iff in H as [H Ck]. apply andb_true_iff in H as [Ar En].
 exists c. split; [reflexivity|]. split; [apply N.eqb_eq; exact Ar|]. split.
 - destruct (B.code_entry c); [discriminate|reflexivity].
 - apply check_fn_sound; exact Ck.
Qed.

(* D_compiled' is JitKRef's D_compiled with the code's shape added. *)
Theorem D_compiled'_D_compiled : forall D cs, D_compiled' D cs = true -> K.D_compiled D cs = true.
Proof.
 intros D cs H. unfold D_compiled', K.D_compiled in *. rewrite forallb_forall in *.
 intros p I. specialize (H p I). destruct (snd p) as [q|ps b]; [reflexivity|].
 destruct (lookup (fst p) cs) as [c|]; [|discriminate].
 apply andb_true_iff in H as [_ Ck]. exact Ck.
Qed.

(* ---------- D_of is well formed for stage 0's sealed list ---------- *)
Lemma dedup_nodup : forall l, NoDup (dedup l).
Proof.
 induction l as [|x l IH]; cbn; constructor.
 - intro I. apply filter_In in I as [_ I]. rewrite text_eqb_refl in I. discriminate.
 - apply NoDup_filter. exact IH.
Qed.

Lemma D_low_keys : forall rows ns d, D_low rows ns = Some d -> map fst d = ns.
Proof.
 intros rows ns; induction ns as [|f ns IH]; intros d H; cbn in H.
 - inversion H; reflexivity.
 - destruct (find_row rows f) as [r|]; [|discriminate].
   destruct (D_low rows ns) as [d'|] eqn:E; [|discriminate].
   inversion H; subst. cbn. f_equal. apply IH. reflexivity.
Qed.

Lemma D_low_found : forall rows ns d f, D_low rows ns = Some d -> In f (map fst d) -> In f (map r_name rows).
Proof.
 intros rows ns; induction ns as [|g ns IH]; intros d f H I; cbn in H.
 - inversion H; subst; contradiction.
 - destruct (find_row rows g) as [r|] eqn:Fr; [|discriminate].
   destruct (D_low rows ns) as [d'|] eqn:E; [|discriminate].
   inversion H; subst. cbn in I. destruct I as [<-|I]; [|eapply IH; eauto].
   unfold find_row in Fr. apply find_some in Fr as [Ir Eq]. apply text_eqb_eq in Eq.
   rewrite <- Eq. apply in_map. exact Ir.
Qed.

Theorem D_of_nodup : forall rows f D, D_of rows f = Some D -> NoDup (map fst D).
Proof.
 intros rows f D H. unfold D_of in H. destruct (find_row rows f) as [r|]; [|discriminate].
 rewrite (D_low_keys _ _ _ H). apply dedup_nodup.
Qed.

(* D_wf for any sealed list that has every stage 0 name the table decoded. *)
Theorem D_of_wf : forall sealed rows f D, incl (map r_name rows) sealed -> D_of rows f = Some D -> K.D_wf sealed D.
Proof.
 intros sealed rows f D Inc H. split; [|eapply D_of_nodup; eauto].
 apply Forall_forall. intros p Ip. apply Inc.
 unfold D_of in H. destruct (find_row rows f) as [r|]; [|discriminate].
 eapply D_low_found; [exact H|]. apply in_map. exact Ip.
Qed.

(* ======================= the allowed store facts ======================= *)
Definition D_has_inline_callee (D : list (name * fundef)) (f : name) (ps : list name) (eF : expr) : Prop :=
 In (f, FUser ps eF) D.
Definition D_has_kernel_thaw (D : list (name * fundef)) : Prop :=
 exists v, In (thaw_name, FUser [v] (EApp (EVar v) [])) D.
Definition D_has_kernel_protect (D : list (name * fundef)) : Prop :=
 exists v, In (protect_name, FUser [v] (EVar v)) D.
Definition D_has_kernel_do (D : list (name * fundef)) : Prop :=
 exists v1 v2, v1 <> v2 /\ In (do_name, FUser [v1; v2] (EVar v2)) D.
Definition D_has_bind (D : list (name * fundef)) : Prop :=
 exists ps b, In (bind_name, FUser ps b) D /\ List.length ps = 4%nat.
Definition D_prims_fold (D : list (name * fundef)) : Prop :=
 In (plus_name, FPrim PAdd) D /\ In (minus_name, FPrim PSub) D.
Definition D_has_port_deref_eq (D : list (name * fundef)) : Prop :=
 exists ps b, In (deref_eq_name, FUser ps b) D /\ List.length ps = 3%nat.
Definition D_has_port_unify (D : list (name * fundef)) : Prop :=
 (exists ps b, In (unify_name, FUser ps b) D /\ List.length ps = 4%nat) /\
 (exists ps b, In (unify_bang_name, FUser ps b) D /\ List.length ps = 4%nat).
(* shen.bindv and shen.unwind: inline callees like any other (D_has_inline_callee), named because
   the spec asks for each port defun bind! relies on. See the header for which checker owns their
   markers inside a bound-now expansion (bind_site, which uses neither fact). *)
Definition D_has_port_bindv (D : list (name * fundef)) : Prop :=
 exists ps b, D_has_inline_callee D bindv_name ps b /\ List.length ps = 3%nat.
Definition D_has_port_unwind (D : list (name * fundef)) : Prop :=
 exists ps b, D_has_inline_callee D unwind_name ps b /\ List.length ps = 3%nat.
(* A store fact, not a D entry (see the header). *)
Definition D_cons_prim (s : store) : Prop := lookup cons_name (gfuns s) = Some (FPrim PCons).

Lemma cons_name_prim : prim_of_name cons_name = Some PCons.
Proof. vm_compute. reflexivity. Qed.

Theorem D_cons_prim_of_Com : forall s m, JitLowerStep.JitLowerStep.Com s m -> D_cons_prim s.
Proof.
 intros s m [_ Fr]. unfold D_cons_prim.
 exact (JitLowerStep.JitLowerStep.fr_name s m Fr cons_name PCons cons_name_prim).
Qed.

(* ======================= alpha-equivalence ======================= *)
Definition num_eqb (a b : num) : bool := match a, b with
 | NInt x, NInt y => Z.eqb x y | NFloat x, NFloat y => N.eqb x y | _, _ => false end.

(* rn pairs a source binder with a target binder, innermost first. A variable bound on one side
   must be bound by the paired binder on the other; a free variable must be free on both sides
   with the same name, so a free name is never renamed and never captured. *)
Fixpoint var_ok (rn : list (name * name)) (x y : name) : bool := match rn with
 | [] => text_eqb x y
 | (a, b) :: rn => if text_eqb a x then text_eqb b y else if text_eqb b y then false else var_ok rn x y end.

(* A binder may not be KLPort's closure-identity key: closure_id reads the head of an
   environment, so binding that name would change what = says about closures. *)
Definition binder_ok (x y : name) : bool := negb (text_eqb x KLPort.KLPort.id_key) && negb (text_eqb y KLPort.KLPort.id_key).

(* `aeq rn e0 e`: e is e0 with bound names renamed (source e0, target e). Symbols, called names
   and free variables are compared as they are. A defun is never equivalent (no inline body or
   lowered body has one). *)
Fixpoint aeq (rn : list (name * name)) (e0 e : expr) {struct e0} : bool :=
 let args := fix args (l0 l : list expr) : bool := match l0, l with
   | [], [] => true | a0 :: l0, a :: l => aeq rn a0 a && args l0 l | _, _ => false end in
 let cls := fix cls (l0 l : list (expr * expr)) : bool := match l0, l with
   | [], [] => true
   | (c0, b0) :: l0, (c, b) :: l => aeq rn c0 c && aeq rn b0 b && cls l0 l
   | _, _ => false end in
 match e0, e with
 | ENum a, ENum b => num_eqb a b
 | EStr a, EStr b => text_eqb a b
 | ESym a, ESym b => text_eqb a b
 | EBool a, EBool b => Bool.eqb a b
 | ENil, ENil => true
 | EVar x, EVar y => var_ok rn x y
 | ELam x b0, ELam y b => binder_ok x y && aeq ((x, y) :: rn) b0 b
 | ELet x a0 b0, ELet y a b => binder_ok x y && aeq rn a0 a && aeq ((x, y) :: rn) b0 b
 | EIf c0 a0 b0, EIf c a b => aeq rn c0 c && aeq rn a0 a && aeq rn b0 b
 | EAnd a0 b0, EAnd a b => aeq rn a0 a && aeq rn b0 b
 | EOr a0 b0, EOr a b => aeq rn a0 a && aeq rn b0 b
 | ETrap a0 b0, ETrap a b => aeq rn a0 a && aeq rn b0 b
 | ECond l0, ECond l => cls l0 l
 | EFreeze a0, EFreeze a => aeq rn a0 a
 | EType a0, EType a => aeq rn a0 a
 | EApp h0 l0, EApp h l => aeq rn h0 h && args l0 l
 | ECall f0 l0, ECall f l => text_eqb f0 f && args l0 l
 | _, _ => false end.

Section Sound.
Variables (sealed : list name) (D : list (name * fundef)).

(* To be proved by F-inline: alpha-equivalent expressions refine each other. scoped g e0: a free
   variable of e0 outside g would be read from unrelated environments. *)
Definition aeq_sound_statement : Prop := forall g e0 e,
 K.D_wf sealed D -> K.scoped g e0 = true -> aeq [] e0 e = true -> K.KRef sealed D g e0 e.
End Sound.

(* Syntactic equality: lower.shen puts a normalised argument into its expansion as it is (the fresh
   let's value, and the body thawed in place), so the site checker asks for the same term, not an
   alpha-equivalent one: a proof then needs no renaming lemma for these positions. *)
Fixpoint expr_eqb (a b : expr) {struct a} : bool :=
 let args := fix args (l0 l : list expr) : bool := match l0, l with
   | [], [] => true | x :: l0, y :: l => expr_eqb x y && args l0 l | _, _ => false end in
 let cls := fix cls (l0 l : list (expr * expr)) : bool := match l0, l with
   | [], [] => true
   | (c0, b0) :: l0, (c, b1) :: l => expr_eqb c0 c && expr_eqb b0 b1 && cls l0 l
   | _, _ => false end in
 match a, b with
 | ENum x, ENum y => num_eqb x y
 | EStr x, EStr y => text_eqb x y
 | ESym x, ESym y => text_eqb x y
 | EBool x, EBool y => Bool.eqb x y
 | ENil, ENil => true
 | EVar x, EVar y => text_eqb x y
 | ELam x p, ELam y q => text_eqb x y && expr_eqb p q
 | ELet x p q, ELet y p' q' => text_eqb x y && expr_eqb p p' && expr_eqb q q'
 | EIf c0 a0 b0, EIf c a1 b1 => expr_eqb c0 c && expr_eqb a0 a1 && expr_eqb b0 b1
 | EAnd a0 b0, EAnd a1 b1 => expr_eqb a0 a1 && expr_eqb b0 b1
 | EOr a0 b0, EOr a1 b1 => expr_eqb a0 a1 && expr_eqb b0 b1
 | ETrap a0 b0, ETrap a1 b1 => expr_eqb a0 a1 && expr_eqb b0 b1
 | ECond l0, ECond l => cls l0 l
 | EFreeze p, EFreeze q => expr_eqb p q
 | EType p, EType q => expr_eqb p q
 | EDefun f ps p, EDefun g qs q => text_eqb f g && names_eqb ps qs && expr_eqb p q
 | EApp h0 l0, EApp h l => expr_eqb h0 h && args l0 l
 | ECall f l0, ECall g l => text_eqb f g && args l0 l
 | _, _ => false end.

(* ======================= the inline relation ======================= *)
(* A parameter of the inlined callee that lower.shen did not bind: an integer constant put into
   the body (inline-numbers), or a frozen argument thawed in place (inline-frozen). *)
Inductive sarg := SInt (z : Z) | SFrozen (x : expr).

Definition free_in (rn : list (name * name)) (x : name) : bool := negb (existsb (fun p => text_eqb (fst p) x) rn).
Definition hidden (rn : list (name * name)) (x : name) : bool := existsb (fun p => text_eqb (snd p) x) rn.
Definition disjoint (xs ys : list name) : bool := forallb (fun x => negb (bound ys x)) xs.

(* lower.shen's small-integers?: both operands of a folded + or - are below 10^9 in magnitude. *)
Definition small (z : Z) : bool := Z.ltb (Z.abs z) 1000000000.
(* The integer a source expression folds to, under the substitution: lower.shen's `prim`, bottom up. *)
Fixpoint sval (sg : list (name * sarg)) (rn : list (name * name)) (e : expr) : option Z := match e with
 | ENum (NInt z) => Some z
 | EVar p => if free_in rn p then match lookup p sg with Some (SInt z) => Some z | _ => None end else None
 | ECall f [a; b] =>
   if text_eqb f plus_name || text_eqb f minus_name then
     match sval sg rn a, sval sg rn b with
     | Some x, Some y => if small x && small y then Some (if text_eqb f plus_name then x + y else x - y)%Z else None
     | _, _ => None end
   else None
 | _ => None end.

Fixpoint take_lets (n : nat) (e : expr) : option (list (name * expr) * expr) := match n with
 | O => Some ([], e)
 | S n => match e with
   | ELet a v b => match take_lets n b with Some (l, r) => Some ((a, v) :: l, r) | None => None end
   | _ => None end end.

(* Lets in sequence, each value read under the earlier lets: distinct names, and no value mentions
   an earlier name (so it means what it would at the start). *)
Fixpoint fresh_seq (seen : list name) (l : list (name * expr)) : bool := match l with
 | [] => true
 | (a, v) :: l => disjoint (K.fv v) seen && negb (bound seen a) && fresh_seq (a :: seen) l end.

Fixpoint vars_are (vs : list expr) (xs : list name) : bool := match vs, xs with
 | [], [] => true
 | EVar a :: vs, x :: xs => text_eqb a x && vars_are vs xs
 | _, _ => false end.

Fixpoint dsize (e : expr) : nat := match e with
 | ELam _ b | EFreeze b | EType b | EDefun _ _ b => S (dsize b)
 | ELet _ a b | EAnd a b | EOr a b | ETrap a b => S (dsize a + dsize b)
 | EIf c a b => S (dsize c + dsize a + dsize b)
 | ECond cl => S (fold_right (fun p n => dsize (fst p) + dsize (snd p) + n) 0 cl)
 | EApp h args => S (dsize h + fold_right (fun a n => dsize a + n) 0 args)
 | ECall _ args => S (fold_right (fun a n => dsize a + n) 0 args)
 | _ => 1 end.

(* `inl_eq fuel fold letdo D sg rn e0 e`: e (target, the inlined normal body N, erased) against e0
   (source, the callee's lowered body e_F), under the substitution sg of unbound parameters.
   - congruence and renaming, as aeq;
   - a free parameter p with sg p = SInt z against the constant z;
   - (apply p) with sg p = SFrozen x against x itself (the same term), no free name of x hidden by
     a target binder on the way;
   - fold = true: a source (+ a b) or (- a b) that folds to c under sg, against the constant c;
   - letdo = true: a source (let X A B), X not free in B, against (do A' B'), as bind!'s;
   - depth cut: a source region (lets of fresh names, lets of G's parameters, a body scoped in G's
     parameters and alpha-equivalent to e_G) against the target call (G args), G's lowered body in
     D, the arguments related by inl_eq. Here the target runs e_G and the source the region's body,
     which is aeq_sound_statement with e0 := the body, e := e_G.
   Any other parameter use fails: a substituted parameter is unbound in the target. *)
Fixpoint inl_eq (fuel : nat) (fold letdo : bool) (D : list (name * fundef)) (sg : list (name * sarg))
  (rn : list (name * name)) (e0 e : expr) {struct fuel} : bool :=
 match fuel with O => false | S fuel =>
 let go := inl_eq fuel fold letdo D sg in
 let args := fix args (l0 l : list expr) : bool := match l0, l with
   | [], [] => true | a0 :: l0, a :: l => go rn a0 a && args l0 l | _, _ => false end in
 let cls := fix cls (l0 l : list (expr * expr)) : bool := match l0, l with
   | [], [] => true
   | (c0, b0) :: l0, (c, b) :: l => go rn c0 c && go rn b0 b && cls l0 l
   | _, _ => false end in
 let cong := match e0, e with
   | ENum a, ENum b => num_eqb a b
   | EStr a, EStr b => text_eqb a b
   | ESym a, ESym b => text_eqb a b
   | EBool a, EBool b => Bool.eqb a b
   | ENil, ENil => true
   | EVar x, EVar y => var_ok rn x y
   | ELam x b0, ELam y b => binder_ok x y && go ((x, y) :: rn) b0 b
   | ELet x a0 b0, ELet y a b => binder_ok x y && go rn a0 a && go ((x, y) :: rn) b0 b
   | EIf c0 a0 b0, EIf c a b => go rn c0 c && go rn a0 a && go rn b0 b
   | EAnd a0 b0, EAnd a b => go rn a0 a && go rn b0 b
   | EOr a0 b0, EOr a b => go rn a0 a && go rn b0 b
   | ETrap a0 b0, ETrap a b => go rn a0 a && go rn b0 b
   | ECond l0, ECond l => cls l0 l
   | EFreeze a0, EFreeze a => go rn a0 a
   | EType a0, EType a => go rn a0 a
   | EApp h0 l0, EApp h l => go rn h0 h && args l0 l
   | ECall f0 l0, ECall f l => text_eqb f0 f && args l0 l
   | _, _ => false end in
 let cut := match e with
   | ECall g l => match lookup g D with
     | Some (FUser psG eG) =>
       let k := List.length psG in
       match take_lets k e0 with
       | Some (fr, rest) => match take_lets k rest with
         | Some (pl, body) =>
           Nat.eqb (List.length l) k && names_eqb (map fst pl) psG && vars_are (map snd pl) (map fst fr)
           && fresh_seq [] fr && disjoint (map fst pl) (map fst fr) && K.scoped psG body
           && args (map snd fr) l && aeq [] body eG
         | None => false end
       | None => false end
     | _ => false end
   | _ => false end in
 match e0 with
 | EVar p =>
   if free_in rn p then match lookup p sg with
     | Some (SInt z) => match e with ENum (NInt z') => Z.eqb z z' | _ => false end
     | Some (SFrozen _) => false
     | None => cong end
   else cong
 | EApp (EVar p) [] =>
   if free_in rn p then match lookup p sg with
     | Some (SFrozen x) => expr_eqb x e && forallb (fun y => negb (hidden rn y)) (K.fv x)
     | Some (SInt _) => false
     | None => cong end
   else cong
 | ECall f [_; _] =>
   if fold && (text_eqb f plus_name || text_eqb f minus_name) then
     match e with
     | ENum (NInt c) => match sval sg rn e0 with Some c' => Z.eqb c c' | None => false end
     | _ => cong end
   else cong
 | ELet x a0 b0 =>
   match e with
   | ECall d [a; b] =>
     if letdo && text_eqb d do_name && negb (bound (K.fv b0) x) then go rn a0 a && go rn b0 b else cut
   | ECall _ _ => cut
   | _ => cong end
 | _ => cong end end.

(* ---------- the inline site ---------- *)
(* lower.shen's expansion of a call to F with normalised arguments nargs:
     (let a1 v1 ... (let ak vk (let q1 a1 ... (let qk ak N))))
   where an integer-constant argument is put into N (SInt), a frozen argument may be thawed in N
   (SFrozen), and every other argument is bound to a fresh name and then to its parameter, in
   order (vi the argument itself). peel splits the expansion along the parameters. *)
Fixpoint peel (ps : list name) (nargs : list expr) (e : expr)
  : option (list (name * sarg) * list (name * name * expr) * expr) :=
 match ps, nargs with
 | [], [] => Some ([], [], e)
 | p :: ps, n :: ns =>
   let frozen := match n with
     | EFreeze x => match peel ps ns e with Some (sg, kept, r) => Some ((p, SFrozen x) :: sg, kept, r) | None => None end
     | _ => None end in
   match n with
   | ENum (NInt z) => match peel ps ns e with Some (sg, kept, r) => Some ((p, SInt z) :: sg, kept, r) | None => None end
   | _ => match e with
     | ELet a v b => if expr_eqb n v then
         match peel ps ns b with Some (sg, kept, r) => Some (sg, (a, p, v) :: kept, r) | None => None end
       else frozen
     | _ => frozen end end
 | _, _ => None end.

Fixpoint peel_params (kept : list (name * name * expr)) (e : expr) : option expr := match kept with
 | [] => Some e
 | (a, p, _) :: kept => match e with
   | ELet q (EVar a') b => if text_eqb q p && text_eqb a a' then peel_params kept b else None
   | _ => None end end.

Definition frozen_free (sg : list (name * sarg)) (xs : list name) : bool :=
 forallb (fun q => match snd q with SFrozen x => disjoint (K.fv x) xs | SInt _ => true end) sg.

Definition inl_site (fold letdo : bool) (D : list (name * fundef)) (f : name) (nargs : list expr) (e : expr) : bool :=
 match lookup f D with
 | Some (FUser ps eF) =>
   nodupb ps && K.scoped ps eF &&
   match peel ps nargs e with
   | Some (sg, kept, r) =>
     let fr := map (fun t => let '(a, _, v) := t in (a, v)) kept in
     let qs := map (fun t => let '(_, q, _) := t in q) kept in
     fresh_seq [] fr && disjoint qs (map fst fr) && frozen_free sg (map fst fr ++ qs) &&
     match peel_params kept r with
     | Some N => inl_eq (S (dsize eF)) fold letdo D sg [] eF N
     | None => false end
   | None => false end
 | _ => false end.

(* bound-now's expansion of (shen.bind! X Y B (freeze E)), normalised arguments [x; y; b; EFreeze E]:
     (let a1 x (let a2 y (let a3 b N)))
   with N against bind!'s lowered body e_B: e_B's first three parameters renamed to a1 a2 a3, its
   fourth thawed as E, its unused let read as do. The `disjoint (K.fv ex) [a1; a2; a3]` guard is
   implied by inl_eq's hidden-name check whenever e_B thaws its fourth parameter (the seeded pairs
   stay in rn at every depth, and the check reads the target side of every pair); stage 0's e_B
   does. It is kept for an e_B that does not, so removing it is an equivalent mutant on stage 0's
   data, not a lost check; bind_site's own mutant (letdo off) is ShenJitFrontBindLetdo. *)
Definition bind_site (fold : bool) (D : list (name * fundef)) (nargs : list expr) (e : expr) : bool :=
 match lookup bind_name D, nargs with
 | Some (FUser [p1; p2; p3; p4] eB), [x; y; b; EFreeze ex] =>
   nodupb [p1; p2; p3; p4] && K.scoped [p1; p2; p3; p4] eB &&
   match e with
   | ELet a1 x' (ELet a2 y' (ELet a3 b' N)) =>
     expr_eqb x x' && expr_eqb y y' && expr_eqb b b' &&
     fresh_seq [] [(a1, x'); (a2, y'); (a3, b')] &&
     binder_ok p1 a1 && binder_ok p2 a2 && binder_ok p3 a3 &&
     disjoint (K.fv ex) [a1; a2; a3] &&
     inl_eq (S (dsize eB)) fold true D [(p4, SFrozen ex)] [(p3, a3); (p2, a2); (p1, a1)] eB N
   | _ => false end
 | _, _ => false end.

Section SiteSound.
Variables (sealed : list name) (D : list (name * fundef)).

(* To be proved by F-inline: a call of a D callee refines lower.shen's expansion of it, given that
   each source argument refines its normalised argument. The fold and letdo cases take their store
   facts (D_prims_fold, interface item 2; D_has_kernel_do). *)
Definition inline_site_sound_statement : Prop := forall fold letdo g f args0 nargs e,
 K.D_wf sealed D ->
 (fold = true -> D_prims_fold D) -> (letdo = true -> D_has_kernel_do D) ->
 inl_site fold letdo D f nargs e = true ->
 Forall2 (K.KRef sealed D g) args0 nargs ->
 K.KRef sealed D g (ECall f args0) e.

(* To be proved by F-inline (or the bind family): a call of shen.bind! refines bound-now's
   expansion, given its arguments refine their normalised forms. *)
Definition bind_site_sound_statement : Prop := forall fold g args0 nargs e,
 K.D_wf sealed D ->
 (fold = true -> D_prims_fold D) -> D_has_kernel_do D ->
 bind_site fold D nargs e = true ->
 Forall2 (K.KRef sealed D g) args0 nargs ->
 K.KRef sealed D g (ECall bind_name args0) e.
End SiteSound.

(* ======================= reports (for the --D smoke run) ======================= *)
Definition D_stats (fs ns ss : list sx) : nat * nat * bool :=
 match rows_of fs ns ss with
 | Some rows => (List.length fs, List.length rows, nodupb (map r_name rows))
 | None => (List.length fs, O, false) end.

(* A definition's D: its names, and whether D_compiled' holds against the table's code objects. *)
Definition D_report (rows : list row) (f : string) : option (list string * bool) :=
 match D_of rows (of_string f) with
 | Some d => Some (map (fun p => show (fst p)) d, D_compiled' d (codes rows))
 | None => None end.

(* bound-now sites, read back from a normal form (a TEST harness: the site's arguments are taken
   from the expansion itself, so expr_eqb on them is trivially true; what is tested is N against
   e_B). A site is (let a1 x (let a2 y (let a3 b (do (let _ a1 (let _ a2 (let _ a3 _))) (let _ E _)))))
   where the do's first argument is bindv's inlined region reading a1 a2 a3. *)
Fixpoint subterms (e : expr) : list expr := e :: match e with
 | ECall _ l => (fix go (l : list expr) : list expr := match l with [] => [] | a :: l => subterms a ++ go l end) l
 | ELam _ b | EFreeze b | EType b | EDefun _ _ b => subterms b
 | ELet _ a b | EAnd a b | EOr a b | ETrap a b => subterms a ++ subterms b
 | EIf c a b => subterms c ++ subterms a ++ subterms b
 | ECond cl => (fix go (l : list (expr * expr)) : list expr := match l with [] => [] | (c, b) :: l => subterms c ++ subterms b ++ go l end) cl
 | EApp h l => subterms h ++ (fix go (l : list expr) : list expr := match l with [] => [] | a :: l => subterms a ++ go l end) l
 | _ => [] end.
Definition bind_args (e : expr) : option (list expr) := match e with
 | ELet a1 x (ELet a2 y (ELet a3 b (ECall d [ELet _ (EVar c1) (ELet _ (EVar c2) (ELet _ (EVar c3) _)); ELet _ ex _]))) =>
   if text_eqb d do_name && text_eqb a1 c1 && text_eqb a2 c2 && text_eqb a3 c3 then Some [x; y; b; EFreeze ex] else None
 | _ => None end.
(* For each definition with a bound-now site: its name, how many sites, how many bind_site accepts
   (fold = false) against its D_of store. *)
Definition bind_report (rows : list row) : list (string * nat * nat) :=
 flat_map (fun r =>
   let cs := flat_map (fun s => match bind_args s with Some a => [(a, s)] | None => [] end) (subterms (r_low r)) in
   match cs with [] => [] | _ =>
     [(show (r_name r), List.length cs,
       match D_of rows (r_name r) with
       | Some D => List.length (filter (fun p => bind_site false D (fst p) (snd p)) cs)
       | None => O end)] end) rows.
(* The definitions whose D_of store holds a name. *)
Definition D_holders (rows : list row) (f : name) : list string :=
 flat_map (fun r => match D_of rows (r_name r) with
   | Some D => match lookup f D with Some _ => [show (r_name r)] | None => [] end
   | None => [] end) rows.

(* ======================= examples (tests, not evidence) ======================= *)
Definition v (s : string) : expr := EVar (of_string s).
Definition nm (s : string) : name := of_string s.

(* port_used: a normal form calling shen-jit.unify=! brings in both unify forms; deref= alone. *)
Example port_used_unify : port_used (NCall unify_bang_name [NVar (nm "X")]) = [unify_name; unify_bang_name].
Proof. vm_compute. reflexivity. Qed.
Example port_used_deref : port_used (NIf (NCall deref_eq_name []) (NConst (VSym (nm "a"))) (NVar (nm "b"))) = [deref_eq_name].
Proof. vm_compute. reflexivity. Qed.
Example port_used_none : port_used (NCall (nm "shen.bindv") []) = [].
Proof. vm_compute. reflexivity. Qed.

(* Renaming a bound name is accepted, on both sides consistently. *)
Example aeq_rename : aeq [] (ELet (nm "x") (ENum (NInt 1)) (v "x")) (ELet (nm "y") (ENum (NInt 1)) (v "y")) = true.
Proof. reflexivity. Qed.
(* Free variables are not renamed. *)
Example aeq_free_swap : aeq [] (ECall (nm "f") [v "a"; v "b"]) (ECall (nm "f") [v "b"; v "a"]) = false.
Proof. reflexivity. Qed.
(* A variable is not a symbol. *)
Example aeq_var_sym : aeq [] (v "a") (ESym (nm "a")) = false.
Proof. reflexivity. Qed.
(* Capture: the target binder y captures the free y. *)
Example aeq_capture : aeq [] (ELam (nm "x") (ECall (nm "f") [v "x"; v "y"])) (ELam (nm "y") (ECall (nm "f") [v "y"; v "y"])) = false.
Proof. reflexivity. Qed.
(* Shadowing: inner binder pairs win. *)
Example aeq_shadow : aeq [] (ELam (nm "x") (ELam (nm "x") (v "x"))) (ELam (nm "a") (ELam (nm "b") (v "b"))) = true.
Proof. reflexivity. Qed.
Example aeq_shadow_wrong : aeq [] (ELam (nm "x") (ELam (nm "x") (v "x"))) (ELam (nm "a") (ELam (nm "b") (v "a"))) = false.
Proof. reflexivity. Qed.
(* The closure-identity key is no binder. *)
Example aeq_id_key : aeq [] (ELam (nm "x") (v "x")) (ELam KLPort.KLPort.id_key (EVar KLPort.KLPort.id_key)) = false.
Proof. reflexivity. Qed.

(* The shape of a real site, transcribed: shen.fbound? inlines not
   ((defun shen.fbound? (V7092) (not (= (arity V7092) -1))), witness: (let stage0.lower.arg1 (prim =
   ((call arity ((var V7092))) (const -1))) (let V4070 (var stage0.lower.arg1) <marker> (if (var
   V4070) (const false) (const true))))), and not's own witness (if (var V4070) (const false)
   (const true))). *)
Definition not_body : expr := EIf (v "V4070") (EBool false) (EBool true).
Definition D_not : list (name * fundef) := [(nm "not", FUser [nm "V4070"] not_body)].
Definition fb_arg : expr := ECall (nm "=") [ECall (nm "arity") [v "V7092"]; ENum (NInt (-1))].
Definition fb_site : expr :=
 ELet (nm "stage0.lower.arg1") fb_arg (ELet (nm "V4070") (v "stage0.lower.arg1") not_body).
Example site_fbound : inl_site false false D_not (nm "not") [fb_arg] fb_site = true.
Proof. vm_compute. reflexivity. Qed.
(* The parameter let must bind the fresh name, not the caller's variable. *)
Example site_fbound_wrong : inl_site false false D_not (nm "not") [fb_arg]
 (ELet (nm "stage0.lower.arg1") fb_arg (ELet (nm "V4070") (v "V7092") not_body)) = false.
Proof. vm_compute. reflexivity. Qed.

(* Integer substitution, the shape of shen.<lsb>'s shen.hds=? site (B := 91). *)
Definition hds_body : expr :=
 EAnd (ECall (nm "cons?") [v "X"]) (ECall (nm "=") [ECall (nm "hd") [v "X"]; v "B"]).
Definition D_hds : list (name * fundef) := [(nm "shen.hds=?", FUser [nm "X"; nm "B"] hds_body)].
Definition hds_site : expr :=
 ELet (nm "stage0.lower.arg1") (v "V1") (ELet (nm "X") (v "stage0.lower.arg1")
  (EAnd (ECall (nm "cons?") [v "X"]) (ECall (nm "=") [ECall (nm "hd") [v "X"]; ENum (NInt 91)]))).
Example site_hds : inl_site false false D_hds (nm "shen.hds=?") [v "V1"; ENum (NInt 91)] hds_site = true.
Proof. vm_compute. reflexivity. Qed.
Example site_hds_wrong_int : inl_site false false D_hds (nm "shen.hds=?") [v "V1"; ENum (NInt 92)] hds_site = false.
Proof. vm_compute. reflexivity. Qed.

(* Folding, the shape of the vector sites ((vector 0): (+ N 1) folds to 1). Needs fold = true. *)
Definition vec_body : expr :=
 ECall (nm "address->") [ECall (nm "absvector") [ECall plus_name [v "N"; ENum (NInt 1)]]; ENum (NInt 0); v "N"].
Definition D_vec : list (name * fundef) := [(nm "vector", FUser [nm "N"] vec_body)].
Definition vec_site : expr :=
 ECall (nm "address->") [ECall (nm "absvector") [ENum (NInt 1)]; ENum (NInt 0); ENum (NInt 0)].
Example site_vector_fold : inl_site true false D_vec (nm "vector") [ENum (NInt 0)] vec_site = true.
Proof. vm_compute. reflexivity. Qed.
Example site_vector_nofold : inl_site false false D_vec (nm "vector") [ENum (NInt 0)] vec_site = false.
Proof. vm_compute. reflexivity. Qed.

(* Thaw-with, the shape of when's sites: (when C _ _ _ (freeze E)) with E in place of (thaw K). *)
Definition when_body : expr := EIf (v "C") (EApp (v "K") []) (EBool false).
Definition D_when : list (name * fundef) := [(nm "when", FUser [nm "C"; nm "K"] when_body)].
Definition when_e : expr := ECall (nm "g") [v "Z"].
Definition when_site : expr :=
 ELet (nm "stage0.lower.arg1") (v "T") (ELet (nm "C") (v "stage0.lower.arg1") (EIf (v "C") when_e (EBool false))).
Example site_when : inl_site false false D_when (nm "when") [v "T"; EFreeze when_e] when_site = true.
Proof. vm_compute. reflexivity. Qed.
(* The thawed expression may not read a name the expansion binds. *)
Example site_when_capture : inl_site false false D_when (nm "when") [v "T"; EFreeze (ECall (nm "g") [v "C"])]
 (ELet (nm "stage0.lower.arg1") (v "T") (ELet (nm "C") (v "stage0.lower.arg1") (EIf (v "C") (ECall (nm "g") [v "C"]) (EBool false)))) = false.
Proof. vm_compute. reflexivity. Qed.

(* Depth cut, the shape of shen.locked?: the source (locked?'s lowered body) inlines unlocked?, the
   target (inlined one level deeper) calls it. *)
Definition unl_body : expr := ECall (nm "<-address") [v "V1901"; ENum (NInt 1)].
Definition locked_body : expr :=
 ELet (nm "stage0.lower.arg1") (v "V1900") (ELet (nm "V1901") (v "stage0.lower.arg1") unl_body).
Definition D_lock : list (name * fundef) :=
 [(nm "shen.locked?", FUser [nm "V1900"] locked_body); (nm "shen.unlocked?", FUser [nm "V1901"] unl_body)].
Definition lock_site : expr :=
 ELet (nm "stage0.lower.arg9") (v "W") (ELet (nm "V1900") (v "stage0.lower.arg9") (ECall (nm "shen.unlocked?") [v "V1900"])).
Example site_cut : inl_site false false D_lock (nm "shen.locked?") [v "W"] lock_site = true.
Proof. vm_compute. reflexivity. Qed.
(* Without unlocked? in D, the cut is not admitted. *)
Example site_cut_needs_D : inl_site false false [(nm "shen.locked?", FUser [nm "V1900"] locked_body)] (nm "shen.locked?") [v "W"] lock_site = false.
Proof. vm_compute. reflexivity. Qed.

(* bound-now, SYNTHETIC (not stage 0's shape: here bindv and unwind are left as calls, while stage
   0's e_B and every real site have both inlined; site_bind_real below is the real one):
   e_B = (let W (shen.bindv P1 P2 P3) (let R (thaw P4) (if (= R false) (shen.unwind P1 P3 R) R))). *)
Definition bind_body : expr :=
 ELet (nm "W") (ECall (nm "shen.bindv") [v "P1"; v "P2"; v "P3"])
  (ELet (nm "R") (EApp (v "P4") [])
   (EIf (ECall (nm "=") [v "R"; EBool false]) (ECall (nm "shen.unwind") [v "P1"; v "P3"; v "R"]) (v "R"))).
Definition D_bind : list (name * fundef) :=
 [(bind_name, FUser [nm "P1"; nm "P2"; nm "P3"; nm "P4"] bind_body); (do_name, FUser [nm "A"; nm "B"] (v "B"))].
Definition bind_e : expr := ECall (nm "k") [v "Z"].
Definition bind_target (e : expr) : expr :=
 ELet (nm "a1") (v "X") (ELet (nm "a2") (v "Y") (ELet (nm "a3") (v "Bs")
  (ECall do_name [ECall (nm "shen.bindv") [v "a1"; v "a2"; v "a3"];
   ELet (nm "a4") e (EIf (ECall (nm "=") [v "a4"; EBool false]) (ECall (nm "shen.unwind") [v "a1"; v "a3"; v "a4"]) (v "a4"))]))).
Example site_bind : bind_site false D_bind [v "X"; v "Y"; v "Bs"; EFreeze bind_e] (bind_target bind_e) = true.
Proof. vm_compute. reflexivity. Qed.
(* E may not read a fresh name bound on the way. *)
Example site_bind_capture : bind_site false D_bind [v "X"; v "Y"; v "Bs"; EFreeze (v "a2")] (bind_target (v "a2")) = false.
Proof. vm_compute. reflexivity. Qed.

(* bound-now on real data, transcribed from the T02 capture (witness set e45add98...): stage 0's
   .norm entry for shen.bind! (prolog.norm), and the second bound-now site of shen.l-rules
   (t-star.norm, the subtree (let stage0.lower.arg152 ...) wrapped as an entry whose parameters are
   its free variables). e_B is bind!'s erased normal form, as D_of puts it in D. *)
Definition bind_norm : sx :=
 (XList [XSym "shen.bind!"; (XList [XSym "V2117"; XSym "V2118"; XSym "V2119"; XSym "V2120"]); (XList [XSym "let"; XSym "W2121"; (XList [XSym "let"; XSym
 "stage0.lower.arg1"; (XList [XSym "var"; XSym "V2117"]); (XList [XSym "let"; XSym "stage0.lower.arg2"; (XList [XSym "var"; XSym "V2118"]);
 (XList [XSym "let"; XSym "stage0.lower.arg3"; (XList [XSym "var"; XSym "V2119"]); (XList [XSym "let"; XSym "X"; (XList [XSym "var"; XSym
 "stage0.lower.arg1"]); (XList [XSym "let"; XSym "Value"; (XList [XSym "var"; XSym "stage0.lower.arg2"]); (XList [XSym "let"; XSym
 "Bindings"; (XList [XSym "var"; XSym "stage0.lower.arg3"]); (XList [XSym "let"; XSym "stage0.lower.inlining"; (XList [XSym "const"; XSym
 "shen.bindv"]); (XList [XSym "prim"; XSym "address->"; (XList [(XList [XSym "var"; XSym "Bindings"]); (XList [XSym "prim"; XSym
 "shen-jit.pvar-offset"; (XList [(XList [XSym "var"; XSym "X"])])]); (XList [XSym "var"; XSym "Value"])])])])])])])])])]); (XList [XSym
 "let"; XSym "W2122"; (XList [XSym "apply"; (XList [XSym "var"; XSym "V2120"])]); (XList [XSym "if"; (XList [XSym "prim"; XSym "="; (XList [(XList [XSym
 "var"; XSym "W2122"]); (XList [XSym "const"; XSym "false"])])]); (XList [XSym "let"; XSym "stage0.lower.arg4"; (XList [XSym "var"; XSym
 "V2117"]); (XList [XSym "let"; XSym "stage0.lower.arg5"; (XList [XSym "var"; XSym "V2119"]); (XList [XSym "let"; XSym "stage0.lower.arg6";
 (XList [XSym "var"; XSym "W2122"]); (XList [XSym "let"; XSym "X"; (XList [XSym "var"; XSym "stage0.lower.arg4"]); (XList [XSym "let"; XSym
 "Bindings"; (XList [XSym "var"; XSym "stage0.lower.arg5"]); (XList [XSym "let"; XSym "Compute"; (XList [XSym "var"; XSym
 "stage0.lower.arg6"]); (XList [XSym "let"; XSym "stage0.lower.inlining"; (XList [XSym "const"; XSym "shen.unwind"]); (XList [XSym "do";
 (XList [XSym "prim"; XSym "address->"; (XList [(XList [XSym "var"; XSym "Bindings"]); (XList [XSym "prim"; XSym "shen-jit.pvar-offset"; (XList [(XList
 [XSym "var"; XSym "X"])])]); (XList [XSym "const"; XSym "shen.-null-"])])]); (XList [XSym "var"; XSym "Compute"])])])])])])])])]); (XList
 [XSym "var"; XSym "W2122"])])])])]).
Definition lrules_site_norm : sx :=
 (XList [XSym "site"; (XList [XSym "V5356"; XSym "V5357"; XSym "V5358"; XSym "V5360"; XSym "W5361"; XSym "W5445"; XSym "W5446"; XSym "W5447"; XSym
 "W5453"; XSym "W5454"]); (XList [XSym "let"; XSym "stage0.lower.arg152"; (XList [XSym "var"; XSym "W5447"]); (XList [XSym "let"; XSym
 "stage0.lower.arg153"; (XList [XSym "prim"; XSym "cons"; (XList [(XList [XSym "var"; XSym "W5453"]); (XList [XSym "var"; XSym "W5454"])])]);
 (XList [XSym "let"; XSym "stage0.lower.arg154"; (XList [XSym "var"; XSym "V5357"]); (XList [XSym "do"; (XList [XSym "let"; XSym
 "stage0.lower.arg156"; (XList [XSym "var"; XSym "stage0.lower.arg152"]); (XList [XSym "let"; XSym "stage0.lower.arg157"; (XList [XSym
 "var"; XSym "stage0.lower.arg153"]); (XList [XSym "let"; XSym "stage0.lower.arg158"; (XList [XSym "var"; XSym
 "stage0.lower.arg154"]); (XList [XSym "let"; XSym "X"; (XList [XSym "var"; XSym "stage0.lower.arg156"]); (XList [XSym "let"; XSym "Value";
 (XList [XSym "var"; XSym "stage0.lower.arg157"]); (XList [XSym "let"; XSym "Bindings"; (XList [XSym "var"; XSym "stage0.lower.arg158"]);
 (XList [XSym "let"; XSym "stage0.lower.inlining"; (XList [XSym "const"; XSym "shen.bindv"]); (XList [XSym "prim"; XSym "address->"; (XList [(XList
 [XSym "var"; XSym "Bindings"]); (XList [XSym "prim"; XSym "shen-jit.pvar-offset"; (XList [(XList [XSym "var"; XSym "X"])])]); (XList [XSym "var";
 XSym "Value"])])])])])])])])])]); (XList [XSym "let"; XSym "stage0.lower.arg155"; (XList [XSym "let"; XSym "Z5449"; (XList [XSym "var"; XSym
 "W5453"]); (XList [XSym "let"; XSym "Z5450"; (XList [XSym "var"; XSym "W5454"]); (XList [XSym "do"; (XList [XSym "let"; XSym
 "stage0.lower.inlining"; (XList [XSym "const"; XSym "shen.incinfs"]); (XList [XSym "prim"; XSym "set"; (XList [(XList [XSym "const"; XSym
 "shen.*infs*"]); (XList [XSym "prim"; XSym "+"; (XList [(XList [XSym "const"; (XInt (1))]); (XList [XSym "prim"; XSym "value"; (XList [(XList [XSym
 "const"; XSym "shen.*infs*"])])])])])])])]); (XList [XSym "let"; XSym "stage0.lower.arg145"; (XList [XSym "var"; XSym "Z5449"]); (XList
 [XSym "let"; XSym "stage0.lower.arg146"; (XList [XSym "var"; XSym "W5445"]); (XList [XSym "let"; XSym "stage0.lower.arg147"; (XList [XSym
 "var"; XSym "V5357"]); (XList [XSym "let"; XSym "stage0.lower.arg148"; (XList [XSym "var"; XSym "V5358"]); (XList [XSym "let"; XSym
 "stage0.lower.arg149"; (XList [XSym "var"; XSym "W5361"]); (XList [XSym "let"; XSym "stage0.lower.arg150"; (XList [XSym "freeze"; (XList [XSym
 "call"; XSym "shen.l-rules"; (XList [(XList [XSym "var"; XSym "W5446"]); (XList [XSym "var"; XSym "Z5450"]); (XList [XSym "var"; XSym "V5356"]);
 (XList [XSym "var"; XSym "V5357"]); (XList [XSym "var"; XSym "V5358"]); (XList [XSym "var"; XSym "W5361"]); (XList [XSym "var"; XSym
 "V5360"])])])]); (XList [XSym "let"; XSym "V2236"; (XList [XSym "var"; XSym "stage0.lower.arg145"]); (XList [XSym "let"; XSym "V2237"; (XList
 [XSym "var"; XSym "stage0.lower.arg146"]); (XList [XSym "let"; XSym "V2238"; (XList [XSym "var"; XSym "stage0.lower.arg147"]); (XList [XSym
 "let"; XSym "V2239"; (XList [XSym "var"; XSym "stage0.lower.arg148"]); (XList [XSym "let"; XSym "V2240"; (XList [XSym "var"; XSym
 "stage0.lower.arg149"]); (XList [XSym "let"; XSym "V2241"; (XList [XSym "var"; XSym "stage0.lower.arg150"]); (XList [XSym "let"; XSym
 "stage0.lower.inlining"; (XList [XSym "const"; XSym "bind"]); (XList [XSym "call"; XSym "shen.bind!"; (XList [(XList [XSym "var"; XSym
 "V2236"]); (XList [XSym "var"; XSym "V2237"]); (XList [XSym "var"; XSym "V2238"]); (XList [XSym "var"; XSym
 "V2241"])])])])])])])])])])])])])])])])])])]); (XList [XSym "if"; (XList [XSym "prim"; XSym "="; (XList [(XList [XSym "var"; XSym
 "stage0.lower.arg155"]); (XList [XSym "const"; XSym "false"])])]); (XList [XSym "let"; XSym "stage0.lower.arg159"; (XList [XSym "var";
 XSym "stage0.lower.arg152"]); (XList [XSym "let"; XSym "stage0.lower.arg160"; (XList [XSym "var"; XSym "stage0.lower.arg154"]); (XList
 [XSym "let"; XSym "stage0.lower.arg161"; (XList [XSym "var"; XSym "stage0.lower.arg155"]); (XList [XSym "let"; XSym "X"; (XList [XSym "var";
 XSym "stage0.lower.arg159"]); (XList [XSym "let"; XSym "Bindings"; (XList [XSym "var"; XSym "stage0.lower.arg160"]); (XList [XSym "let"; XSym
 "Compute"; (XList [XSym "var"; XSym "stage0.lower.arg161"]); (XList [XSym "let"; XSym "stage0.lower.inlining"; (XList [XSym "const"; XSym
 "shen.unwind"]); (XList [XSym "do"; (XList [XSym "prim"; XSym "address->"; (XList [(XList [XSym "var"; XSym "Bindings"]); (XList [XSym "prim"; XSym
 "shen-jit.pvar-offset"; (XList [(XList [XSym "var"; XSym "X"])])]); (XList [XSym "const"; XSym "shen.-null-"])])]); (XList [XSym "var"; XSym
 "Compute"])])])])])])])])]); (XList [XSym "var"; XSym "stage0.lower.arg155"])])])])])])])]).

Definition bind_real : option (list name * expr) :=
 match decode_entry bind_norm with Some (_, ps, n) => option_map (fun e => (ps, e)) (erase ps n) | None => None end.
Definition lrules_site : option expr :=
 match decode_entry lrules_site_norm with Some (_, ps, n) => erase ps n | None => None end.
(* e_B calls neither shen.bindv nor shen.unwind: both bodies are inlined (their markers erased). *)
Example bind_real_inlined :
 option_map (fun p => existsb (fun f => text_eqb f bindv_name || text_eqb f unwind_name) (calls (snd p))) bind_real = Some false.
Proof. vm_compute. reflexivity. Qed.
(* The real site against the real e_B, with the kernel's do (letdo): accepted. *)
Example site_bind_real : match bind_real, lrules_site with
 | Some (ps, eB), Some e => match bind_args e with
   | Some a => bind_site false [(bind_name, FUser ps eB); (do_name, FUser [nm "A"; nm "B"] (v "B"))] a e
   | None => false end
 | _, _ => false end = true.
Proof. vm_compute. reflexivity. Qed.

(* inl_eq's hidden-name check is the only guard against a thawed-in-place argument captured by a
   binder inside N (frozen_free covers only the expansion's own lets): callee (let Y 1 (thaw K)),
   argument (freeze Y), expansion (let Y 1 Y). The same with Z, which no binder hides, passes. *)
Definition D_hid : list (name * fundef) := [(nm "h", FUser [nm "K"] (ELet (nm "Y") (ENum (NInt 1)) (EApp (v "K") [])))].
Example site_frozen_hidden : inl_site false false D_hid (nm "h") [EFreeze (v "Y")] (ELet (nm "Y") (ENum (NInt 1)) (v "Y")) = false.
Proof. vm_compute. reflexivity. Qed.
Example site_frozen_visible : inl_site false false D_hid (nm "h") [EFreeze (v "Z")] (ELet (nm "Y") (ENum (NInt 1)) (v "Z")) = true.
Proof. vm_compute. reflexivity. Qed.

(* Interface item 1, on real data (stage 0's shen.partial-parse-failure?, whose witness inlines
   shen.in->): the lowered body binds stage0.lower.arg1, so JitKRef.fresh_ok on the lowered D
   bodies fails, while the source body passes. *)
Definition ppf_form : sx := XList [XSym "defun"; XSym "shen.partial-parse-failure?"; XList [XSym "V127"];
 XList [XSym "cons?"; XList [XSym "shen.in->"; XSym "V127"]]].
Definition ppf_norm : sx := XList [XSym "shen.partial-parse-failure?"; XList [XSym "V127"];
 XList [XSym "prim"; XSym "cons?"; XList [XList [XSym "let"; XSym "stage0.lower.arg1"; XList [XSym "var"; XSym "V127"];
  XList [XSym "let"; XSym "V393"; XList [XSym "var"; XSym "stage0.lower.arg1"];
   XList [XSym "let"; XSym "stage0.lower.inlining"; XList [XSym "const"; XSym "shen.in->"];
    XList [XSym "prim"; XSym "hd"; XList [XList [XSym "var"; XSym "V393"]]]]]]]]].
Definition ppf_low : option expr := match decode_entry ppf_norm with Some (_, ps, n) => erase ps n | None => None end.
Definition ppf_src : option expr := match parse [] (to_value ppf_form) with Some (EDefun _ _ b) => Some b | _ => None end.
Example fresh_ok_lowered_fails :
 option_map (fun e => K.fresh_ok K.ns_stage0 [e]) ppf_low = Some false /\
 option_map (fun e => K.fresh_ok K.ns_stage0 [e]) ppf_src = Some true.
Proof. vm_compute. split; reflexivity. Qed.
End JitFrontD.
