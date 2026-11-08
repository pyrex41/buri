\\ Pass capture for the Shen/JIT lowerer (wave 1a of the pass split, spikes/pass-split/CENSUS.md).
\\
\\ For every defun of the stage 0 input it records what the lowerer's two front
\\ passes produced, as untrusted witnesses for Rocq to check later:
\\
\\   S = (share Body)                  the KLambda after chain factorisation
\\   N = (norm Params S)               the normal form
\\   C = (code F Params N Sealed) ++ [(inline-form F Params Body)]
\\
\\ and checks that [defun F C], printed, is byte-identical to the stored stage 0
\\ line. Driven by tests/shen-jit/capture_passes.sh, which states the witness
\\ formats; run from an empty scratch directory (it writes only under OUT-DIR):
\\
\\   HOST script capture_passes.shen SJ-DIR LOWER OUT-DIR MODE FILE ...
\\
\\ SJ-DIR is the pinned Shen/JIT checkout (with .deps/kernel/klambda/,
\\ build/port/lower.kl and build/stage0/). LOWER is the lowerer to load: the
\\ build's own build/tools/lower.shen for witnesses, or an instrumented copy
\\ for MODE count. FILE names omit .kl.
\\
\\ How stage 0 is produced is reproduced, not reinvented: src/lowerer/stage0.shen
\\ loads src/lowerer/host.shen and build/tools/lower.shen (lower.shen with
\\ shen-jit.lower. renamed stage0.lower.), reads the 22 kernel files, the port
\\ and the lowerer unprocessed, drops kernel defuns the port overrides, seals
\\ every remaining defun name, sets the host's sealed and inline tables from all
\\ of them, and lowers each defun with stage0.lower.defun. stage0.shen itself is
\\ not loaded: its last form runs the build and writes build/stage0/. The
\\ functions below marked "as stage0.shen" are copies of its definitions.

(set *hush* true)
\\ Under Shen/JIT shen-jit.symbol? is a primitive the kernel's arity table
\\ does not list (tests/shen-jit/capture.shen does the same); host.shen
\\ defines it elsewhere.
(put shen-jit.symbol? arity 1)
(set pc.argv (value *argv*))
(set pc.sj (hd (tl (value pc.argv))))
(load (cn (value pc.sj) "/src/lowerer/host.shen"))
(set *hush* false)

\\ ---------------------------------------------------------------------------
\\ Rewrite counters, for MODE count with an instrumented lowerer that calls
\\ (pc.tick Key). Reset per definition.

(define pc.tick
  K -> (let Entry (assoc K (value pc.ticks))
         (set pc.ticks (if (empty? Entry)
                           [[K | 1] | (value pc.ticks)]
                           [[K | (+ 1 (tl Entry))] | (pc.drop K (value pc.ticks))]))))

(define pc.drop
  _ [] -> []
  K [[K | _] | R] -> R
  K [E | R] -> [E | (pc.drop K R)])

(define pc.pairs
  [] -> []
  [[K | N] | R] -> [[K N] | (pc.pairs R)])

(set *hush* true)
(load (hd (tl (tl (value pc.argv)))))
(set *hush* false)

\\ As stage0.shen.
(define pc.files
  -> ["toplevel" "core" "sys" "dict" "sequent" "yacc" "reader" "prolog" "track" "load"
      "writer" "macros" "declarations" "types" "t-star" "init"
      "extension-features" "extension-launcher" "extension-programmable-pattern-matching"
      "extension-namespaces" "extension-expand-dynamic" "extension-type-annotations"])

\\ As stage0.shen's kernel-inputs, with the default paths made absolute.
(define pc.inputs
  Sj -> (append (map (/. F [F (cn Sj (cn "/.deps/kernel/klambda/" (cn F ".kl")))]) (pc.files))
                [["shen-jit" (cn Sj "/src/port/shen-jit.kl")] ["lower" (cn Sj "/build/port/lower.kl")]]))

\\ As stage0.shen's select-overrides, defun-signature, omit, defun-names, defun-name.
(define pc.select-overrides
  Inputs -> (let Port (mapcan (/. I (if (= (hd I) "shen-jit") (tl I) [])) Inputs)
                 Overrides (mapcan (/. X (pc.defun-signature X)) Port)
              (map (/. I (if (= (hd I) "shen-jit")
                             I
                             [(hd I) | (pc.omit Overrides (tl I))]))
                   Inputs)))

(define pc.defun-signature
  [defun F Params | _] -> [[F | (length Params)]]
  _ -> [])

(define pc.omit
  _ [] -> []
  Overrides [[defun F Params | Body] | Forms]
  -> (let Entry (assoc F Overrides)
       (cond ((empty? Entry) [[defun F Params | Body] | (pc.omit Overrides Forms)])
             ((= (tl Entry) (length Params)) (pc.omit Overrides Forms))
             (true (simple-error (make-string "override of ~A changes its parameter count" F)))))
  Overrides [X | Forms] -> [X | (pc.omit Overrides Forms)])

(define pc.defun-names
  Inputs -> (mapcan (/. I (mapcan (/. X (pc.defun-name X)) (tl I))) Inputs))

(define pc.defun-name
  [defun F | _] -> [F]
  _ -> [])

\\ ---------------------------------------------------------------------------
\\ Printing, as stage0.shen's write, write-rest, write-string, write-bytes,
\\ escape, hex, symbol-name, plain?, numeric?, digit?.

(define pc.write
  S [] -> (pr "()" S)
  S [X | Xs] -> (do (pr "(" S) (pc.write S X) (pc.write-rest S Xs))
  S X -> (pc.write-string S X) where (string? X)
  S X -> (pr (str X) S) where (or (number? X) (boolean? X))
  S X -> (pr (pc.symbol-name X) S) where (symbol? X)
  _ X -> (simple-error (make-string "stage 0: cannot print ~S" X)))

(define pc.write-rest
  S [] -> (pr ")" S)
  S [X | Xs] -> (do (pr " " S) (pc.write S X) (pc.write-rest S Xs))
  _ X -> (simple-error (make-string "stage 0: improper list ending in ~S" X)))

(define pc.write-string
  S X -> (do (pr (n->string 34) S) (pc.write-bytes S X) (pr (n->string 34) S)))

(define pc.write-bytes
  _ "" -> skip
  S (@s C Cs) -> (do (pr (pc.escape (string->n C)) S)
                     (pc.write-bytes S Cs)))

(define pc.escape
  N -> (cn (n->string 92) (n->string N)) where (or (= N 34) (= N 92))
  N -> (n->string N) where (and (>= N 32) (<= N 126))
  N -> (cn (n->string 92) (cn "x" (pc.hex N 0))) where (< N 256)
  N -> (simple-error (make-string "stage 0: character ~A is not a byte" N)))

(define pc.hex
  N High -> (pc.hex (- N 16) (+ High 1)) where (>= N 16)
  N High -> (cn (pos "0123456789abcdef" High) (pos "0123456789abcdef" N)))

(define pc.symbol-name
  X -> (let Name (str X)
         (if (and (pc.plain? Name) (not (pc.numeric? Name)))
             Name
             (simple-error (make-string "stage 0: symbol ~A cannot be printed plainly" Name)))))

(define pc.plain?
  "" -> true
  (@s C Cs) -> (let N (string->n C)
                 (and (> N 32) (< N 127) (not (element? C ["(" ")" "c#34;" "c#92;"]))
                      (pc.plain? Cs))))

(define pc.numeric?
  (@s C _) -> true where (pc.digit? C)
  (@s C D _) -> (pc.digit? D) where (element? C ["-" "+" "."])
  _ -> false)

(define pc.digit?
  C -> (let N (string->n C) (and (>= N 48) (<= N 57))))

(define pc.line
  S X -> (do (pc.write S X) (pr (n->string 10) S)))

\\ ---------------------------------------------------------------------------
\\ Erasure of a normal form back to KLambda, for the census only (untrusted).
\\ Flags, set per definition: folded (a [const V] with V a cons), shadow (a
\\ constant symbol bound in scope, which erasure would turn into a variable),
\\ applyhead (an [apply F ...] whose F erases to a symbol not in scope, which
\\ erasure would turn into a named call), callshadow (a [call F ...] with F in
\\ scope, which erasure would turn into a dynamic application). With
\\ pc.transparent (for <f>.tforms) the inlining marker
\\ (let stage0.lower.inlining (const F) Body) erases to Body alone, as emission
\\ treats it at stage 0 (lower.shen, mark); otherwise to a let of the symbol F.

(define pc.flag
  K -> (set pc.flags (if (element? K (value pc.flags)) (value pc.flags) [K | (value pc.flags)])))

(define pc.erase
  Sc [const V] -> (pc.erase-const Sc V)
  _ [var X] -> X
  Sc [if C X Y] -> [if (pc.erase Sc C) (pc.erase Sc X) (pc.erase Sc Y)]
  Sc [and X Y] -> [and (pc.erase Sc X) (pc.erase Sc Y)]
  Sc [or X Y] -> [or (pc.erase Sc X) (pc.erase Sc Y)]
  Sc [let stage0.lower.inlining [const _] B] -> (pc.erase Sc B) where (value pc.transparent)
  Sc [let X V B] -> [let X (pc.erase Sc V) (pc.erase [X | Sc] B)]
  Sc [do X Y] -> [do (pc.erase Sc X) (pc.erase Sc Y)]
  Sc [lambda X B] -> [lambda X (pc.erase [X | Sc] B)]
  Sc [freeze B] -> [freeze (pc.erase Sc B)]
  Sc [prim F As] -> [F | (map (/. A (pc.erase Sc A)) As)]
  Sc [call F As] -> (do (if (element? F Sc) (pc.flag callshadow) skip)
                        [F | (map (/. A (pc.erase Sc A)) As)])
  Sc [apply F] -> [thaw (pc.erase Sc F)]
  Sc [apply F X] -> (let G (pc.erase Sc F)
                      (do (if (and (symbol? G) (not (element? G Sc))) (pc.flag applyhead) skip)
                          [G (pc.erase Sc X)]))
  Sc [trap X E H] -> [trap-error (pc.erase Sc X) [lambda E (pc.erase [E | Sc] H)]]
  _ X -> (simple-error (make-string "capture: not a normal form ~S" X)))

(define pc.erase-const
  Sc V -> (do (pc.flag folded) (pc.cons-chain Sc V)) where (cons? V)
  Sc V -> (do (pc.flag shadow) V) where (element? V Sc)
  _ V -> V)

(define pc.cons-chain
  _ [] -> []
  Sc [A | B] -> [cons (pc.erase-const Sc A) (pc.cons-chain Sc B)])

\\ Facts about N for the census: whether it mentions shen-jit.inlined?, the
\\ inlining marker, and binders the lowerer made (stage0.lower.<prefix><n>).
(define pc.facts
  [prim shen-jit.inlined? _] -> (pc.flag inlined?)
  [let stage0.lower.inlining _ B] -> (do (pc.flag inlining-marker) (pc.facts B))
  [let X V B] -> (do (pc.fresh-binder X) (pc.facts V) (pc.facts B))
  [lambda X B] -> (do (pc.fresh-binder X) (pc.facts B))
  [trap X E H] -> (do (pc.fresh-binder E) (pc.facts X) (pc.facts H))
  [const _] -> skip
  [X | Xs] -> (do (pc.facts X) (pc.facts Xs))
  _ -> skip)

(define pc.fresh-binder
  X -> (if (pc.prefix? "stage0.lower." (str X)) (pc.flag fresh) skip))

(define pc.prefix?
  "" _ -> true
  (@s C P) (@s C S) -> (pc.prefix? P S)
  _ _ -> false)

\\ ---------------------------------------------------------------------------
\\ One definition, as stage0.lower.defun does it: check, reset both globals,
\\ then share, norm, code and inline-form in that order (KLambda evaluates
\\ arguments left to right, so share runs before norm, and the fresh counter
\\ carries through all three).

(define pc.lower-one
  [defun F Params Body] Sealed
  -> (do (stage0.lower.check-defun F Params Sealed)
         (set stage0.lower.*inline-depth* 0)
         (set stage0.lower.*fresh* 0)
         (set pc.ticks [])
         (let S (stage0.lower.share Body)
              N (stage0.lower.norm Params S)
              C (stage0.lower.code F Params N Sealed)
              I (stage0.lower.inline-form F Params Body)
           [S N [defun F (append C [I])]])))

(define pc.open-out
  Out Name Ext -> (open (cn Out (cn Name Ext)) out))

(define pc.run-file
  Mode Out Name Defuns Sealed
  -> (let Sbc (pc.open-out Out Name ".sbc")
          Frm (pc.open-out Out Name ".forms")
          Shr (if (= Mode witness) (pc.open-out Out Name ".share") skip)
          Nrm (if (= Mode witness) (pc.open-out Out Name ".norm") skip)
          Nfm (if (= Mode witness) (pc.open-out Out Name ".nforms") skip)
          Tfm (if (= Mode witness) (pc.open-out Out Name ".tforms") skip)
          Cen (pc.open-out Out Name (if (= Mode witness) ".ncensus" ".ticks"))
          Done (map (/. D (pc.emit Mode D (pc.lower-one D Sealed) Sbc Frm Shr Nrm Nfm Tfm Cen)) Defuns)
       (do (close Sbc) (close Frm) (close Cen)
           (if (= Mode witness) (do (close Shr) (close Nrm) (close Nfm) (close Tfm)) skip)
           (output "~A: ~A definitions~%" Name (length Done)))))

(define pc.emit
  Mode [defun F Params Body] [S N Code] Sbc Frm Shr Nrm Nfm Tfm Cen
  -> (do (pc.line Sbc Code)
         (pc.line Frm [defun F Params Body])
         (if (= Mode witness)
             (do (pc.line Shr [defun F Params S])
                 (pc.line Nrm [F Params N])
                 (set pc.flags [])
                 (pc.facts N)
                 (set pc.transparent false)
                 (pc.line Nfm [defun F Params (pc.erase Params N)])
                 (set pc.transparent true)
                 (pc.line Tfm [defun F Params (pc.erase Params N)])
                 (pc.line Cen [F (reverse (value pc.flags))]))
             (pc.line Cen [F (pc.pairs (reverse (value pc.ticks)))]))))

(define pc.main
  [_ Sj _ Out Mode | Files]
  -> (let Read (map (/. F [(hd F) | (read-from-string-unprocessed (read-file-as-string (hd (tl F))))])
                    (pc.inputs Sj))
          Inputs (pc.select-overrides Read)
          Sealed (pc.defun-names Inputs)
          Tables (shen-jit.host.set-tables (mapcan (/. I (tl I)) Inputs))
          M (intern Mode)
          Want (if (empty? Files) (map (/. I (hd I)) Inputs) Files)
       (do (output "sealed: ~A names~%" (length Sealed))
           (map (/. I (if (element? (hd I) Want)
                          (pc.run-file M Out (hd I) (stage0.filter (/. X (cons? X)) (tl I)) Sealed)
                          skip))
                Inputs)
           (output "capture done~%"))))

(pc.main (value pc.argv))
