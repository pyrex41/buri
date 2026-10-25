\\ Exact nonrecursive pass from tizoc/shen-scheme src/compiler.shen,
\\ commit 8d261518db17fbfec32d1b268b40ed216b925c74, blob 42ac753b8f305c578998b74693fc85b28112a814.
\\ Copyright (c) 2012-2021 Bruno Deferrari. BSD-3-Clause.
\\ Only the package-qualified entry name is made explicit below.
(tc -)
(define _scm.merge-nested-lets
  [let [Binding] [let* Bindings Body]] -> [let* [Binding | Bindings] Body]
  [let [Binding1] [let [Binding2] Body]] -> [let* [Binding1 Binding2] Body]
  X -> X)
