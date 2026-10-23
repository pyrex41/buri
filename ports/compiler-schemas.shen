\\ Fixed trusted schemas. Free names denote arbitrary exact integer inputs.
(tc -)
(define buri.compiler-schemas ->
 [[addition [x y] [+ x y]]
  [subtraction [x y] [- x y]]
  [multiplication [x y] [* x y]]
  [nested [x y z] [+ [* x y] [- z 3]]]
  [let-binding [x y] [let a [+ x 1] [* a y]]]
  [shadowing [x y] [let x [+ x 1] [- x y]]]
  [nested-let [x y] [let a [+ x 1] [let b [* a y] [- b a]]]]
  [shadowed-let [x y] [let x [+ x y] [let x [* x 2] [- x y]]]]
  [left-right [x y z] [- [+ x y] [* y z]]]
  [negative [x] [+ x -17]]
  [large [x] [+ x 9223372036854775808]]
  [unused-binding [x y] [let unused [* x y] [+ x y]]]])
