[[define [kl:buri.kernel.element? V5973 V5974] [cond [[null? V5974] false] [[and [pair? V5974] [kl:= V5973 [car V5974]]] true] [[pair? V5974] [kl:buri.kernel.element? V5973 [cdr V5974]]] [true [error [quote buri.kernel.element?] "attempt to find an element in a non-list
"]]]]]
