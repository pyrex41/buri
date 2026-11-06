(print (shen-jit.lower.toplevel [defun sp8.f [X Y] [if [cons? X] [cons [hd X] Y] X]] []))
(nl)
(print (shen-jit.lower.toplevel [defun sp8.g [X] [if [cons? X] [hd [tl X]] [cons X []]]] []))
(nl)
