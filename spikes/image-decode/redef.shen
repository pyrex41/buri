\* r21-image-lane, OB-JIT-IMAGE-SEALING: test evidence, not proof. Run in buri-lps:
   qemu-riscv64 /lps/p6/sj/build/shen-jit script redef.shen
   Redefines one of the 65 unsealed extension names and reads a sealed call site, an open call
   and sealed? before and after; then tries sealed and fixed names. *\
(define try
  F -> (trap-error (thaw F) (/. E (cn "ERROR: " (error-to-string E)))))
(output "R1 sealed? execute-all before: ~S~%" (shen-jit.sealed? shen.x.launcher.execute-all))
(output "R2 sealed? shen.x.launcher.main: ~S~%" (shen-jit.sealed? shen.x.launcher.main))
(output "R3 caller before: ~S~%" (try (freeze (shen.x.launcher.eval-command-h [] []))))
(output "R4 redefine execute-all: ~S~%" (try (freeze (eval-kl [defun shen.x.launcher.execute-all [X] redefined]))))
(output "R5 open call after: ~S~%" (try (freeze (shen.x.launcher.execute-all []))))
(output "R6 sealed caller after: ~S~%" (try (freeze (shen.x.launcher.eval-command-h [] []))))
(output "R7 sealed? execute-all after: ~S~%" (shen-jit.sealed? shen.x.launcher.execute-all))
(output "R8 redefine sealed shen.x.launcher.main: ~S~%" (try (freeze (eval-kl [defun shen.x.launcher.main [X] redefined]))))
(output "R9 redefine thaw: ~S~%" (try (freeze (eval-kl [defun thaw [X] redefined]))))
(output "R10 redefine hd: ~S~%" (try (freeze (eval-kl [defun hd [X] redefined]))))
(output "R11 hd after: ~S~%" (try (freeze (hd [1 2]))))
(output "R12 redefine tl: ~S~%" (try (freeze (eval-kl [defun tl [X] redefined]))))
(output "R13 tl after: ~S~%" (try (freeze (tl [1 2]))))
(output "R14 sealed? hd tl thaw: ~S ~S ~S~%" (shen-jit.sealed? hd) (shen-jit.sealed? tl) (shen-jit.sealed? thaw))
