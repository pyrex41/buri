;;; Dump the exact machine-code bytes of one compiled SBCL function, its code
;;; component constants, and the SBCL disassembler listing (the listing is a
;;; reading aid only; the bytes are the artifact).
(in-package :cl-user)

(defun buri-hex (n w) (format nil "~v,'0x" w n))

(defun buri-dump-fun (fname out-prefix)
  (let* ((f (fdefinition fname))
         (code (sb-kernel:fun-code-header f))
         (insts (sb-kernel:code-instructions code))
         (start (sb-sys:sap-int insts))
         (size (sb-kernel:%code-text-size code))
         (entries (loop for i below (sb-kernel:code-n-entries code)
                        collect (sb-kernel:%code-entry-point code i))))
    (with-open-file (o (concatenate 'string out-prefix ".hex")
                       :direction :output :if-exists :supersede)
      (format o "# sbcl ~a ~a code-component text bytes~%"
              (lisp-implementation-version) (machine-type))
      (format o "# function ~s~%# text-start #x~x size ~d~%" fname start size)
      (dolist (e entries)
        (format o "# simple-fun ~s entry offset ~d (address #x~x)~%"
                (sb-kernel:%simple-fun-name e)
                (- (sb-sys:sap-int (sb-vm::simple-fun-entry-sap e)) start)
                (sb-sys:sap-int (sb-vm::simple-fun-entry-sap e))))
      (loop for off from 0 below size by 4
            do (format o "~a ~a~%" (buri-hex off 4)
                       (buri-hex (sb-sys:sap-ref-32 insts off) 8))))
    (with-open-file (o (concatenate 'string out-prefix ".bin")
                       :direction :output :if-exists :supersede
                       :element-type '(unsigned-byte 8))
      (dotimes (i size) (write-byte (sb-sys:sap-ref-8 insts i) o)))
    (with-open-file (o (concatenate 'string out-prefix ".constants")
                       :direction :output :if-exists :supersede)
      (loop for i from sb-vm:code-constants-offset
              below (sb-kernel:code-header-words code)
            do (format o "~d ~s~%" i (sb-kernel:code-header-ref code i))))
    (with-open-file (o (concatenate 'string out-prefix ".sbcl-disasm")
                       :direction :output :if-exists :supersede)
      (let ((*standard-output* o))
        (sb-disassem:disassemble-code-component code)))
    (with-open-file (o (concatenate 'string out-prefix ".policy")
                       :direction :output :if-exists :supersede)
      (let ((*standard-output* o)) (sb-ext:describe-compiler-policy)))
    (list :start start :size size :entries (length entries))))
