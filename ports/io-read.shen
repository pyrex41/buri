(tc -)
(define read-file-as-string
  Filename -> ((foreign scm.read-file-as-string) ((foreign scm.string-append) (value *home-directory*) Filename)))
