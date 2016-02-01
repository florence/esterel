#lang racket
(require esterel/front-end
         (for-syntax racket))

(define abro-machine
  (esterel-machine
   #:inputs (A B R) #:outputs (O)
   (loop-each&
    R
    (seq& (par& (await& A) (await& B))
          (emit& O)))))
#;
(pretty-print (machine-prog abro-machine))

(module+ test
  (require rackunit "test-harness.rkt")
  (test-seq
   abro-machine
   (() ())
   ((A) ())
   ((B) (O))
   ((A) ())
   ((R) ())
   ((B) ())
   ((A B) (O))
   ((A B R) ())))
