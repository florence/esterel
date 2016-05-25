#lang racket
(module* cos racket
  (require esterel/cos-front-end redex/reduction-semantics)
  (define abro-machine
    (esterel-machine
     #:inputs (A B R) #:outputs (O)
     (loop-each&
      R
      (seq& (par& (await& A) (await& B))
            (emit& O)))))

  (pretty-print (machine-prog abro-machine))
  (eval-top abro-machine '(A)))

(module* cbs racket
  (require esterel/front-end
           (for-syntax racket))

  (define abro-machine
    (esterel-machine
     #:inputs (A B R) #:outputs (O)
     (loop-each&
      R
      (seq& (par& (await& A) (await& B))
            (emit& O)))))
  ;(pretty-print (machine-prog abro-machine))

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
     ((A B R) ()))))
