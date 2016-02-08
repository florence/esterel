#lang racket
(require esterel/front-end)
(module+ test (require "test-harness.rkt"))
;; this should error somehow... right?
(define causality
  (esterel-machine #:inputs () #:outputs (O1 O2)
                   (signal& S
                            (present& S (emit& O1) (emit& O2))
                            (emit& S)
                            (present& S (emit& O1) (emit& O2)))))
(module+ test
  (check-exn
   (lambda ()
     (test-seq
      causality
      (() (O1))))))

(define dependency
  (esterel-machine
   #:inputs (S) #:outputs (O1 O2)
   (signal& R
           (emit& S)
           (present& R (emit& O1) (emit& O2))
           (present& S (emit& R)))))

;; I'm not sure if this is constructive or not...
#;
(module+ test
  (test-seq
   dependency
   (() (O2))))
