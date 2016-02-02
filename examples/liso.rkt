#lang racket
(require esterel/front-end (for-syntax syntax/parse))

(define-esterel-form do-after-n&
  (syntax-parser
    [(_ S_e:id n:nat S_a:id body:expr ...)
     #'(loop-each& S_e (await& n S_a) body ...)]))

(define lisinopril
  (esterel-machine
   #:inputs (weight refill day bp-checked hour between-6-and-8-am took)
   #:outputs (check-weight please-refill please-check-bp please-take)
   (par&
    ;; taking lisinopril
    (signal& over-18-h
             (par&
              (loop-each& took (await& 18 hour) (emit& over-18-h))
              (loop& (present& between-6-and-8-am (present& over-18-h (emit& please-take)))
                     pause&)))
    ;; bp checking
    (loop-each& bp-checked
                (await& 48 hour)
                (emit& please-check-bp))
    ;; refill handling
    (loop-each& refill
                ;; making up a number. must be a const for now
                (await& 23 took)
                (emit& please-refill))
    ;;handle weight checking
    (loop-each& weight
                ;; technically wrong, because we might be close to the
                ;; day boundry when this occurs...
                (await& 3 day)
                (emit& check-weight)))))
