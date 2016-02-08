#lang racket
(require esterel/front-end (for-syntax syntax/parse racket/syntax))
(module+ test (require "test-harness.rkt"))

(define-esterel-form any&
  (syntax-parser
    [(_ body ...)
     (define/with-syntax T (generate-temporary 'any-trap))
     #'(trap& T
              (seq& body (exit& T)) ...)]))
(define-esterel-form after&
  (syntax-parser
    [(_ n:nat S body ...)
     #'(seq& (await& n S) body ...)]
    [(_ S body ...)
     #'(seq& (await& S) body ...)]))

(define heparin
  (esterel-machine
   #:inputs (aptt<45 aptt-45-59 aptt-59-101 aptt-101-123 aptt>123
                     hour minute)
   #:outputs (give-bolus increase decrease check-aptt hold restart start bad-aptt)
   (par&
    ;; initially
    (seq& start& give-bolus&)
    ;; infusion
     (signal&
      waiting
      (signal&
       stop-waiting
       (par&
        (loop-each& check-aptt (abort& stop-waiting (sustain& waiting)))
        (loop&
         ;; a bit weird, b/c we are using many signals rather than one value
         ;; carying signal. but we assume all the signals are mutually exclusive
         (any&
          (after& aptt<45 give-bolus& increase&)
          (after& aptt-45-59 give-bolus& increase&)
          (after& aptt-59-101)
          (after& aptt-101-123 decrease&)
          (after& aptt>123
                  hold&
                  (after& 60 minute
                          restart&
                          decrease&)))
         stop-waiting&
         pause&)
        (loop&
         (present& waiting
                   (present& (or aptt<45 aptt-45-59 aptt-59-101 aptt-101-123 aptt>123)
                             bad-aptt&))
         pause&))))
    ;; checking
    (signal&
     theraputic
     (par&
      (loop-each&
       (or aptt<45 aptt-45-59 aptt-101-123 aptt>123)
       (await& 2 aptt-59-101)
       (sustain& theraputic))

      (loop-each& check-aptt
                  (await& 6 hour)
                  (present& theraputic nothing& check-aptt&))

      (loop-each& check-aptt
                  (await& 24 hour)
                  (present& theraputic check-aptt&)))))))


(module+ test
  (test-seq
   heparin
   #:equivalence ([hour => 60 minute])
   (() (start give-bolus check-aptt))
   ((aptt>123) (hold))
   ((hour) (restart decrease))))
