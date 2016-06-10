#lang racket
(module* cos racket
  (require esterel/cos-front-end (for-syntax syntax/parse racket/syntax))
  (define-esterel-form after&
    (syntax-parser
      [(_ n:nat S body ...)
       #'(seq& (await& n S) body ...)]
      [(_ S body ...)
       #'(seq& (await& S) body ...)]))
  (define heparin
    (esterel-machine
     #:inputs ((aptt 0) ;; in seconds
               hour
               minute)
     #:outputs ((give-bolus 0)
                (increase 0)
                (decrease 0)
                check-aptt
                start
                hold
                restart)
     (par&
      ;; the initially
      (seq& (emit& start) (emit& give-bolus 20))
      ;; infusion
      (par&
       (loop-each& check-aptt
                   (await& aptt)
                   pause&
                   (loop&
                    (present& aptt (emit& bad-aptt))
                    pause&))
       (loop&
        (await& aptt)
        (cond& [(< (? aptt) 45) (emit& give-bolus 10) (emit& increase 3)]
               [(<= 45 (? aptt) 59) (emit& give-bolus 5) (emit& increase 1) ]
               [(<= 59 (? aptt) 101) nothing&]
               [(<= 101 (? aptt) 123) (emit& decrease 1)]
               [(< 123 (? aptt))
                (emit& hold)
                (after& 59 minute
                        (emit& restart)
                        (emit& decrease 3))])
        (await& check-aptt)))
      ;; monitoring
      (signal&
       theraputic
       (par&
        (loop-each&
         aptt
         ;; TODO how?
         (await& 2 aptt-59-101)
         (sustain& theraputic))

        ;; this probably has the wrong behavior
        ;; IF check-aptt is also an input signal
        (loop&
         (trap& checking
                (par& (seq& (await& check-aptt) (exit& checking))
                      (loop&
                       (present& theraputic nothing& (emit& check-aptt))
                       (await& 6 hour));; should actually be 6*60 minutes?
                      (loop&
                       (present& theraputic (emit& check-aptt))
                       (await& 24 hour))))))))))
  (define mach (machine-prog heparin))
  (require esterel/cos-model redex/reduction-semantics)
  (time
   (eval-top heparin '((aptt 10))))
  )
(module* cbs racket
  (require esterel/front-end (for-syntax syntax/parse racket/syntax))
  (module+ test (require "test-harness.rkt"))

  ;; like par& but exits when any of the parallel branches finishes
  (define-esterel-form any&
    (syntax-parser
      [(_ body ...)
       (define/with-syntax T (generate-temporary 'any-trap))
       #'(trap& T
                (par&
                 (seq& body (exit& T)) ...))]))

  (define-esterel-form after&
    (syntax-parser
      [(_ n:nat S body ...)
       #'(seq& (await& n S) body ...)]
      [(_ S body ...)
       #'(seq& (await& S) body ...)]))

  ;; like loop each but doesnt suspend on S to avoid causality cycles
  (define-esterel-form loop-each/no-suspend&
    (syntax-parser
      [(_ S body ...)
       #'(loop&
          (trap& K
                 (par&
                  (loop& (await& S) (exit& K))
                  (seq& body ... halt&))))]))

  (define heparin
    (esterel-machine
     #:inputs (aptt<45 aptt-45-59 aptt-59-101 aptt-101-123 aptt>123
                       hour minute)
     #:outputs (give-bolus increase decrease check-aptt hold restart start bad-aptt)
     (par&
      ;; initially
      (seq& start& give-bolus&)
      ;; infusion
      (par&
       (loop-each& check-aptt
                   (await& (or aptt<45 aptt-45-59 aptt-59-101 aptt-101-123 aptt>123))
                   pause&
                   (loop&
                    (present& (or aptt<45 aptt-45-59 aptt-59-101 aptt-101-123 aptt>123)
                              (emit& bad-aptt))
                    pause&))
       ;; i dont know what the behavior on duplicate check-aptt signals should be
       ;; so, uh, i picked one.
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
                 (after& 59 minute
                         restart&
                         decrease&)))
        (await& check-aptt)))
      ;; checking
      (signal&
       theraputic
       (par&
        (loop-each&
         (or aptt<45 aptt-45-59 aptt-101-123 aptt>123)
         (await& 2 aptt-59-101)
         (sustain& theraputic))

        ;; this probably has the wrong behavior
        ;; IF check-aptt is also an input signal
        (loop&
         (trap& checking
                (par& (seq& (await& check-aptt) (exit& checking))
                      (loop&
                       (present& theraputic nothing& check-aptt&)
                       (await& 6 hour));; should actually be 6*60 minutes?
                      (loop&
                       (present& theraputic check-aptt&)
                       (await& 24 hour))))))))))


  (module+ test
    (test-seq
     heparin
     #:equivalence ([hour => 60 minute])
     (() (start give-bolus check-aptt))
     ((aptt-59-101) ())
     ((aptt-101-123) (bad-aptt)))

    (test-seq
     heparin
     #:equivalence ([hour => 60 minute])
     (() (start give-bolus check-aptt))
     ((aptt>123) (hold))
     ((hour) (restart decrease))
     ((aptt>123) (bad-aptt)))

    (test-seq
     heparin
     #:equivalence ([hour => 60 minute])
     (() (start give-bolus check-aptt))
     ((aptt>123) (hold))
     ((hour) (restart decrease)))

    (test-seq
     heparin
     #:equivalence ([hour => 60 minute])
     (() (start give-bolus check-aptt))
     ((aptt<45) (give-bolus increase))
     ;; 6 hours
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) (check-aptt))
     ((aptt-101-123) (decrease))
     ;; 6 hours
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) (check-aptt))
     ((aptt-59-101) ())
     ;; 6 hours
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) (check-aptt))
     ((aptt-59-101) ())
     ;; 24 hours
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) (check-aptt))
     ((aptt-59-101) ())
     ;; 24 hours
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) (check-aptt))
     ((aptt>123) (hold))
     ((hour) (restart decrease))
     ;; 5 hours
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) (check-aptt))
     ((aptt-59-101) ())
     ;; 6 horus
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) (check-aptt))
     ((aptt-59-101) ())
     ;; 24 hours
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) ())
     ((hour) (check-aptt)))

    (test-seq
     heparin
     #:equivalence ([hour => 60 minute])
     (() (start give-bolus check-aptt))
     ((aptt>123) (hold))
     ((aptt>123) (bad-aptt))
     ((hour) (restart decrease)))))
