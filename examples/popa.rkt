#lang racket
(require esterel/front-end (for-syntax syntax/parse racket/syntax racket/sequence))
(module+ test (require "test-harness.rkt"))

(define-esterel-form with-queries&
  (syntax-parser
    [(_ history:msg
        (T:id ...)
        (query:expr ...)
        body:expr ...)
     (define/with-syntax (T_send ...) (generate-temporaries #'(T ...)))
     (define/with-syntax (T& ...)
       (for/list ([id (in-syntax #'(T ...))])
         (syntax-property (format-id id "~a&" id #:source id) 'original-for-check-syntax #t)))
     #'(signal&
        (T_send ...)
        (par&
         (let ([T& (present& history nothing& (emit& T_send))] ...
               [T T_send] ...)
           (par& query ...))
         (suspend&
          history
          (present& history pause&)
          (signal&
           (T ...)
           (par&
            (seq& body ...)
            (par&
             (loop&
              (present& T_send (emit& T))
              pause&)
             ...))))))]))

(define-esterel-form query&
  (syntax-parser
    [(_ x:msg
        #:except z:msg
        #:times times:nat
        #:apart apart:nat h:msg
        #:emit emit:expr
        #:auto-restart auto:boolean)
     #`(loop-each&
        z
        (#,(if (syntax-e #'auto) #'loop& #'values)
         #,@(for/list ([_ (sub1 (syntax-e #'times))])
              #`(seq&
                 (await& x)
                 #,@(for/list ([_ (syntax-e #'apart)]) #'(await& h))))
         (await& x)
         emit))]))

(define popa
  (esterel-machine
   #:inputs (pulse-ox<92
             vital-sign-recording
             painscore>8 painscore<3
             painscore<8 painscore>3
             hour minute history)
   #:outputs (start set increase check-painscore decrease notify-doctor)
   (with-queries&
     history (painscore-trend-up painscore-trend-down)
     [(query&
       painscore>8
       #:except painscore<8
       ;;(or notify-doctor) we dont need this anymore! Would be more complicated
       ;; if we wanted the other behavior we could use sustain&
       #:times 3
       #:apart 1 hour
       #:emit painscore-trend-up&
       #:auto-restart #t)
      (query&
       painscore<3
       #:except painscore>3
       #:times 3
       #:apart 1 hour
       #:emit painscore-trend-down&
       #:auto-restart #t)]
     (seq&
      ;; initially
      start&
      set&
      (par&
       ;; breakthrough
       (par&
        ;; this even implicitly handles "ignoring" extrainious values
        (every& painscore>8
                increase&
                (await& 59 minute);; /grumble off by 1
                check-painscore&)
        (every& painscore-trend-up notify-doctor&))
       ;; minimal
       (every& painscore-trend-down decrease&)
       ;; monitoring
       (par&
        (every& vital-sign-recording check-painscore&)
        (every& pulse-ox<92 notify-doctor&)))))))


(module+ test
  (test-seq
   popa
   #:equivalence ([hour => 60 minute]
                  [painscore>8 => 1 painscore>3]
                  [painscore<3 => 1 painscore<8])
   ([] [start set])
   ([painscore>8] [increase])
   ([hour] [check-painscore])
   ([painscore<3] [])
   ([painscore<3] [])
   ([painscore<3] [])
   ([hour] [])
   ([hour] [])
   ([painscore<3] [])
   ([hour] [])
   ([hour] [])
   ([painscore<3] [decrease]))
  (test-seq
   popa
   #:equivalence ([hour => 60 minute]
                  [painscore>8 => 1 painscore>3]
                  [painscore<3 => 1 painscore<8])
   ([] [start set])
   ([vital-sign-recording] [check-painscore])
   ([pulse-ox<92] [notify-doctor]))
  (test-seq
   popa
   #:equivalence ([hour => 60 minute]
                  [painscore>8 => 1 painscore>3]
                  [painscore<3 => 1 painscore<8])

   ([] [start set])
   ([painscore>8] [increase])
   ([hour] [check-painscore])
   ([painscore<3] [])
   ([painscore<3] [])
   ([painscore<3] [])
   ([hour] [])
   ([hour] [])
   ([painscore<3] [])
   ([hour] [])
   ([hour] [])
   ([painscore<3] [decrease])
   ([painscore<3] [])
   ([painscore<3] [])
   ([painscore<3] [])
   ([hour] [])
   ([hour] [])
   ([painscore<3] [])
   ([hour] [])
   ([hour] [])
   ([painscore<3] [decrease])
   ([painscore<3] [])
   ([painscore<3] [])
   ([painscore<3] [])
   ([hour] [])
   ([hour] [])
   ([painscore<3] [])
   ([hour] [])
   ([hour] [])
   ([painscore<3] [decrease])))
