#lang racket
(provide
 (except-out
  (all-from-out esterel/cos-front-end)
  esterel:await&
  esterel:emit&
  esterel:loop-each&
  esterel:signal&
  esterel:abort&
  esterel:every&
  esterel-machine
  eval-top)
 pop-pl-eval
 pop-pl-machine
 await&
 emit&
 signal&
 loop-each&
 signal&
 abort&
 every&)

(require esterel/cos-front-end
         (prefix-in esterel: esterel/cos-front-end)
         (for-syntax syntax/parse racket/format racket/syntax))


(define-syntax (pop-pl-machine stx)
  (syntax-parse stx
    [(_ #:inputs (i ...)
        #:outputs (o ...)
        body)
     #'(esterel-machine
        #:inputs ((time 0) i ...)
        #:outputs (o ...)
        body)]))

(define (pop-pl-eval in-machine inputs)
  (define inputs/time
    (for/list ([i inputs])
      (match i
        [(list (? time? t) v)
         (list t (* v (time->factor t)))]
        [(? time? t)
         (list t (time->factor t))]
        [else i])))
  (eval-top
   in-machine
   inputs/time))

(define-syntax (def-time-tables stx)
  (syntax-parse stx
    [(_ [time-factor e] time->factor time-msg pred? factor [name factor-expr] ...)
     (define/with-syntax time->factor-def
       #`(define (time->factor x)
           (case x
             [(name) factor-expr] ...)))
     #`(begin
         ;; maps to minutes to the internal heartbeat
         (define time-factor e)
         (define-for-syntax time-factor e)
         time->factor-def
         (define (pred? x)
           (member x '(name ...)))
         (begin-for-syntax
           time->factor-def
           (define-syntax-class time-msg
             #:attributes (factor)
             (pattern
              (~or
               (~literal name) ...)
              #:attr factor (datum->syntax this-syntax (time->factor (syntax-e this-syntax)))))))]))

(def-time-tables
  [time-factor 1]
  time->factor
  time-msg
  time?
  factor
  [time 1]
  [minute time-factor]
  [hour (* 60 (time->factor 'minute))]
  [day (* 24 (time->factor 'hour))])
#;
(begin-for-syntax
  (define (time->factor x)
    (case x
      [(time) 1]
      [(minute) time-factor]
      [(hour) (* 60 (time->factor 'minute))]
      [(day) (* 24 (time->factor 'hour))]))
  (define-syntax-class time-msg
    #:attributes (factor)
    (pattern
     (~or
      (~literal time)
      (~literal minute)
      (~literal hour)
      (~literal day))
     #:attr factor (time->factor (syntax-e this-syntax)))))

(define-esterel-form await&
  (syntax-parser
    [(f S:time-msg)
     #'(f 1 S:msg)]
    [(_ t:call S:time-msg)
     #'(esterel:await& (* S.factor t) time)]
    [(_ b ...)
     #'(esterel:await& b ...)]))

(define-esterel-form every&
  (syntax-parser
    [(_ (c:call S:msg) p:expr ...)
     #'(seq& (await& c S) (loop-each& S p ...))]
    [(f S:msg p:expr ...)
     #'(f (1 S:msg) p ...)]))

(define-esterel-form loop-each&
  (syntax-parser
    [(_ test:expr p:expr ...)
     #'(loop&
        (abort& test
                (seq& (seq& p ...) halt&)))]))

(define-esterel-form abort&
  (syntax-parser
    [(f S:time-msg p:expr ...)
     #'(f (1 S) p ...)]
    [(_ (c:call S:time-msg) p:expr ...)
     (define/with-syntax T (generate-temporary (format-id #f "~a-time-abort-trap"
                                                          (~a (syntax->datum #'S)))))
     (define/with-syntax S_local (generate-temporary (format-id #f "~a-time-abort-message"
                                                                (~a (syntax->datum #'S)))))
     #'(trap& T
              (signal& S_local
                       (par& (seq& (suspend& S_local (seq& p ...)) (exit& T))
                             (seq& (await& c S) (emit& S_local) (exit& T)))))]
    [(_ S:msg p:expr ...)
     #'(esterel:abort& S p ...)]))

(define-esterel-form signal&
  (syntax-parser
    [(signal& S:time-msg b ...)
     (raise-syntax-error 'signal& "cannot override time signal" this-syntax)]
    [(signal& b ...)
     #'(esterel:signal& b ...)]))

(define-esterel-form emit&
  (syntax-parser
    [(emit& S:time-msg b ...)
     (raise-syntax-error 'emit& "cannot emit time signal" this-syntax)]
    [(emit& b ...)
     #'(esterel:emit& b ...)]))
