#lang racket
(provide test-seq)
(require esterel/front-end
         rackunit
         (for-syntax syntax/parse racket/sequence racket/syntax
                     racket/list))
(define-syntax test-seq
  (syntax-parser
    #:datum-literals (=>)
    [(_ machine:expr
        (~seq
         (~optional (~seq #:equivalence ((x:id => n:nat y:id) ...))
                    #:defaults ([(x 1) null]
                                [(n 1) null]
                                [(y 1) null]))
         (~and ops ((ins ...) (outs ...))) ...))


     
     (define matching-table
       (apply hash (append-map values (syntax->datum #'((x (n y)) ...)))))
     (define (get-equiv i/o-pair)
       (syntax-parse i/o-pair
         [((x) (a ...))
          (hash-ref matching-table (syntax-e #'x)
                    #f)]
         [else #f]))
     (define-values (p _)
       (for/fold ([prog null] [mach #'machine])
                 ([i/o-pair (in-syntax #'(ops ...))])
         (define/with-syntax ((ins ...) (outs ...)) i/o-pair)
         (define/with-syntax next (generate-temporary))
         (define/with-syntax out (generate-temporary))
         (define nstx
           (cond [(get-equiv i/o-pair) =>
                  (lambda (matching)
                    (define bindings
                      (append
                       (list #`[(out next) (values (set) #,mach)])
                       (for/list ([_ (in-range (car matching))])
                         #`[(out next)
                            (let ()
                              (define-values (a b) (eval-top next '#,(cdr matching)))
                              (values (set-union a out) b))])
                       (list #'[(out next)
                                (let ()
                                  (define-values (a b) (eval-top next '(ins ...)))
                                  (values (set-union a out) b))])))
                    #`(begin
                        (define-values (out next)
                          (let*-values (#,@bindings)
                            (values out next)))
                        #,(quasisyntax/loc i/o-pair
                            (check-equal? out (set 'outs ...)
                                          (~a '#,i/o-pair)))))]
                 [else
                  #`(begin
                      #|
                      (pretty-print '#,i/o-pair)
                      (displayln 'old:)
                      (pretty-print (machine-prog #,mach))
                      |#
                      (define-values (out next) (eval-top #,mach '(ins ...)))
                      #|
                      (displayln 'new:)
                      (pretty-print (machine-prog next))
                      |#
                      #,(quasisyntax/loc i/o-pair
                          (check-equal? out (set 'outs ...)
                                        (~a '#,i/o-pair))))]))
         (values (cons nstx prog) #'next)))
     #`(let () #,@(reverse p))]))
