#lang racket
(provide test-seq)
(require esterel/front-end
         rackunit
         (for-syntax syntax/parse racket/sequence racket/syntax))
(define-syntax test-seq
  (syntax-parser
    [(_ machine (~and ops ((ins ...) (outs ...))) ...)
     (define-values (p _)
       (for/fold ([prog null] [mach #'machine])
                 ([i/o-pair (in-syntax #'(ops ...))])
         (define/with-syntax ((ins ...) (outs ...)) i/o-pair)
         (define/with-syntax next (generate-temporary))
         (define/with-syntax out (generate-temporary))
         (values
          (cons
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
                                 (~a '#,i/o-pair))))
           prog)
          #'next)))
     #`(let () #,@(reverse p))]))
