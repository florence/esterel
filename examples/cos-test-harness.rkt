#lang racket
(provide test-seq)
(require (for-syntax syntax/parse racket/match racket/syntax)
         esterel/pop-pl-front-end
         rackunit)

(define-syntax test-seq
  (syntax-parser
    [(_ machine (ins outs) ...)
     (define/with-syntax test
       (let loop ([ins (syntax->list #'(ins ...))]
                  [outs (syntax->list #'(outs ...))]
                  [m #'machine])
         (match* (ins outs)
           [((cons in rin)
             (cons out rout))
            (loop
             rin
             rout
             (quasisyntax/loc out
               (let ()
                 (define-values (m* out*)
                   #,(quasisyntax/loc out (pop-pl-eval #,m '#,in)))
                 #,(quasisyntax/loc out (#,(quasisyntax/loc out check-equal?)
                                         #,(quasisyntax/loc out (list->set out*))
                                         #,(quasisyntax/loc out (list->set '#,out))))
                 m*)))]
           [(_ _) m])))
     #'(test-begin test)]))
