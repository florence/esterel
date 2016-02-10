#lang racket
(provide esterel-machine
         define-esterel-form
         eval-top
         nothing&
         exit&
         emit&
         pause&
         present&
         suspend&
         seq&
         loop&
         par&
         trap&
         signal&
         loop-each&
         await&
         abort&
         halt&
         sustain&
         machine-prog
         machine-valid-ins
         machine-valid-outs)
(require esterel/transform esterel/analysis racket/stxparam racket/stxparam-exptime
         esterel/analysis
         (prefix-in est: esterel/eval)
         (prefix-in node: esterel/ast)
         (for-syntax syntax/parse racket/syntax racket/sequence racket/format))

(struct machine (prog valid-ins valid-outs)
  #:reflection-name 'esterel-machine)

(define (eval-top in-machine inputs)
  ;;TODO check for valid inputs
  (define vins (machine-valid-ins in-machine))
  (define vouts (machine-valid-outs in-machine))
  (define-values (p* outs _)
    (est:eval (machine-prog in-machine)
              (append
               (map node::present inputs)
               (map node::absent
                    (filter-not (lambda (x) (member x inputs))
                                vins)))))
  (values
   (list->set (filter (lambda (x) (member x vouts)) outs))
   (machine
    p*
    vins
    (machine-valid-outs in-machine))))

(begin-for-syntax
  (define signal-intro (make-syntax-introducer)))

(define-syntax-parameter in-machine #f)
(define-syntax esterel-machine
  (syntax-parser
    [(_ #:inputs (in:id ...) #:outputs (out:id ...)
        p)
     ;&; TODO lift analysis and transforms to compile time
     (define/with-syntax (out& ...)
       (for/list ([id (in-syntax #'(out ...))])
         (syntax-property (format-id id "~a&" id #:source id) 'original-for-check-syntax #t)))
     #`(syntax-parameterize ([in-machine #t])
         (let ()
           (let* ([in 'in] ...
                  [out 'out] ...)
             (define-esterel-form out&
               (syntax-parser
                 [_:id
                  (define/with-syntax out* (quasisyntax/loc this-syntax out))
                  #`(emit& out*)]))
             ...
             (let ([raw-prog p])
               (loop-safe! p)
               (define orig-prog (replace-I/O raw-prog '(in ...) '(out ...)))
               (machine orig-prog '(in ...) '(out ...))))))]))

(define-syntax define-esterel-form
  (syntax-parser
    [(_ name:id val)
     #'(define-syntax name (make-esterel-form val))]))
(define-for-syntax (make-esterel-form f)
  (lambda (stx)
    (unless (syntax-parameter-value #'in-machine)
      (raise-syntax-error #f "use of a esterel form not in a esterel machine" stx))
    (f stx)))

(begin-for-syntax
  (define-syntax-class msg
    (pattern _:id)
    (pattern (or _:id ...))))

;;TODO signals can interfier if they have the same name
(define-esterel-form nothing&
  (syntax-parser
    [_:id #'(node:nothing)]))
(define-esterel-form exit&
  (syntax-parser
    [(_ T:id)
     #`(node:exit 'T #,(get-exit-code #'T))]))
(define-esterel-form emit&
  (syntax-parser
    [(_ S:id) #'(node:emit S)]))
(define-esterel-form pause&
  (syntax-parser
    [_:id #'(node:pause)]))
(define-esterel-form present&
  (syntax-parser
    [(_ (~or (or S:id) S:id) th:expr el:expr) #'(node:present S th el)]
    [(p S:msg th:expr) #'(p S th nothing&)]
    [(p (or S1:id S2:id ...) th:id el:expr)
     #'(p S1 th (p (or S2 ...) th el))]
    [(p (or S1:id S2:id ...) th:expr el:expr)
     #'(let ([t th])
         (p S1 t (p (or S2 ...) t el)))]))
(define-esterel-form suspend&
  (syntax-parser
    [(_ (~or (or S:id) S:id) p:expr ...)
     #'(node:suspend S (seq& p ...))]
    [(s (or S1:id S2:id ...) p:expr ...)
     #'(s S1 (s (or S2 ...) p ...))]))
(define-esterel-form seq&
  (syntax-parser
    [(_ p:expr) #'p]
    [(_ l:expr r:expr ...) #'(node:seq l (seq& r ...))]))
(define-esterel-form loop&
  (syntax-parser
    [(_ p:expr ...)
     #'(node:loop (seq& p ...))]))
(define-esterel-form par&
  (syntax-parser
    [(_ l:expr) #'l]
    [(_ l:expr r:expr ...) #'(node:par l (par& r ...))]))
(define-esterel-form trap&
  (syntax-parser
    [(_ T:id p:expr ...)
     #`(syntax-parameterize ([exit-stack (cons #'T (syntax-parameter-value #'exit-stack))])
         (node:trap 'T (seq& p ...)))]))
(define-esterel-form signal&
  (syntax-parser
    [(_ S:id p:expr ...)
     (define/with-syntax S&
       (syntax-property (format-id #'S "~a&" #'S #:source #'S) 'original-for-check-syntax #t) )
     #'(let ([S 'S])
         (define-esterel-form S&
           (syntax-parser
             [_:id #`(emit& #,(quasisyntax/loc this-syntax S))]))
         (node:signal 'S (seq& p ...)))]))

(define-esterel-form loop-each&
  (syntax-parser
    [(_ S:msg p:expr ...)
     #'(loop&
        (abort& S
                (seq& (seq& p ...) halt&)))]))

(define-esterel-form abort&
  (syntax-parser
    [(_ S:msg p:expr ...)
     (define/with-syntax T (generate-temporary (format-id #f "~a-abort-trap"
                                                          (~a (syntax->datum #'S)))))
     #'(trap& T
              (par& (seq& (suspend& S (seq& p ...)) (exit& T))
                    (seq& (await& S) (exit& T))))]))

(define-esterel-form halt&
  (syntax-parser
    [_:id #'(loop& pause&)]))

;; very large expansion, should use `repeat` when we have impure esterel
(define-esterel-form await&
  (syntax-parser
    [(a n:nat S:msg)
     #'(let ([R (a S)])
         (await-R n R))]
    [(_ S:msg)
     (define/with-syntax T (generate-temporary (format-id #f "~a-await-trap"
                                                          (~a (syntax->datum #'S)))))
     #'(trap& T
              (loop&
               (seq&
                pause&
                (present& S (exit& T) nothing&))))]))

(define-esterel-form await-R
  (syntax-parser
    [(_ n:nat x:id)
     (define c (syntax-e #'n))
     (if (zero? c)
         #'nothing&
         #`(seq& x (await-R #,(sub1 c) x)))]))

(define-esterel-form sustain&
  (syntax-parser
    [(_ S:msg) #'(loop& (emit& S) pause&)]))




(define-syntax-parameter exit-stack null)
(define-for-syntax (get-exit-code T)
  (+ 2
     (for/sum ([k (syntax-parameter-value #'exit-stack)]
               #:break (free-identifier=? T k))
       1)))
