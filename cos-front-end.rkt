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
         every&
         if&
         (for-syntax msg))
(require esterel/cos-model
         redex/reduction-semantics
         (for-syntax syntax/parse racket/syntax racket/sequence racket/format))

(define-for-syntax core-esterel-forms
  (syntax->list
   (quote-syntax
    (nothing
     pause
     seq
     par
     loop
     suspend
     present
     trap
     exit
     emit
     var
     shared
     signal
     :=
     <=
     if))))


;; Machine Inputs -> Machine Inputs
;; where Inputs = (listof (U symbol (lst symbol any)))
(define (eval-top in-machine inputs)
  (match-define (machine in-prog in-store valid-ins) in-machine)
  (define in-store*
    (for/fold ([store in-store])
              ([i (in-list inputs)])
      (match i
        [(list s d)
         (term (data<- ,store ,s ,d new))]
        [s in-store])))
  (define E
    (for/list ([i (in-list valid-ins)])
      (match-define (or (list S _) S) i)
      (if (member S inputs)
          (list S 'one)
          (list S 'zero))))
  (match-define (list (list 'machine out-prog out-store) out-E)
    (term (eval (machine ,in-prog ,in-store*) ,E)))
  (values (make-machine out-prog out-store)
          ;; TODO look crap up in the store
          out-E))

(struct machine (prog store valid-ins)
  #:reflection-name 'esterel-machine
  #:extra-constructor-name make-machine)
(define-syntax esterel-machine
  (syntax-parser
    [(_ #:ins (in:id ...)
        #:outs (out:id ...)
        machine)
     (define/with-syntax t
       (parameterize ([in-machine? #t])
         (local-expand-esterel
          (wrap-outs #'(out ...)
                     (wrap-ins #'(in ...)
                               #'machine)))))
     #'(let ([raw-prog (term t)])
         ;(loop-safe! raw-prog) TODO
         (make-machine raw-prog (term ()) '(in ...)))]))

(define-for-syntax (wrap-outs outs stx)
  ;TODO
  stx)
(define-for-syntax (wrap-ins ins stx)
  ;TODO
  stx)

(define-syntax define-esterel-form
  (syntax-parser
    [(_ name:id val)
     #'(define-syntax name (make-esterel-form val))]))

(define-for-syntax in-machine? (make-parameter #f))

(define-for-syntax (make-esterel-form f)
  (lambda (stx)
    (unless (in-machine?)
      (raise-syntax-error #f "use of a esterel form not in a esterel machine" stx))
    (syntax-parse stx
      [(_:id body ...)
       ;; TODO local expand?
       (f stx)]
      [name:id (f stx)])))

(define-for-syntax (local-expand-esterel stx)
  (unless (in-machine?)
      (raise-syntax-error #f "use of a esterel form escaped esterel context" stx))
  (local-expand stx 'expression core-esterel-forms))

(begin-for-syntax
  (define-syntax-class msg
    (pattern _:id)
    (pattern (or _:id ...))))

(define-esterel-form nothing& (syntax-parser [_:id #'nothing]))
(define-esterel-form pause& (syntax-parser [_:id #'pause]))
(define-esterel-form exit&
  (syntax-parser
    [(_ T:id) #`(exit #,(get-exit-code #'T))]))
(define-esterel-form emit&
  (syntax-parser
    [(_ S:id) #'(emit S)]
    [(form S:id call:expr)
     #'(seq& (form S)
             (<= #,(get-signal-var #'S) call))]))
(define-esterel-form present&
  (syntax-parser
    [(_ (~or (or S:id) S:id) th:expr el:expr) #'(present S th el)]
    [(p S:msg th:expr) #'(p S th nothing&)]
    ;; WARNING duplicates code
    [(p (or S1:id S2:id ...) th:id el:expr)
     #'(p S1 th (p (or S2 ...) th el))]))
(define-esterel-form suspend&
  (syntax-parser
    [(_ (~or (or S:id) S:id) p:expr ...)
     #'(suspend S (seq& p ...))]
    [(s (or S1:id S2:id ...) p:expr ...)
     #'(s S1 (s (or S2 ...) p ...))]))
(define-esterel-form seq&
  (syntax-parser
    [(_ p:expr) #'p]
    [(_ l:expr r:expr ...) #'(seq l (seq& r ...))]))
(define-esterel-form loop&
  (syntax-parser
    [(_ p:expr ...)
     #'(loop (seq& p ...))]))
(define-esterel-form par&
  (syntax-parser
    [(_ l:expr) #'l]
    [(_ l:expr r:expr ...) #'(par l (par& r ...))]))
(define-esterel-form trap&
  (syntax-parser
    [(_ T:id p:expr ...)
     (parameterize ([exit-stack (cons #'T (exit-stack))])
       (local-expand-esterel
        #'(trap (seq& p ...))))]))
(define-esterel-form signal&
  (syntax-parser
    #:datum-literals (:=)
    [(s (S:id) p:expr ...)
     #'(s S p ...)]
    [(s (S_1:id S:id ...) p:expr ...)
     #'(s S_1 (s (S ...) p ...))]
    [(_ S:id p:expr ...)
     ;(define/with-syntax S&
     ;  (syntax-property (format-id #'S "~a&" #'S #:source #'S) 'original-for-check-syntax #t) )
     ;#'(let ([S 'S])
     ;    (define-esterel-form S&
     ;      (syntax-parser
     ;        [_:id #`(emit& #,(quasisyntax/loc this-syntax S))])))
     #'(signal S (seq& p ...))]
    ;; value
    [(form S:id := e:expr p:expr)
     (parameterize ([signal-var-map (extend-signal-var-map-for #'S)])
       (local-expand-esterel
        #'(form S
                (shared #,(get-signal-var #'S) := e p))))]))
(define-esterel-form ?
  (syntax-parser
    [(? s:id)
     (get-signal-var #'s)]))
(define-esterel-form if&
  (syntax-parser
    [(if call:expr p:expr q:expr)
     (define/with-syntax v (generate-temporary))
     #'(var v := call (if v p q))]))

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
     (define/with-syntax v (generate-temporary))
     (define/with-syntax T (generate-temporary))
     #'(trap& T
              (var v := n
                   (loop&
                    pause&
                    (await& S)
                    (<= v (+ v -1))
                    (if (= v 0)
                        (exit& T)
                        nothing&))))]
    [(_ S:msg)
     (define/with-syntax T (generate-temporary (format-id #f "~a-await-trap"
                                                          (~a (syntax->datum #'S)))))
     #'(trap& T
              (loop&
               (seq&
                pause&
                (present& S (exit& T) nothing&))))]))
(define-esterel-form sustain&
  (syntax-parser
    [(_ S:msg) #'(loop& (emit& S) pause&)]))

(define-esterel-form every&
  (syntax-parser
    [(_ S:msg p:expr ...)
     #'(seq& (await& S) (loop-each& S p ...))]))



(define-for-syntax exit-stack (make-parameter null))
(define-for-syntax (get-exit-code T)
  (+ 2
     (for/sum ([k (exit-stack)]
               #:break (free-identifier=? T k))
       1)))
(define-for-syntax signal-var-map (make-parameter (make-hash)))
(define-for-syntax (extend-signal-var-map-for s)
  (hash-set (signal-var-map) s (gensym)))
(define-for-syntax (get-signal-var s)
  (hash-ref (signal-var-map) s))
