#lang debug racket
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
         cond&
         ?
         machine-prog
         machine-store
         (for-syntax msg call est))
(require esterel/cos-model
         redex/reduction-semantics
         racket/stxparam
         (for-syntax racket/pretty syntax/parse racket/syntax
                     racket/sequence racket/format racket/promise
                     syntax/id-set))

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
              ([i (in-list valid-ins)])
      (match i
        [(list s d)
         (match inputs
           [(list x ... (list (== s) d) y ...)
            (term (data<- ,store ,s ,d ready))]
           [else (term (data<- ,store ,s ,d old))])]
        [s store])))
  (define E
    (for/list ([i (in-list valid-ins)])
      (match-define (or (list S _) S) i)
      (match inputs
        [(list _ ... (or (== S) (list (== S) _)) _ ...)
         (list S '(Succ zero))]
        [else (list S 'zero)])))
  (pretty-print in-store*)
  (pretty-print E)
  (match-define (list (list 'machine out-prog out-store) out-E)
    (term (eval (machine ,in-prog ,in-store*) ,E)))
  (values (make-machine out-prog out-store valid-ins)
          ;; TODO look crap up in the store
          out-E))

(struct machine (prog store valid-ins)
  #:reflection-name 'esterel-machine
  #:extra-constructor-name make-machine)
(define-syntax esterel-machine
  (syntax-parser
    [(_ #:inputs (in ...)
        #:outputs (out ...)
        machine)
     (define/with-syntax t
       (parameterize ([in-machine? #t])
         (parameterize (#;
                        [signal-var-map
                         (for*/hash ([i* (in-syntax #'(in ... out ...))]
                                     [i (in-value (syntax-parse i* [(s _) #'s] [_ #f]))]
                                     #:when i)
                           (values (syntax-e i) (generate-temporary i)))])
           (define init-expr
             (parameterize (#;
                            [signal-replace-map
                             (for/hash ([i (in-syntax #'(in ... out ...))])
                               (define i* (syntax-e (syntax-parse i [(s _) #'s] [_ i])))
                               (values i* (generate-temporary i*)))])
               (wrap-shared #'(in ... out ...)
                            (local-expand-esterel #'machine))))
           init-expr)))
     (define/with-syntax (out/value ...)
       (for/list ([o (in-syntax #'(out ...))]
                  #:when
                  (syntax-parse o
                    [(a b) #t]
                    [_ #f]))
         (syntax-parse o
           [(n v)
            #`(dshared n v old)])))
     (define/with-syntax (in/sym ...)
       (for/list ([x (in-syntax #'(in ...))])
         (syntax-parse x
           [(i _) #'i]
           [i #'i])))
     (define/with-syntax (out/sym ...)
       (for/list ([x (in-syntax #'(out ...))])
         (syntax-parse x
           [(i _) #'i]
           [i #'i])))
     #'(let-values ([(raw-prog) (fix-i/o (term t) '(in/sym ...) '(out/sym ...))])
         ;(loop-safe! raw-prog) TODO
         (make-machine raw-prog (term (out/value ...)) '(in ...)))]))

(define-for-syntax (wrap-shared vars stx)
  (syntax-parse vars
    [() stx]
    [((s:id c) r ...)
     ;(define/with-syntax s_var (get-signal-var #'s))
     #`(shared s := c #,(wrap-shared #'(r ...) stx))]
    [(s:id r ...)
     (wrap-shared #'(r ...) stx)]))

(define-for-syntax valid-esterel-forms (mutable-free-id-set))
(define-syntax define-esterel-form
  (syntax-parser
    [(_ name:id val)
     #'(define-syntax name (make-esterel-form val))]))

(define-for-syntax in-machine? (make-parameter #f))

(begin-for-syntax
  (struct esterel-form (proc)
    #:property prop:procedure (struct-field-index proc)))
(define-for-syntax (make-esterel-form f)
  (esterel-form
   (lambda (stx)
     (unless (in-machine?)
       (raise-syntax-error #f "use of a esterel form not in a esterel machine" stx))
     (define n
       (syntax-parse stx
         [(n:id . body)
          #'n]
         [name:id #'name]))
     (unless (esterel-form? (syntax-local-value n))
       (raise-syntax-error #f "use of non-esterel form in esterel context" stx))
     (f stx))))

(define-for-syntax (local-expand-esterel stx)
  (unless (in-machine?)
      (raise-syntax-error #f "use of a esterel form escaped esterel context" stx))
  (local-expand stx 'expression core-esterel-forms))

(define-syntax-parameter ENV (lambda (stx) (raise-syntax-error #f "no" stx)))
(define-for-syntax shared-vars-set (make-parameter #f))
(define-for-syntax (delayed-call e)
  (delay
    (with-syntax ([env #'env])
      (parameterize ([shared-vars-set (mutable-free-id-set)])
        (define/with-syntax f
          (local-expand
           #`(make-esterel-top-procedure
              (lambda (env)
                (syntax-parameterize ([ENV (make-rename-transformer #'env)])
                  #,e)))
           'expression
           null))
        (define/with-syntax (var ...)  (free-id-set->list (shared-vars-set)))
        #`(func var ... (unquote f))))))
(begin-for-syntax
  (define-syntax-class msg
    (pattern _:id)
    (pattern (or _:id ...)))
  (define-syntax-class est
    (pattern a
             #:attr exp (delay (local-expand-esterel #'a))))
  (define-syntax-class call
    (pattern e
             #:attr func (delayed-call #'e))))

(define-esterel-form nothing& (syntax-parser [_:id #'nothing]))
(define-esterel-form pause& (syntax-parser [_:id #'pause]))
(define-esterel-form exit&
  (syntax-parser
    [(_ T:id) #`(exit (to-nat #,(get-exit-code #'T)))]))
(define-esterel-form emit&
  (syntax-parser
    [(_ S:id)
     #`(emit #,(get-signal-replacement #'S))]
    [(form S:id call:call)
     #`(seq& (form S)
             (<= #,(get-signal-var (get-signal-replacement #'S)) call.func))]))
(define-esterel-form emit/noreplace&
  (syntax-parser
    [(_ S:id) #`(emit S)]
    [(form S:id call:call)
     #`(seq& (form S)
             (<= S call.func))]))
(define-esterel-form present&
  (syntax-parser
    [(_ (~or (or S:id) S:id) th:est el:est)
     #`(present #,(get-signal-replacement #'S) th.exp el.exp)]
    [(p S:msg th:expr) #'(p S th nothing&)]
    ;; WARNING duplicates code
    [(p (or S1:id S2:id ...) th:expr el:expr)
     #'(p S1 th (p (or S2 ...) th el))]))
(define-esterel-form present/noreplace&
  (syntax-parser
    [(_ (~or (or S:id) S:id) th:est el:est)
     #`(present S th.exp el.exp)]
    [(p S:msg th:expr) #'(p S th nothing&)]
    ;; WARNING duplicates code
    [(p (or S1:id S2:id ...) th:expr el:expr)
     #'(p S1 th (p (or S2 ...) th el))]))
(define-esterel-form suspend&
  (syntax-parser
    [(_ (~or (or S:id) S:id) p:est)
     #`(suspend p.exp #,(get-signal-replacement #'S))]
    [(s (~or (or S:id) S:id) p:expr ...)
     #`(s s (seq& p ...))]
    [(s (or S1:id S2:id ...) p:expr ...)
     #'(s S1 (s (or S2 ...) p ...))]))
(define-esterel-form seq&
  (syntax-parser
    [(_ p:expr) #'p]
    [(_ l:est r:est)
     #'(seq l.exp r.exp)]
    [(_ l:expr r:expr ...)
     #`(seq& l (seq& r ...))]))
(define-esterel-form loop&
  (syntax-parser
    [(_ p:est)
     #'(loop p.exp)]
    [(_ p:expr ...)
     #`(loop& (seq& p ...))]))
(define-esterel-form par&
  (syntax-parser
    [(_ l:expr) #'l]
    [(_ l:est r:est) #'(par l.exp r.exp)]
    [(_ l:expr r:expr ...) #`(par& l (par& r ...))]))
(define-esterel-form trap&
  (syntax-parser
    [(_ T p:est)
     (parameterize ([exit-stack (cons #'T (exit-stack))])
       #'(trap p.exp))]
    [(_ T:id p:expr ...)
     #`(trap& T (seq& p ...))]))
(define-esterel-form signal&
  (syntax-parser
    #:datum-literals (:=)
    [(form S:id := e:call p:est)
     (parameterize ([signal-var-map (extend-signal-var-map-for #'S)])
       #`(signal S
               (shared #,(get-signal-var #'S) := e.func p.exp)))]
    [(form S:id := e:call p:expr ...)
     #`(form S := e.func (seq& p ...))]
    [(s (S:id) p:expr ...)
     #'(s S p ...)]
    [(s (S_1:id S:id ...) p:expr ...)
     #'(s S_1 (s (S ...) p ...))]
    [(_ S:id p:est)
     #`(signal S p.exp)]
    [(form S:id p:expr ...)
     #`(form S (seq& p ...))]))

(define-syntax ?/noreplace
  (syntax-parser
    [(? s:id)
     (free-id-set-add! (shared-vars-set) #'s)
     #`(redex-let esterel-eval
                  ([(any_1 (... ...) (dshared s datum shared-stat) any_2 (... ...))
                    ENV])
                  (term datum))]))

(define-syntax ?
  (syntax-parser
    [(? s:id)
     (define/with-syntax svar (get-signal-var (get-signal-replacement #'s)))
     (free-id-set-add! (shared-vars-set) #'svar)
     #`(redex-let esterel-eval
                  ([(any_1 (... ...) (dshared svar datum shared-stat) any_2 (... ...))
                    ENV])
                  (term datum))]))
(define-syntax get-var
  (syntax-parser
    [(? v:id)
     #`(redex-let esterel-eval
                  ([((any_1 (... ...) (dvar v datum) any_2 (... ...)))
                    ENV])
                  (term datum))]))
(define-esterel-form cond&
  (syntax-parser
    [(cond& [a b ...] body ...)
     #`(if& a
            (seq& b ...)
            (cond& body ...))]
    [(cond&) #'nothing&]))
(define-esterel-form if&
  (syntax-parser
    [(_ call:call p:est q:est)
     (define/with-syntax v (generate-temporary))
     #'(var v := call.func (if v p.exp q.exp))]))

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
    [(a n:call S:msg)
     (define/with-syntax v (generate-temporary))
     (define/with-syntax T (generate-temporary))
     #`(trap& T
              (var v := n.func
                   #,(local-expand-esterel
                      #'(loop&
                         pause&
                         (await& S)
                         (:=& v (+ (get-var v) -1))
                         (if& (= (get-var v) 0)
                              (exit& T)
                              nothing&)))))]
    [(_ S:msg)
     (define/with-syntax T (generate-temporary (format-id #f "~a-await-trap"
                                                          (~a (syntax->datum #'S)))))
     #'(trap& T
              (loop&
               (seq&
                pause&
                (present& S (exit& T) nothing&))))]))
(define-esterel-form :=&
  (syntax-parser
    [(_ v c:call)
     #'(:= v c.func)]))
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
  (if (hash-has-key? (signal-var-map) (syntax-e s))
      (signal-var-map)
      (hash-set (signal-var-map) (syntax-e s) (generate-temporary s))))
(define-for-syntax (get-signal-var s)
  (hash-ref (signal-var-map) (syntax-e s) s))

(define-for-syntax signal-replace-map (make-parameter (make-hash)))
(define-for-syntax (extend-signal-replace-map-for s)
  (hash-set (signal-replace-map) (syntax-e s) (gensym)))
(define-for-syntax (get-signal-replacement s)
  (hash-ref (signal-replace-map) (syntax-e s) s))

(module+ test
  (require rackunit)
  (test-begin
    (define-values (M S...)
      (eval-top
       (esterel-machine
        #:inputs ((I 0))
        #:outputs ((O 0))
        (present& I
                  (if& (= (? I) 1)
                       (emit& O 1)
                       nothing&)))
       '((I 1))))
    (check-equal? S... '(O))))


(define (fix-i/o prog ins outs)
  (define-values (prog* in-map out-map) (needed+sub prog ins outs))
  (define new/ins
    (for/fold ([p prog*])
              ([(old new) (in-hash in-map)])
      `(signal ,new
               (par
                ,p
                (loop
                 (seq
                  (present ,old (emit ,new) nothing)
                  pause))))))
  (define new/outs
    (for/fold ([p new/ins])
              ([(old new) (in-hash out-map)])
      `(signal ,new
               (par
                ,p
                (loop
                 (seq
                  (present ,new (emit ,old) nothing)
                  pause))))))
  new/outs)
(define (needed+sub prog ins outs [ins-hash (hash)] [outs-hash (hash)])
  (define (recur p #:ins [in* ins-hash] #:outs [out* outs-hash])
    (needed+sub p ins outs in* out*))
  (define (get S)
    (or (hash-ref outs-hash S #f)
        (hash-ref ins-hash S #f)
        S))
  (define do
    (term-match/single
     esterel-eval
     [nothing (values prog ins-hash outs-hash)]
     [pause (values prog ins-hash outs-hash)]
     [(seq p q)
      (let ()
        (define-values (l1 l2 l3) (recur `p))
        (define-values (r1 r2 r3) (recur `q #:ins l2 #:outs l3))
        (values `(seq ,l1 ,r1) r2 r3))]
     [(par p q)
      (let ()
         (define-values (l1 l2 l3) (recur `p))
         (define-values (r1 r2 r3) (recur `q #:ins l2 #:outs l3))
         (values `(par ,l1 ,r1) r2 r3))]
     [(loop p)
      (let ()
         (define-values (a b c) (recur `p))
         (values `(loop ,a) b c))]
     [(suspend p S)
      (let ()
         (cond [(hash-ref outs-hash `S #f) =>
                (lambda (nS)
                  (recur `(suspend p ,nS)))]
               [(member `S outs)
                (recur prog #:outs (hash-set outs-hash `S (gensym `S)))]
               [else
                (define-values (l1 l2 l3) (recur `p))
                (values `(suspend ,l1 S) l2 l3)]))]
     [(signal S p)
      (let ()
         (define-values (a b c) (recur `p))
         (values `(signal S ,a) b c))]
     [(emit S)
      (let ()
         (cond [(hash-ref ins-hash `S #f) =>
                (lambda (nS)
                  (values `(emit ,nS) ins-hash outs-hash))]
               [(member `S ins)
                (recur prog #:ins (hash-set ins-hash `S (gensym `S)))]
               [(hash-ref outs-hash `S #f) =>
                (lambda (nS)
                  (values `(emit ,nS) ins-hash outs-hash))]
               [else (values prog ins-hash outs-hash)]))]
     [(present S p q)
      (let ()
         (cond [(hash-ref outs-hash `S #f) =>
                (lambda (nS)
                  (recur `(present ,nS p q)))]
               [(member `S outs)
                (recur prog #:outs (hash-set outs-hash `S (gensym `S)))]
               [(hash-ref ins-hash `S #f) =>
                (lambda (nS)
                  (recur `(present ,nS p q)))]
               [else
                (define-values (l1 l2 l3) (recur `p))
                (define-values (r1 r2 r3) (recur `q #:ins l2 #:outs l3))
                (values `(present S ,l1 ,r1) r2 r3)]))]
     [(trap p)
      (let ()
         (define-values (a b c) (recur `p))
         (values `(trap ,a) b c))]
     [(exit _) (values prog ins-hash outs-hash)]
     [(var v := any p)
      (let ()
         (define-values (a b c) (recur `p))
         (values `(var v := any ,a) b c))]
     [(shared s := any p)
      (let ()
        (define-values (a b c) (recur `p))
        (values `(shared s := any ,a) b c))]
     [(:= v call) (values prog ins-hash outs-hash)]
     [(<= s call) (values prog ins-hash outs-hash)]
     [(if v p q)
      (let ()
         (define-values (l1 l2 l3) (recur `p))
         (define-values (r1 r2 r3) (recur `q #:ins l2 #:outs l3))
         (values `(if v ,l1 ,r1) r2 r3))]))
  ;; -- in --
  (do prog))
