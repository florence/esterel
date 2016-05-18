#lang racket
(require redex racket/random)
(module+ test
  (provide (all-defined-out))
  (require rackunit (prefix-in rackunit: rackunit))
  (define-syntax-rule (test-case str tests ...)
    (rackunit:test-case
     str
     (printf "starting \"~a\" tests\n" str)
     tests ...
     (printf "finishing \"~a\" tests\n" str))))

(define-syntax quasiquote (make-rename-transformer #'term))

(define-syntax-rule (render-derivations r)
    (show-derivations (build-derivations r)))

(define-language nats
  (nat zero  (Succ nat))
  (one (Succ zero)) (two (Succ (Succ zero))) (three (Succ (Succ (Succ zero)))))


(define-term one (Succ zero))
(define-term two (Succ (Succ zero)))
(define-term three (Succ (Succ (Succ zero))))

#|
(define-metafunction nats
  to-nat : natural -> nat
  [(to-nat 0) zero]
  [(to-nat natural) (Succ (to-nat ,(sub1 `natural)))])
|#

(define-metafunction nats
  nat- : nat nat -> nat
  [(nat- nat zero) nat]
  [(nat- zero _) zero]
  [(nat- (Succ nat_1) (Succ nat_2))
   (nat- nat_1 nat_2)]
  [(nat- nat_1 nat_2) (nat- (natnorm nat_1) (natnorm nat_2))])

(define-metafunction  nats
  nat+ : nat nat -> nat
  [(nat+ nat zero) nat]
  [(nat+ nat_1 (Succ nat_2)) (nat+ (Succ nat_1) nat_2)]
  [(nat+ nat_1 nat_2) (nat+ nat_1 (natnorm nat_2))])

(define-metafunction  nats
  [(nat<= zero nat) #t]
  [(nat<= nat zero) #f]
  [(nat<= (Succ nat_1) (Succ nat_2)) (nat<= nat_1 nat_2)]
  [(nat<= nat_1 nat_2) (nat<= (natnorm nat_1) (natnorm nat_2))])

(define-metafunction  nats
  [(nat= zero zero) #t]
  [(nat= nat zero) #f]
  [(nat= zero nat) #f]
  [(nat= (Succ nat_1) (Succ nat_2)) (nat= nat_1 nat_2)]
  [(nat= nat_1 nat_2) (nat= (natnorm nat_1) (natnorm nat_2))])

(module+ test
  (test-equal
   `(nat= two one)
   #f)
  (test-equal
   `(nat= one two)
   #f))

(define-metafunction nats
  [(natnorm zero) zero]
  [(natnorm one) (Succ zero)]
  [(natnorm two) (Succ (natnorm one))]
  [(natnorm three) (Succ (natnorm two))]
  [(natnorm (Succ nat)) (Succ (natnorm nat))])

(define-extended-language esterel nats
  ((p q)
   nothing
   pause
   (seq p q)
   (par p q)
   (loop p)
   (suspend p S)
   (present S p q)
   (trap p)
   (exit k)
   (emit S)
   (var v := call p)
   (shared s := call p)
   (signal S p)
   (:= v call)
   (<= s call)
   (if v p q))

  ((phat qhat)
   (hat pause)
   (present S phat q)
   (present S p qhat)
   (suspend S phat)
   (seq phat q)
   (seq p qhat)
   (suspend phat S)
   (loop phat)
   (par phat qbar)
   (par pbar qhat)
   (trap phat)
   (var v := call phat)
   (shared s := call phat)
   (signal S phat)
   (if v phat q)
   (if v p qhat))

  ((pbar qbar) p phat)

  ((pdot qdot)
   (· pbar)
   (seq pdot q)
   (seq p qdot)
   (par pdot ⊥ qdot ⊥)
   (par pdot ⊥ qbar l)
   (par pbar k qdot ⊥)
   (par pbar k qbar l)
   (loop lstat pdot)
   (suspend pdot S)
   (present S pdot q)
   (present S p qdot)
   (trap pdot)
   (var v := call pdot)
   (shared s := call pdot)
   (signal S sstat pdot)
   (if v pdot q)
   (if v p qdot))

  ;; for now the only value is numbers
  (call datum (+ call call) (+ call) (+) v s)
  (datum natural)

  ((pdotdot qdotdot) pdot pbar)

  ((S v s) variable-not-otherwise-mentioned)

  (lstat none stop go)
  (pstat ⊥ l k)
  ((l k m) nat)
  (sstat ⊥ one zero)
   #:binding-forms
   (signal S p #:refers-to S)
   (signal S phat #:refers-to S)
   (signal S sstat pdot #:refers-to S)
   )
(module+ test
  (test-case "grammar"
    (check-true
     (redex-match? esterel (exit k) `(exit zero)))
    (check-true
     (redex-match? esterel (exit k) `(exit one)))
    (check-true
     (redex-match? esterel (exit k) `(exit two)))
    (check-true
     (redex-match? esterel (exit k) `(exit (Succ (Succ zero)))))
    (check-true
     (redex-match? esterel (exit k) `(exit three)))))
(define-extended-language esterel-eval esterel
  ;(m P E Ss k data)
  (E ((S sstat) ...))
  (K (k ...))
  (V (v ...))
  (e ⊥ S)
  ((l k m) .... ⊥)
  (data (data-elem ...))
  (data-elem (dvar v datum)
             (dshared s datum shared-stat))
  (shared-stat ready old new)

  (M (machine pdotdot data))

  #:binding-forms
  (machine pdotdot data))
(module+ test
  (test-case "eval grammar"
    (check-true
     (redex-match? esterel-eval l `one))
    (check-true
     (redex-match? esterel-eval sstat `one))
    (check-true
     (redex-match? esterel-eval E `((S one))))
    (check-true
     (redex-match? esterel-eval (E K V) `(((S one)) (zero) ())))))

(define-judgment-form esterel-eval
  #:mode     (→ I I O O O)
  #:contract (→ M E M e k)
  #|
  [------------
  ""
  (→ )]
  |#
  [------------
   "1"
   (→ (machine (· nothing) data) E
      (machine nothing data) ⊥ zero)]
  [------------
   "2"
   (→ (machine (· pause) data) E
      (machine (hat pause) data) ⊥ (Succ zero))]
  [------------
   "3"
   (→ (machine (· (hat pause)) data) E
      (machine pause data) ⊥ zero)]
  [------------
   "4"
   (→ (machine (· (seq pbar q)) data) E
      (machine (seq (· pbar) q) data) ⊥ ⊥)]

  [(→ (machine pdot data) E (machine pdotdot data_*) e k)
   (side-condition ,(not (equal? `k `zero)))
   ------------
   "5"
   (→ (machine (seq pdot q) data) E
      (machine (seq pdotdot q) data_*) e k)]

  [(→ (machine pdot data) E (machine p data_*) e zero)
   ------------
   "6"
   (→ (machine (seq pdot q) data) E
      (machine (seq p (· q)) data_*) e ⊥)]

  [------------
   "7"
   (→ (machine (· (seq p qhat)) data) E
      (machine (seq p (· qhat)) data) ⊥ ⊥)]
  [(→ (machine qdot data) E (machine qdotdot data_*) e m)
   ------------
   "8"
   (→ (machine (seq p qdot) data) E
      (machine (seq p qdotdot) data_*) e m)]
  [------------
  "9"
  (→ (machine (· (par p q)) data) E
     (machine (par (· p) ⊥ (· q) ⊥) data) ⊥ ⊥)]
  [------------
  "10"
  (→ (machine (· (par phat qhat)) data) E
     (machine (par (· phat) ⊥ (· qhat) ⊥) data) ⊥ ⊥)]
  [------------
  "11"
  (→ (machine (· (par phat q)) data) E
     (machine (par (· phat) ⊥  q zero) data) ⊥ ⊥)]
  [------------
  "12"
  (→ (machine (· (par p qhat)) data) E
     (machine (par p zero (· qhat) ⊥) data) ⊥ ⊥)]
  [------------
  "13"
  (→ (machine (par pbar k qbar l) data) E
     (machine (par pbar qbar) data) ⊥ (meta-max k l))]

  [(→ (machine pdot data) E (machine pdotdot data_*) e k)
   ------------
  "14"
   (→ (machine (par pdot ⊥ qdotdot m) data) E
      (machine (par pdotdot k qdotdot m) data_*) e ⊥)]

  [(→ (machine qdot data) E (machine qdotdot data_*) e k)
   ------------
  "15"
   (→ (machine (par pdotdot m qdot ⊥) data) E
      (machine (par pdotdot m qdotdot k) data_*) e ⊥)]

  [------------
   "16"
   (→ (machine (· (loop p)) data) E
      (machine (loop stop (· p)) data) ⊥ ⊥)]

  [------------
   "17"
   (→ (machine (· (loop phat)) data) E
      (machine (loop go (· phat)) data) ⊥ ⊥)]

  [(→ (machine pdot data) E
      (machine p data_*) e zero)
   ------------
   "18"
   (→ (machine (loop go pdot) data) E
      (machine (loop stop (· p)) data_*) e ⊥)]

  [(→ (machine pdot data) E
      (machine pbar data_*) e k)
   (side-condition ,(and (not (equal? `k `⊥))
                         (not (equal? `k `zero))))
   ------------
   "19"
   (→ (machine (loop lstat pdot) data) E
      (machine (loop pbar) data_*) e k)]

  ;; BLATANT TYPO data is missing? (page 103)
  [(→ (machine pdot data) E
      (machine pdot_* data_*) e ⊥)
   ------------
   "20"
   (→ (machine (loop lstat pdot) data) E
      (machine (loop lstat pdot_*) data_*) e ⊥)]

   [------------
   "21"
   (→ (machine (· (trap pbar)) data) E
      (machine (trap (· pbar)) data) ⊥ ⊥)]
   [(→ (machine pdot data) E
       (machine pdot_* data_*) e ⊥)
   ------------
   "22"
    (→ (machine (trap pdot) data) E
       (machine (trap pdot_*) data_*) e ⊥)]

   ;; TODO pbar and p used in rule? does that mean remove any pauses?
   ;; (page 89)
   [(→ (machine pdot data) E
       (machine pbar data_*) e two)
   ------------
   "23"
    (→  (machine (trap pdot) data) E
        (machine (trap (remove-selected pbar)) data_*) e zero)]

   [(→ (machine pdot data) E
       (machine p data_*) e zero)
   ------------
   "24"
    (→  (machine (trap pdot) data) E
        (machine (trap p) data_*) e zero)]

   [(→ (machine pdot data) E
       (machine phat data_*) e one)
   ------------
   "25"
    (→  (machine (trap pdot) data) E
        (machine (trap phat) data_*) e one)]

   [(→ (machine pdot data) E
       (machine pbar data) ⊥ k)
    (where nat k)
    ;; k >= 3
    (side-condition (nat<= (Succ (Succ (Succ zero))) k))
   ------------
   "26"
    (→  (machine (trap pdot) data) E
        (machine (trap pbar) data) ⊥ (↓ k))]

   [------------
   "27"
   (→ (machine (· (exit k)) data) E
      (machine (exit k) data) ⊥ k)]

   [------------
   "28"
   (→ (machine (· (signal S pbar)) data) E
      (machine (signal S ⊥ (· pbar)) data) ⊥ ⊥)]

   [(→ (machine pdot data) (* E (S m))
       ;;TODO should this really be the same data?
       (machine pdot_* data) S ⊥)
    (side-condition (∈ m (⊥ 1)))
    ------------
   "29"
    (→ (machine (signal S m pdot) data) E
       (machine (signal S (Succ zero) pdot_*) data) ⊥ ⊥)]

   ;; TODO (page 105) confusing S should be decorated with 1, 0, or ⊥
   ;; assuming to mean (S 1) is not in Can_S?

   [(side-condition (∉ (S (Succ zero)) (Can_S pdot (* E (S ⊥)))))
    ------------
   "30"
    (→ (machine (signal S ⊥ pdot) data) E
       (machine (signal S zero pdot) data) ⊥ ⊥)]

   [(→ (machine pdot data) (* E (S m))
       (machine qdot data_*) e ⊥)
    (side-condition ,(not (equal? `e `S)))
    ;; added to avoid unneeded non-determinism
    (side-condition ,(or
                      (not (equal? `⊥ `m))
                      (not `(∉ (S one) (Can_S pdot (* E (S ⊥)))))))
    ------------
   "31"
    (→ (machine (signal S m pdot) data) E
       (machine (signal S m qdot) data_*) e ⊥)]

   [(→ (machine pdot data) (* E (S m))
       (machine qbar data_*) e k)
    (side-condition ,(not (equal? `k `⊥)))
    (side-condition ,(not (equal? `e `S)))
    ;; added to avoid unneeded non-determinism
    (side-condition ,(or
                      (not (equal? `⊥ `m))
                      (not `(∉ (S one) (Can_S pdot (* E (S ⊥)))))))
    ------------
   "32"
    (→ (machine (signal S m pdot) data) E
       (machine (signal S qbar) data_*) e k)]


   [(→ (machine pdot data) (* E (S m))
       (machine qbar data_*) S k)
    (side-condition ,(not (equal? `k `⊥)))
    ;; added to avoid unneeded non-determinism
    (side-condition ,(or
                      (not (equal? `⊥ `m))
                      (not `(∉ (S one) (Can_S pdot (* E (S ⊥)))))))
    ------------
   "33"
    (→ (machine (signal S m pdot) data) E
       (machine (signal S qbar) data_*) ⊥ k)]

   [------------
   "34"
   (→ (machine (· (emit S)) data) E
      (machine (emit S) data) S zero)]

   [(where #t (∈ (S (Succ zero)) E))
    ------------
    "35"
    (→ (machine (· (suspend phat S)) data) E
       (machine (suspend phat S) data) ⊥ (Succ zero))]

   [(where #t (∈ (S zero) E))
    ------------
    "36"
    (→ (machine (· (suspend phat S)) data) E
       (machine (suspend (· phat) S) data) ⊥ ⊥)]

   [------------
    "37"
    (→ (machine (· (suspend p S)) data) E
       (machine (suspend (· p) S) data) ⊥ ⊥)]

   [(→ (machine pdot data) E (machine pdotdot data_*) e k)
    ------------
    "38"
    (→ (machine (suspend pdot S) data) E
       (machine (suspend pdotdot S) data_*) e k)]

   [(where #t (∈ (S (Succ zero)) E))
    ------------
    "39"
    (→ (machine (· (present S p q)) data) E
       (machine (present S (· p) q) data) ⊥ ⊥)]

   [(where #t (∈ (S zero) E))
    ------------
    "40"
    (→ (machine (· (present S p q)) data) E
       (machine (present S p (· q)) data) ⊥ ⊥)]

   [------------
    "41"
    (→ (machine (· (present S phat q)) data) E
       (machine (present S (· phat) q) data) ⊥ ⊥)]
   [------------
    "42"
    (→ (machine (· (present S p qhat)) data) E
       (machine (present S p (· qhat)) data) ⊥ ⊥)]

   [(→ (machine pdot data) E (machine pdotdot data_*) e k)
    ------------
    "43"
    (→ (machine (present S pdot q) data) E
       (machine (present S pdotdot q) data_*) e k)]

   [(→ (machine qdot data) E (machine qdotdot data_*) e k)
    ------------
    "44"
    (→ (machine (present S p qdot) data) E
       (machine (present S p qdotdot) data_*) e k)]

   [(where (s ...) (shared-of call_init data))
    (where (ready ...) ((data-ref data (s status)) ...))
    (where data_* (data<- data
                         s_set
                         (eval-call call_init data)
                         old))
    ------------
    "45"
    (→ (machine (· (shared s_set := call_init p)) data) E
       (machine (shared s_set := call_init (· p)) data_*) ⊥ ⊥)]

   [------------
    "46"
    (→ (machine (· (shared s := call_init phat)) data) E
       (machine (shared s := call_init (· phat)) (data<- data (s status) old)) ⊥ ⊥)]
   [(where #t (∈ (data-ref data (s status))
                 (old new)))
    (where #t (∉ s (Can_V pdot E)))
    ------------
    "47"
    (→ (machine (shared s := call_init pdot) data) E
       (machine (shared s := call_init pdot) (data<- data (s status) ready)) ⊥ ⊥)]

   [(→ (machine pdot data) E (machine pdotdot data_*) e k)
    ;; added to avoid nondeterminism
    (where #t
           (meta-or ((∈ s (Can_V pdot E))
                     (∈ (data-ref data (s status)) (ready)))))
    ------------
    "48"
    (→ (machine (shared s := call_init pdot) data) E
       (machine (shared s := call_init pdotdot) data_*) e k)]

   [(where old (data-ref data (s status)))

    (where (s_shared ...) (shared-of call data))
    (where (ready ...) ((data-ref data (s_shared status)) ...))

    (where data_* (data<- data (s status) new))
    (where data_** (data<- data_* (s value) (eval-call call data)))
    ------------
    "49"
    (→ (machine (· (<= s call)) data) E
       (machine (<= s call) data_**) ⊥ zero)]

   [(where new (data-ref data (s status)))

    (where (s_shared ...) (shared-of call data))
    (where (ready ...) ((data-ref data (s_shared status)) ...))


    ;; TODO allow for other comb functions
    (where datum_this (eval-call call data))
    (where datum_new (eval-call (+ (data-ref data (s value)) datum_this) data))
    (where data_* (data<- data (s value) datum_new))
    ------------
    "50"
    (→ (machine (· (<= s call)) data) E
       (machine (<= s call) data_*) ⊥ zero)]

   [(where (s_shared ...) (shared-of call data))
    (where (ready ...) ((data-ref data (s_shared status)) ...))

    (where data_* (data<- data v (eval-call call data)))
    ----------
    "51"
    (→ (machine (· (var v := call p)) data) E
       (machine (var v := call (· p)) data_*) ⊥ ⊥)]

   [----------
    "52"
    (→ (machine (· (var v := call phat)) data) E
       (machine (var v := call (· phat)) data) ⊥ ⊥)]

   [(→ (machine pdot data) E
       (machine pdotdot data_*) e k)
    ----------
    "53"
    (→ (machine (var v := call pdot) data) E
       (machine (var v := call pdotdot) data_*) e k)]

   [(where #t (∉ (data-ref data v) (0)))
    ----------
    "54"
    (→ (machine (· (if v p q)) data) E
       (machine (if v (· p) q) data) ⊥ ⊥)]

   [(where 0 (data-ref data v))
    ----------
    "55"
    (→ (machine (· (if v p q)) data) E
       (machine (if v p (· q)) data) ⊥ ⊥)]

   [----------
    "56"
    (→ (machine (· (if v phat q)) data) E
       (machine (if v (· phat) q) data) ⊥ ⊥)]

   [----------
    "57"
    (→ (machine (· (if v p qhat)) data) E
       (machine (if v p (· qhat)) data) ⊥ ⊥)]

   [(→ (machine pdot data) E
       (machine pdotdot data_*) e k)
    ----------
    "58"
    (→ (machine (if v pdot q) data) E
       (machine (if v pdotdot q) data_*) e k)]

   [(→ (machine qdot data) E
       (machine qdotdot data_*) e k)
    ----------
    "59"
    (→ (machine (if v p qdot) data) E
       (machine (if v p qdotdot) data_*) e k)]

   [(where (s_shared ...) (shared-of call data))
    (where (ready ...) ((data-ref data (s_shared status)) ...))

    (where datum (eval-call call data))
    (where data_* (data<- data v datum))
    ------------
    "60"
    (→ (machine (· (:= v call)) data) E
       (machine (:= v call) data_*) ⊥ zero)])


(define-metafunction esterel-eval
  meta-or : (boolean ...) -> boolean
  [(meta-or ()) #f]
  [(meta-or (#f any ...))
   (meta-or (any ...))]
  [(meta-or (#t any ...)) #t])

(define-metafunction esterel-eval
  shared-of : call data -> (s ...)
  [(shared-of datum data) ()]
  [(shared-of s data)
   (s)
   (where (any_1 ... (dshared s datum shared-stat) any_2 ...)
          data)]
  [(shared-of v data) ()]
  [(shared-of (+) data) ()]
  [(shared-of (+ call) data)
   (shared-of call data)]
  [(shared-of (+ call_1 call_2) data)
   (U (shared-of call_1 data) (shared-of call_2 data))])

(define-extended-language ref-lang esterel-eval
  (input ::= v s (s status) (s value))
  (output ::= datum shared-stat))
(define-metafunction ref-lang
  data-ref : data input -> output
  [(data-ref (any_1 .... (dvar v datum) any_2 ...) v) datum]
  [(data-ref (any_1 .... (dshared s datum shared-stat) any_2 ...)
             (s status))
   shared-stat]
  [(data-ref (any_1 .... (dshared s datum shared-stat) any_2 ...)
             (s value))
   datum])


(define-metafunction esterel-eval
  eval-call : call data -> datum
  [(eval-call s data)
   (data-ref data (s value))
   (where #t (∈ s (shared-of s data)))]
  [(eval-call v data) (data-ref data v)]
  [(eval-call datum data) datum]
  [(eval-call (+ call ...) data)
   ,(apply + `(datum ...))
   (where (datum ...) ((eval-call call data) ...))])

(define-metafunction esterel-eval
  ;data<- : data v datum -> data
  ;data<- : data s datum shared-stat -> data
  ;data<- : data (s value) datum -> data
  ;data<- : data (s status) shared-stat -> data
  [(data<- (any_1 ... (dvar v any) any_2 ...) v datum)
   (any_1 ... (dvar v datum) any_2 ...)]
  [(data<- (any ...) v datum)
   ((dvar v datum) any ...)]
  [(data<- (any_1 ... (dshared s any_3 any_4) any_2 ...) s datum shared-stat)
   (any_1 ... (dshared s datum shared-stat) any_2 ...)]
  [(data<- (any ...) s datum shared-stat)
   ((dshared s datum shared-stat) any ...)]
  [(data<- (any_1 ... (dshared s any shared-stat) any_2 ...) (s value) datum)
   (any_1 ... (dshared s datum shared-stat) any_2 ...)]
  [(data<- (any_1 ... (dshared s datum any) any_2 ...) (s status) shared-stat)
   (any_1 ... (dshared s datum shared-stat) any_2 ...)])

(module+ test
  (default-language esterel-eval)
  (define (do t [E `()] [data `()])
    (judgment-holds (→ (machine ,t ,data) ,E
                       (machine pdotdot data_*) e k)
                    (pdotdot e k data_*)))
  (test-case "1"
    (parameterize ([current-traced-metafunctions '(→)])
      (test-equal (do `(· nothing))
                  `((nothing ⊥ zero ())))))
  (test-case "2"
    (test-equal (do `(· pause))
                `(((hat pause) ⊥ one ()))))
  (test-case "3"
    (test-equal (do `(· (hat pause)))
                `((pause ⊥ zero ()))))
  (test-case "4"
    (test-equal
     (do `(· (seq pause pause)))
     `(((seq (· pause) pause) ⊥ ⊥ ())))
    (test-equal
     (do `(· (seq (hat pause) pause)))
     `(((seq (· (hat pause)) pause) ⊥ ⊥ ()))))
  (test-case "5"
    (test-equal
     (do `(seq (· (hat pause)) pause))
     `(( (seq pause (· pause)) ⊥ ⊥ ())))
    (test-equal
     (do `(seq (· pause) pause))
     `(( (seq (hat pause) pause) ⊥ one ()))))
  (test-case "6"
    (test-equal
     (do `(seq (· (hat pause)) pause))
     `(( (seq pause (· pause)) ⊥ ⊥ () )))

    (test-equal
     (do `(seq (· nothing) pause))
     `(( (seq nothing (· pause)) ⊥ ⊥ () ))))

  (test-case "7"
    (test-not-false "pbar"
     (redex-match esterel pbar `(seq pause (hat pause))))
    (test-equal
     (do `(· (seq pause (hat pause))))
     `(( (seq pause (· (hat pause))) ⊥ ⊥ ())))
    (test-equal
     (do `(· (seq pause (seq pause (hat pause)))))
     `(( (seq pause (· (seq pause (hat pause)))) ⊥ ⊥ () ))))

  (test-case "8"
    (check-not-false
     "8"
     (redex-match esterel pdot `(seq pause (seq (· (hat pause)) pause))))
    (check-not-false
     "8"
     (redex-match esterel pdot `(seq (· (hat pause)) pause)))
    (check-not-false
     "8"
     (redex-match esterel (seq p qdot) `(seq pause (seq (· (hat pause)) pause))))
    (test-equal
     (do ` (seq pause (· (hat pause))))
     `(( (seq pause pause) ⊥ zero ())))
    (test-equal
     (do `(seq pause (seq pause (· (hat pause)))))
     `(( (seq pause  (seq pause pause)) ⊥ zero () )))
    (test-equal
     (do `(seq pause (seq pause (· pause))) )
     `(( (seq pause (seq pause (hat pause))) ⊥ one () )))
    (test-equal
     (do `(seq pause (seq (· (hat pause)) pause)))
     `(( (seq pause (seq pause (· pause))) ⊥ ⊥ () ))))

  (test-case "9"
    (test-equal
     (do `(· (par pause pause)))
     `(( (par (· pause) ⊥ (· pause) ⊥) ⊥ ⊥ ()))))

  (test-case "10"
    (test-equal
     (do `(· (par (hat pause) (hat pause))))
     `(( (par (· (hat pause)) ⊥ (· (hat pause)) ⊥) ⊥ ⊥ ()))))

  (test-case "11"
    (test-equal
     (do `(· (par (hat pause)  pause)))
     `(( (par (· (hat pause)) ⊥ pause zero) ⊥ ⊥ ()))))

  (test-case "12"
    (test-equal
     (do `(· (par  pause (hat pause))))
     `(( (par pause zero (· (hat pause)) ⊥) ⊥ ⊥ ()))))

  (test-case "13"
    (test-equal
     (do `(par pause zero (hat pause) one))
     `(( (par pause (hat pause)) ⊥ one ()))))
  (test-case "14"
    (test-equal
     (do `(par (· (seq pause pause)) ⊥ pause zero))
     `(( (par (seq (· pause) pause) ⊥ pause zero) ⊥ ⊥ ()))))
  (test-case "15"
    (test-equal
     (do `(par pause zero (· (seq pause pause)) ⊥))
     `(( (par pause zero (seq (· pause) pause) ⊥) ⊥ ⊥ ()))))
  (test-case "14/15"
    (test-equal
     (do `(par (· (seq pause pause)) ⊥ (· (seq pause pause)) ⊥))
     `(( (par (seq (· pause) pause) ⊥ (· (seq pause pause)) ⊥) ⊥ ⊥ ())
       ( (par (· (seq pause pause)) ⊥ (seq (· pause) pause) ⊥) ⊥ ⊥ ()))))
  (test-case "16"
    (test-equal
     (do `(· (loop (seq pause nothing))))
     `(( (loop stop (· (seq pause nothing))) ⊥ ⊥ ()))))
  (test-case "17"
    (test-equal
     (do `(· (loop (seq (hat pause) nothing))))
     `(( (loop go (· (seq (hat pause) nothing))) ⊥ ⊥ ())))
    (test-equal
     (do `(· (loop (hat pause) )))
     `(( (loop go (· (hat pause))) ⊥ ⊥ ()))))
  (test-case "18"
    (test-equal
     (do `(loop go (seq pause (· nothing))))
     `(( (loop stop (· (seq pause nothing))) ⊥ ⊥ ()))))
  (test-case "19"
    (test-equal
     (do `(loop go (seq (· pause) nothing)))
     `(( (loop (seq (hat pause) nothing)) ⊥ one ())))
    (test-equal
     (do `(loop stop (seq (· pause) nothing)))
     `(( (loop (seq (hat pause) nothing)) ⊥ one ()))))
  (test-case "20"
    (test-equal
     (do `(loop go (seq (· (hat pause)) nothing)))
     `(( (loop go (seq pause (· nothing))) ⊥ ⊥ ())))
    (test-equal
     (do `(loop stop (seq (· (hat pause)) nothing)))
     `(( (loop stop (seq pause (· nothing))) ⊥ ⊥ ()))))
  (test-case "21"
    (test-equal
     (do `(· (trap (par pause pause))))
     `(( (trap (· (par pause pause))) ⊥ ⊥ ()))))
  (test-case  "22"
    (test-equal
     (do `(trap (seq (· nothing) pause)))
     `(( (trap (seq  nothing (· pause))) ⊥ ⊥ ()))))
  (test-case "23"
    (test-equal
     (do `(trap (seq (· (exit two)) pause)))
     `(( (trap (seq (exit two) pause)) ⊥ zero ()))))
  (test-case "24"
    (test-equal
     (do `(trap (seq pause (· (hat pause)))))
     `(( (trap (seq pause pause)) ⊥ zero ()))))
  (test-case "25"
    (test-equal
     (do `(trap (seq pause (· pause))))
     `(( (trap (seq pause (hat pause))) ⊥ one ()))))
  (test-case "26"
    (test-equal
     (do `(trap (· (exit three))))
     `(( (trap (exit three)) ⊥ (natnorm two) () ))))
  (test-case "27"
    (test-equal
     (do `(· (exit three)))
     `(( (exit three) ⊥ three ()))))
  (test-case "28"
    (test-equal
     (do `(· (signal S (emit S))))
     `(( (signal S ⊥ (· (emit S))) ⊥ ⊥ ()))))
  (test-case "29"
    (test-true "29-pdotdot"
     (redex-match? esterel-eval pdotdot `(seq (· (emit S«156»)) pause)))
    (test-true "29-E"
               (redex-match? esterel-eval E `((S«156» ⊥))))
    (test-equal
     (do `(seq (· (emit S)) pause))
     `(( (seq (emit S) (· pause)) S ⊥ ())))
    (test-equal
     (do `(signal S ⊥ (seq (· (emit S)) pause)))
     `(( (signal S one (seq (emit S) (· pause))) ⊥ ⊥ ()))))
  (test-case "30"
    (test-equal
     `(Can_S (signal S zero (seq (emit S) (seq pause (· pause)))) ((S ⊥)))
     `())
    (test-equal
     (do `(signal S ⊥ (seq (emit S) (seq pause (· pause)))))
     `(
       ((signal
          S«226»
          zero
          (seq (emit S«226») (seq pause (· pause))))
         ⊥
         ⊥
         ())
       )))
  (test-case "31"
    (test-equal
     (do `(signal S zero (seq (· (emit R)) pause)))
     `(( (signal S zero (seq (emit R) (· pause)))
         R
         ⊥
         ())))
    (test-equal
     `(Can_S (seq (· (hat pause)) (emit S)) ())
     `((S one)))
    (test-equal
     (do `(signal S ⊥ (seq (· (hat pause)) (emit S))))
     `(( (signal S ⊥ (seq pause (· (emit S))))
         ⊥
         ⊥
         ()))))

  (test-case "32"
    (test-equal
     (do `(signal S zero (· (emit R))))
     `(( (signal S (emit R))
         R
         zero
         ())))
    (test-equal
     (do `(· pause))
     `(( (hat pause) ⊥ one ())))
    (test-equal
     (do `(signal S zero (· pause)))
     `(( (signal S (hat pause))
         ⊥
         one
         ()))))

  (test-case "33"
    (test-equal
     (do `(signal S one (· (emit S)) ))
     `(( (signal S (emit S))
         ⊥
         zero
         ()))))

  (test-case "34"
    (test-equal
     (do `(· (emit S)))
     `(( (emit S) S zero ()))))

  (test-case "35"
    (test-equal
     (do `(· (suspend (hat pause) S))
         `((S (Succ zero))))
     `(( (suspend (hat pause) S) ⊥ (Succ zero) () ))))

  (test-case "36"
    (test-equal
     (do `(· (suspend (hat pause) S))
         `((S zero)))
     `(( (suspend (· (hat pause)) S) ⊥ ⊥ () ))))

  (test-case "37"
    (test-equal
     (do `(· (suspend pause S)))
     `(( (suspend (· pause) S) ⊥ ⊥ () ))))

  (test-case "38"
    (test-equal
     (do `(suspend (· pause) S))
     `(( (suspend (hat pause) S) ⊥ one () ))))

  (test-case "39"
    (test-equal
     (do `(· (present t pause pause)) `((t one)))
     `(( (present t (· pause) pause) ⊥ ⊥ ()))))
  (test-case "40"
    (test-equal
     (do `(· (present t pause pause)) `((t zero)))
     `(( (present t pause (· pause)) ⊥ ⊥ ()))))

  (test-case "41"
    (test-equal
     (do `(· (present t (hat pause) pause)) `((t zero)))
     `(( (present t (· (hat pause)) pause) ⊥ ⊥ ()))))
  (test-case "42"
    (test-equal
     (do `(· (present t  pause (hat pause))) `((t one)))
     `(( (present t pause (· (hat pause))) ⊥ ⊥ ()))))
  (test-case "43"
    (test-equal
     (do `(present t (· (hat pause)) pause))
     `(( (present t pause pause) ⊥ zero ()))))
  (test-case "44"
    (test-equal
     (do `(present t pause (· (hat pause))))
     `(( (present t pause pause) ⊥ zero ()))))

  (define-syntax-rule (do* p data)
    (judgment-holds (→ (machine p data) ()
                       M e k)
                    (M e k)))
  (test-case "45"
    (test-equal
     (do* (· (shared s := 5 nothing)) ())
     `(( (machine (shared s := 5 (· nothing)) ((dshared s 5 old)))
         ⊥ ⊥ )))
    (test-equal
     (do* (· (shared s := 5 nothing)) ((dshared s 5 old)))
     `(( (machine (shared s := 5 (· nothing)) ((dshared s 5 old)))
         ⊥ ⊥ ))))
  (test-case "46"
    (test-equal
     (do* (· (shared s := 5 (hat pause))) ((dshared s 12 ready)))
     `(( (machine (shared s := 5 (· (hat pause))) ((dshared s 12 old)))
         ⊥ ⊥
         ))))
  (test-case "47"
    (test-equal
     (do* (shared s := 1 (· nothing)) ((dshared s 0 old)))
     `(( (machine (shared s := 1 (· nothing)) ((dshared s 0 ready)))
         ⊥ ⊥ ))))
  (test-case "48"
    (test-equal
     (do* (shared s := 1 (· nothing)) ((dshared s 0 ready)))
     `(( (machine (shared s := 1 nothing) ((dshared s 0 ready)))
         ⊥ zero ))))
  (test-case "49"
    (test-equal
     (do* (shared s := 1
                  (· (<= s (+ 1 y))))
          ((dshared s 1 old)
           (dshared y 1 ready)))
     `((
        (machine
         (shared s := 1 (<= s (+ 1 y)))
         ((dshared s 2 new)
          (dshared y 1 ready)))
        ⊥
        zero
        ))))
  (test-case "50"
    (test-equal
     (do* (shared s := 1
                  (· (<= s (+ 1 y))))
          ((dshared s 1 new )
           (dshared y 1 ready)))
     `((
        (machine
         (shared s := 1 (<= s (+ 1 y)))
         ((dshared s 3 new)
          (dshared y 1 ready)))
        ⊥
        zero
        ))))

  (test-case "51"
    (test-equal `(shared-of (+ 2 1) ()) `())
    (check-true
     (redex-match? esterel-eval (· (var v := call p)) `(· (var v := (+ 2 1) nothing))))
    (test-equal
     (do*
      (· (var v := (+ 2 1) nothing))
      ())
     `((
        (machine (var v := (+ 2 1) (· nothing))
                 ((dvar v 3)))
        ⊥ ⊥
        ))))

  (test-case "52"
    (test-equal
     (do*
      (· (var v := 3 (hat pause)))
      ((dvar v 2)))
     `((
        (machine (var v := 3 (· (hat pause)))
                 ((dvar v 2)))
        ⊥
        ⊥
        ))))
  (test-case "53"
    (test-equal
     (do*
      (var v := 3 (· (hat pause)))
      ((dvar v 2)))
     `((
        (machine (var v := 3 pause)
                 ((dvar v 2)))
        ⊥
        zero)))
    (test-equal
     (do*
      (var v := 3 (· (:= v 4)))
      ((dvar v 2)))
     `((
        (machine (var v := 3 (:= v 4))
                 ((dvar v 4)))
        ⊥
        zero))))
  (test-case "54"
    (test-equal
     (do*
      (· (if v nothing pause))
      ((dvar v 1)))
     `((
        (machine (if v (· nothing) pause) ((dvar v 1)))
        ⊥ ⊥))))
  (test-case "55"
    (test-equal
     (do*
      (· (if v nothing pause))
      ((dvar v 0)))
     `((
        (machine (if v nothing (· pause)) ((dvar v 0)))
        ⊥ ⊥))))
  (test-case "56"
    (test-equal
     (do*
      (· (if v (hat pause) nothing))
      ((dvar v 12)))
     `(((machine
         (if v (· (hat pause)) nothing)
         ((dvar v 12)))
        ⊥ ⊥))))
  (test-case "57"
    (test-equal
     (do*
      (· (if v nothing (hat pause)))
      ((dvar v 12)))
     `((
        (machine
         (if v nothing (· (hat pause)))
         ((dvar v 12)))
        ⊥ ⊥
        ))))
  (test-case "58"
    (test-equal
     (do*
      (if v (· pause) nothing)
      ((dvar v 12)))
     `((
        (machine
         (if v (hat pause) nothing)
         ((dvar v 12)))
        ⊥ (Succ zero)
        ))))
  (test-case "59"
    (test-equal
     (do*
      (if v nothing (· pause))
      ((dvar v 12)))
     `((
        (machine
         (if v nothing (hat pause))
         ((dvar v 12)))
        ⊥ (Succ zero)
        ))))
  (test-case "60"
      (test-equal
     (do*
      (· (:= v 4))
      ((dvar v 2)))
     `((
        (machine (:= v 4)
                 ((dvar v 4)))
        ⊥
        zero))))



  (test-case "bugs"
    (test-equal
     (do `(loop go (present t (· (hat pause)) nothing)))
     `(( (loop stop (· (present t pause nothing))) ⊥ ⊥ () )))
    (test-equal
     (do `(trap (· (signal T (hat pause)))))
     `(( (trap (signal T ⊥ (· (hat pause))))
         ⊥
         ⊥
         ())))
    (test-equal
     (do `(· (signal T (hat pause))))
     `(( (signal T ⊥ (· (hat pause)))
         ⊥
         ⊥
         ()  )))
    (test-equal (do `(· (par nothing nothing)))
                `(( (par (· nothing) ⊥ (· nothing) ⊥) ⊥ ⊥ () )))

    (test-equal (do `(par (· nothing) ⊥ nothing zero))
                `(( (par nothing zero nothing zero) ⊥ ⊥ () )))

    (test-equal (do `(par nothing zero nothing zero))
                `(( (par nothing nothing) ⊥ zero () )))

    (test-equal
     (do* (· (seq (shared c := 1 nothing) (suspend pause plU)))
          ((dshared c 1 old)))
     `((
        (machine
         (seq (·(shared c := 1 nothing)) (suspend pause plU))
         ((dshared c 1 old)))
        ⊥
        ⊥
        )))
    (test-equal
     (do*  (seq (· (shared c := 1 nothing)) (suspend pause plU))
           ((dshared c 1 old)))
     `((
        (machine
         (seq (shared c := 1 (· nothing)) (suspend pause plU))
         ((dshared c 1 old)))
        ⊥
        ⊥
        )))))

(define-judgment-form esterel-eval
  #:mode     (→* I I O  O      O)
  #:contract (→* M E M (S ...) k)
  [(→ (machine pdotdot data) E
      (machine pdotdot_* data_*) ⊥ k)
   -----------
   (→* (machine pdotdot data) E
       (machine pdotdot_* data_*) () k)]

  [(→ (machine pdotdot data) E
      (machine pdotdot_* data) S k)
   -----------
   (→* (machine pdotdot data) E
       (machine pdotdot_* data) (S) k)]

  [(→ (machine pdotdot data) E
      (machine pdotdot_* data_*) S ⊥)
   (→* (machine pdotdot_* data_*) E
       (machine pdotdot_** data_**) (S_r ...) k)
   -----------
   (→* (machine pdotdot data) E
       (machine pdotdot_** data_**) (U (S) (S_r ...)) k)]

  [(→ (machine pdotdot data) E
      (machine pdotdot_* data_*) ⊥ ⊥)
   (→* (machine pdotdot_* data_*) E
       (machine pdotdot_** data_**) (S ...) k)
   -----------
   (→* (machine pdotdot data) E
       (machine pdotdot_** data_**) (S ...) k)])

(define-judgment-form esterel-eval
  ;; constructive ->>
  #:mode     (c->> I I O  O      O)
  #:contract (c->> M E M (S ...) k)
  [(→* (machine (· pbar) data) E (machine pbar_* data_*) (S ...) k)
   (side-condition ,(not (equal? `k `⊥)))
   -------
   (c->> (machine pbar data) E (machine pbar_* data_*) (S ...) k)])

(define-metafunction esterel
  free-emitted-signals : pbar  -> (S ...)
  [(free-emitted-signals nothing) ()]
  [(free-emitted-signals pause) ()]
  [(free-emitted-signals (hat pause)) ()]
  [(free-emitted-signals (seq pbar qbar))
   (U (free-emitted-signals pbar) (free-emitted-signals qbar))]
  [(free-emitted-signals (par pbar qbar))
   (U (free-emitted-signals pbar) (free-emitted-signals qbar))]
  [(free-emitted-signals (loop pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (suspend pbar S)) (free-emitted-signals pbar)]
  [(free-emitted-signals (present S pbar qbar))
   (U (free-emitted-signals pbar) (free-emitted-signals qbar))]
  [(free-emitted-signals (trap pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (exit _)) ()]
  [(free-emitted-signals (emit S)) (S)]
  [(free-emitted-signals (var v := call pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (shared s := call pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (signal S pbar)) (without_s (free-emitted-signals pbar) S)]
  [(free-emitted-signals (:= v call)) ()]
  [(free-emitted-signals (<= s call)) ()])

(define-metafunction esterel
  free-signal-vars : pbar -> (S ...)
  [(free-signal-vars nothing) ()]
  [(free-signal-vars pause) ()]
  [(free-signal-vars (hat pause)) ()]
  [(free-signal-vars (seq pbar qbar))
   (U (free-signal-vars pbar) (free-signal-vars qbar))]
  [(free-signal-vars (par pbar qbar))
   (U (free-signal-vars pbar) (free-signal-vars qbar))]
  [(free-signal-vars (loop pbar)) (free-signal-vars pbar)]
  [(free-signal-vars (suspend pbar S)) (U (S) (free-signal-vars pbar))]
  [(free-signal-vars (present S pbar qbar))
   (U (S)
      (U (free-signal-vars pbar) (free-signal-vars qbar)))]
  [(free-signal-vars (trap pbar)) (free-signal-vars pbar)]
  [(free-signal-vars (exit _)) ()]
  [(free-signal-vars (emit S)) (S)]
  [(free-signal-vars (var v := call pbar)) (free-signal-vars pbar)]
  [(free-signal-vars (shared s := call pbar)) (free-signal-vars pbar)]
  [(free-signal-vars (signal S pbar)) (without_s (free-signal-vars pbar) S)]
  [(free-signal-vars (:= v call)) ()]
  [(free-signal-vars (<= s call)) ()])


(module+ test
  (define-extended-language esterel-check esterel-eval
    (p-check
     nothing
     pause
     (seq p-check p-check)
     (par p-check p-check)
     (trap p-check)
     (exit nat)
     (signal S p-check)
     (suspend p-check S)
     (present S p-check p-check)
     (emit S)
     (shared s := call p-check+sset)
     (var v := call p-check+vset))

    (p-check+sset
     p-check
     (seq p-check+sset p-check+sset)
     (par p-check+sset p-check+sset)
     (trap p-check+sset)
     (exit nat)
     (signal S p-check+sset)
     (suspend p-check+sset S)
     (present S p-check+sset p-check+sset)
     (var v := call p-check+sset+vset)
     (<= s call))

    (p-check+vset
     p-check
     (seq p-check+vset p-check+sset)
     (par p-check+vset p-check)
     (trap p-check+vset)
     (exit nat)
     (signal S p-check+vset)
     (suspend p-check+vset S)
     (present S p-check+vset p-check+vset)

     (shared s := call p-check+sset+vset)
     (:= v call))

    (p-check+sset+vset
     p-check+vset
     p-check+sset)

    (phat-check
     (hat pause)
     ;; loops only present here to force loops to be non-instantanious
     (loop phat-check)
     (suspend phat-check S)
     (seq phat-check p-check)
     (seq p-check phat-check)
     ;; force a phat for the sake of loop safety
     (present S phat-check phat-check)
     (par phat-check phat-check)
     (trap phat-check)
     (signal S phat-check)
     (shared s := call phat-check+sset))
    (phat-check+sset
     phat-check
     (loop phat-check+sset)
     (suspend phat-check+sset S)
     (seq phat-check+sset p-check+sset)
     (seq p-check+sset phat-check+sset)
     ;; force a phat for the sake of loop safety
     (present S phat-check+sset phat-check+sset)
     (par phat-check+sset phat-check+sset)
     (trap phat-check+sset)
     (signal S phat-check+sset))
    (pbar-check p-check phat-check)

    (NL ()
        (nat NL))
    )

  (define-judgment-form esterel-eval
  ;; constructive ->>, with testing checks
  #:mode     (cc->> I I O O       O)
  #:contract (cc->> M E M (S ...) k)
  [(where (((machine qbar_r data_r*) (S_r ...) k_r) ...)
          ,(judgment-holds
            (c->> (machine pbar data) E (machine qbar data_*) (S ...) k)
            ((machine qbar data_*) (S ...) k)))
   (where (((machine qbar data_*) (S ...) k) any_2 ...)
          (((machine qbar_r data_r*) (S_r ...) k_r) ...))
   (where #t ,(andmap (curry equal? `k)
                      `(k_r ...)))
   (where #t ,(andmap (lambda (M) (alpha-equivalent? esterel-eval `(machine qbar data_*) M))
                      `((machine qbar_r data_r*) ...)))
   ;(side-condition ,(displayln `(free-signals pbar)))
   ;(side-condition ,(displayln `((∈ S (free-signals pbar)) ...)))
   (where (#t ...) ((∈ S (free-emitted-signals pbar)) ...))
   (where E_2 (Can_S pbar ()))
   ;(side-condition ,(displayln `((∈ (S one) E) ...)))
   (where (#t ...) ((∈ (S (Succ zero)) E_2) ...))
   (where #t
          ,(for*/and ([Sl1 (in-list `((S_r ...) ...))]
                      [Sl2 (in-list `((S_r ...) ...))])
             (equal? (list->set Sl1) (list->set Sl2))))
   (bars-match qbar k)
   -------
   (cc->> (machine pbar data) E (machine qbar data_*) (S ...) k)])

  (define-judgment-form esterel-eval
    #:mode (bars-match I I)
    #:contract (bars-match pbar k)
    [-------
     (bars-match p zero)]
    [-------
     (bars-match phat (Succ zero))])

  (define-metafunction esterel-eval
    random-E : (S ...) -> E
    [(random-E (S ...))
     ((random-E_S S) ...)])

  (define-metafunction esterel-eval
    random-E_S : S -> (S k)
    [(random-E_S S)
     (S ,(if (> (random) 0.5) `zero `(Succ zero)))])

  (define-judgment-form esterel-eval
    #:mode (->*/final I I O O O)
    [(→* (machine pdotdot data) E (machine qdotdot data_*) (S ...) k)
     (where #f ,(judgment-holds (→ (machine qdotdot data) E _ _ _)))
     -------------
     (->*/final (machine pdotdot data) E (machine qdotdot data_*) (S ...) k)])

  (test-case "eval bugs"
    (test-judgment-holds
     (c->>
      (machine (par (signal f (emit S)) (shared v := 1 pause)) ()) ()
      (machine (par (signal S_f (emit S_S)) (shared v := 1 (hat pause))) ((dshared v 1 ready)))
      (S_S)
      (Succ zero)))
    (test-judgment-holds
     (cc->>
      (machine (par (signal f (emit S)) (shared v := 1 pause)) ()) ()
      (machine (par (signal S_f (emit S_S)) (shared v := 1 (hat pause))) ((dshared v 1 ready)))
      (S_S)
      (Succ zero)))

    #|
    (test-judgment-holds
     (c->>
      (seq (loop (present h nothing (hat pause))) (trap (exit (Succ (Succ zero)))))
      ))
    |#
    (test-judgment-holds
     (c->>
      (machine
       (present Q (par pause nothing) (signal z nothing))
       ())
      ((Q one))

      (machine
       (present S_Q (par (hat pause) nothing) (signal S_z nothing))
       ())
      ()
      (Succ zero)))
    (test-judgment-holds
     (c->>
      (machine
       (seq (trap (signal X (emit p))) (suspend (signal g pause) UU))
       ())
      ((g one) (X zero))
      (machine (seq (trap (signal S_X (emit S_p)))
                    (suspend (signal S_g (hat pause)) S_U))
               ())
      (S_p)
      (Succ zero)))
    (test-judgment-holds
     (c->>
      (machine
       (seq (suspend (loop (seq (hat pause) (emit QY))) t) (signal f (trap nothing)))
       ())
      ((t zero))
      (machine
       (seq (suspend (loop (seq (hat pause) (emit S_QY))) S_t) (signal f (trap nothing)))
       ())
      (S_QY)
      (Succ zero)))
    (test-judgment-holds
     (c->>
      (machine
       (seq (suspend (hat pause) N) (signal k (emit Z)))
       ())
      ((N zero))
      (machine
       (seq (suspend pause S_N) (signal S_k (emit S_Z)))
       ())
      (S_Z)
      zero))
    (test-judgment-holds
     (c->>
      (machine
       (seq (trap (hat pause)) (signal n (emit h)))
       ())
      ()
      (machine
       (seq (trap pause) (signal S_n (emit S_h)))
       ())
      (S_h)
      zero))
    (test-judgment-holds
     (cc->>
      (machine
       (seq (trap (hat pause)) (signal n (emit h)))
       ())
      ()
      (machine
       (seq (trap pause) (signal S_n (emit S_h)))
       ())
      (S_h)
      zero))
    (test-judgment-holds
     (cc->>
      (machine
       (seq (loop (hat pause)) (trap nothing))
       ())
      ()
      (machine
       (seq (loop (hat pause)) (trap nothing))
       ())
      ()
      one))
    (test-judgment-holds
     (cc->>
      (machine
       (signal A (signal Gz (emit H)))
       ())
      ()
      (machine
       (signal S_A (signal S_Gz (emit S_H)))
       ())
      (S_H)
      zero))
    (test-judgment-holds
     (cc->>
      (machine
       (trap (trap (exit (Succ two))))
       ())
      ()
      (machine
       (trap (trap (exit (Succ two))))
       ())
      ()
      zero))

    (test-judgment-holds
     (cc->>
      (machine
       (seq (trap (trap (exit (Succ two)))) (signal A (signal Gz (emit H))))
       ())
      ()
      (machine
       (seq (trap (trap (exit (Succ two)))) (signal S_A (signal S_Gz (emit S_H))))
       ())
      (S_H)
      zero))

    (test-judgment-holds (cc->>
                          (machine
                           (loop (hat pause))
                           ())
                          ()
                          (machine
                           (loop (hat pause))
                           ())
                          ()
                          one))
    (test-judgment-holds (cc->>
                          (machine
                           (seq (emit z) (loop pause))
                           ())
                          ()
                          (machine
                           (seq (emit S_z) (loop (hat pause)))
                           ())
                          (z)
                          one))
    (test-judgment-holds (cc->>
                          (machine
                           (seq (emit z) (loop (hat pause)))
                           ())
                          ()
                          (machine
                           (seq (emit S_z) (loop (hat pause)))
                           ())
                          ()
                          one))
    (test-judgment-holds (cc->>
                          (machine
                           (trap (trap (exit (Succ two))))
                           ())
                          ()
                          any_1
                          any_2
                          any_3))
    (test-judgment-holds
     (cc->>
      (machine
       (seq (trap (trap (exit (Succ two)))) (signal IH nothing))
       ())
      ()
      (machine
       (seq (trap (trap (exit (Succ two)))) (signal S_IH nothing))
       ())
      ()
      zero))

    (test-judgment-holds
     (cc->>
      (machine
       (par (seq (emit Q) (emit Q)) (signal S pause))
       ())
      ()
      (machine
       (par (seq (emit S_Q) (emit S_Q)) (signal S_v (hat pause)))
       ())
      (Q)
      one)))

  (define-judgment-form esterel-check
    #:mode (traps-okay I I)
    #:contract (traps-okay pbar NL)

    [(traps-okay (exit nat_h) NL)
     -----------
     (traps-okay (exit nat_h) (nat_h NL))]

    [-----------
     (traps-okay (exit nat_h) (nat_h NL))]

    [(traps-okay pbar ((Succ (Succ zero)) ()))
     ----------
     (traps-okay (trap pbar) ())]

    [(traps-okay pbar ((Succ nat) (nat NL)))
     ----------
     (traps-okay (trap pbar) (nat NL))]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (loop pbar) NL)]

    [---------
     (traps-okay nothing any)]

    [---------
     (traps-okay pause any)]

    [---------
     (traps-okay (hat pause) any)]

    [---------
     (traps-okay (emit S) any)]

    [(traps-okay pbar_l NL)
     (traps-okay pbar_r NL)
     ---------
     (traps-okay (seq pbar_l pbar_r) NL)]

    [(traps-okay pbar_l NL)
     (traps-okay pbar_r NL)
     ---------
     (traps-okay (present S pbar_l pbar_r) NL)]

    [(traps-okay pbar_l NL)
     (traps-okay pbar_r NL)
     ---------
     (traps-okay (par pbar_l pbar_r) NL)]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (signal S pbar) NL)]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (suspend pbar S) NL)]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (shared s := call pbar) NL)]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (var v := call pbar) NL)]

    [---------
     (traps-okay (<= s call) NL)]

    [---------
     (traps-okay (:= v call) NL)]

    [(traps-okay pbar NL)
     (traps-okay qbar NL)
     ---------
     (traps-okay (if v pbar qbar) NL)])

  (define-judgment-form esterel-check
    #:mode (loops-okay I)
    #:contract (loops-okay pbar)
    [-----------
     (loops-okay (exit nat_h))]

    [-----------
     (loops-okay (exit nat_h))]

    [(loops-okay pbar)
     ----------
     (loops-okay (trap pbar))]

    [---------
     (loops-okay nothing)]

    [---------
     (loops-okay pause)]

    [---------
     (loops-okay (hat pause))]

    [---------
     (loops-okay (emit S))]

    [(loops-okay pbar_l)
     (loops-okay pbar_r)
     ---------
     (loops-okay (seq pbar_l pbar_r))]

    [(loops-okay pbar_l)
     (loops-okay pbar_r)
     ---------
     (loops-okay (present S pbar_l pbar_r))]

    [(loops-okay pbar_l)
     (loops-okay pbar_r)
     ---------
     (loops-okay (par pbar_l pbar_r))]

    [(loops-okay pbar)
     ---------
     (loops-okay (signal S pbar))]

    [(loops-okay pbar)
     ---------
     (loops-okay (suspend pbar S))]

    [(loops-okay pbar)
     (K_s pbar (k ...))
     (where #f (∈ zero (k ...)))
     ---------
     (loops-okay (loop pbar))]
    )

  (define-judgment-form esterel-check
    #:mode (K_s I O)
    #:contract (K_s pbar (k ...))
    [----------
     (K_s nothing (zero))]
    [----------
     (K_s pause ((Succ zero)))]
    [----------;; identical. we're pretending its a p
     (K_s (hat pause) ((Succ zero)))]
    [----------
     (K_s (exit k) (k))]

    [(K_s pbar (k_1 ...))
     (K_s qbar (k_2 ...))
     ----------
     (K_s (present S pbar qbar) (U (k_2 ...) (k_2 ...)))]
    [(K_s pbar (k ...))
     ----------
     (K_s (suspend S pbar) (k ...))]
    [(K_s pbar (k_1 ...))
     (K_s qbar (k_2 ...))
     (where #t (∈ 0 (k_1 ...)))
     ----------
     (K_s (seq pbar qbar) (U (k_2 ...) (without zero (k_1 ...))))]
    [(K_s pbar (k ...))
     (where #f (∈ 0 (k ...)))
     ----------
     (K_s (seq pbar qbar) (k ...))]
    [(K_s pbar (k ...))
     ----------
     (K_s (loop pbar) (without zero (k ...)))]
    [(K_s pbar (k_1 ...))
     (K_s qbar (k_2 ...))
     ----------
     (K_s (seq pbar qbar) (metamax (k_2 ...) (k_1 ...)))]
    [(K_s pbar (k ...))
     ----------
     (K_s (trap pbar) (↓ (k ...)))]
    [(K_s pbar (k ...))
     ----------
     (K_s (suspend S pbar) (k ...))])

  (define-metafunction esterel-eval
    fix-env : M -> M

    [(fix-env (machine (exit nat_h) data))
     (machine (exit nat_h) data)]

    [(fix-env (machine pause data))
     (machine pause data)]

    [(fix-env (machine (hat pause) data))
     (machine (hat pause) data)]

    [(fix-env (machine nothing data))
     (machine nothing data)]

    [(fix-env (machine (emit S) data))
     (machine (emit S) data)]

    [(fix-env (machine (trap pbar) data))
     (machine (trap pbar_*) data_*)
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

    [(fix-env (machine (loop pbar) data))
     (machine (loop pbar_*) data_*)
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

    [(fix-env (machine (signal S pbar) data))
     (machine (signal S pbar_*) data_*)
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

    [(fix-env (machine (suspend pbar S) data))
     (machine (suspend pbar_* S) data_*)
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))]

    [(fix-env (machine (seq pbar qbar) data))
     (machine (seq pbar_* qbar_*) (U data_* data_**))
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))
     (where (machine qbar_* data_**) (fix-env (machine qbar data)))]

    [(fix-env (machine (par pbar qbar) data))
     (machine (par pbar_* qbar_*) (U data_* data_**))
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))
     (where (machine qbar_* data_**) (fix-env (machine qbar data)))]

    [(fix-env (machine (present S pbar qbar) data))
     (machine (present S pbar_* qbar_*) (U data_* data_**))
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))
     (where (machine qbar_* data_**) (fix-env (machine qbar data)))]

    [(fix-env (machine (shared s := call phat) data))
     (machine (shared s := call_* phat_*) data_**)
     (where call_* (delete-bad-var-call s data call))
     (where data_* (data<- data s (eval-call call_* data) ready))
     (where (machine phat_* data_**) (fix-env (machine phat data_*)))]

    [(fix-env (machine (shared s := call p) data))
     (machine (shared s := call_* p_*) data_**)
     (where call_* (delete-bad-var-call s data call))
     (where data_* (data<- data s (eval-call call_* data) old))
     (where (machine p_* data_**) (fix-env (machine p data_*)))]

    [(fix-env (machine (<= s call) data))
     (machine (<= s_* call_*) data)
     (where s_* (visible-s s data))
     (where call_* (delete-bad-var-call s_* data call))]

    [(fix-env (machine (var v := call pbar) data))
     (machine (var v := call_* pbar_*) data_**)
     (where call_* (delete-bad-var-call ,(gensym) data call))
     (where data_* (data<- data v (eval-call call_* data)))
     (where (machine pbar_* data_**) (fix-env (machine pbar data_*)))]

    [(fix-env (machine (:= v call) data))
     (machine (:= v_* call_*) data)
     (where v_* (visible-v v data))
     (where call_* (delete-bad-var-call ,(gensym) data call))]

    [(fix-env (machine (if v pbar qbar) data))
     (machine (if v_* pbar_* qbar_*) (U data_* data_**))
     (where v_* (delete-bad-var-call ,(gensym) data v))
     (where (machine pbar_* data_*) (fix-env (machine pbar data)))
     (where (machine qbar_* data_**) (fix-env (machine qbar data)))])

  (define-metafunction esterel-eval
    visible-s : s data -> s
    [(visible-s s data)
     s
     (where #t (∈ s (get-shared data)))]
    [(visible-s s data) (get-random-s data)])

  (define-metafunction esterel-eval
    visible-v : v data -> v
    [(visible-v v data)
     s
     (where #t (∈ v (get-shared data)))]
    [(visible-v v data) (get-random-v data)])


  (define-metafunction esterel-eval
    get-shared : data -> (s ...)
    [(get-shared ()) ()]
    [(get-shared ((dshared s any_1 any_2) data-elem ...))
     (s s_r ...)
     (where (s_r ...) (get-shared (data-elem ...)))]
    [(get-shared ((dvar any_1 any_2) data-elem ...))
     (get-shared (data-elem ...))])

  (define-metafunction esterel-eval
    get-random-s : data -> s
    [(get-random-s data)
     ,(random-ref `(s ...))
     (where (s ...) (get-shared data))])

  (define-metafunction esterel-eval
    get-random-v : data -> s
    [(get-random-v data)
     ,(random-ref `(v ...))
     (where (v ...) (get-unshared data))])

  (define-metafunction esterel-eval
    get-unshared : data -> (v ...)
    [(get-unshared ()) ()]
    [(get-unshared ((dvar v any) data-elem ...))
     (v v_r ...)
     (where (v_r ...) (get-unshared (data-elem ...)))]
    [(get-unshared (any data-elem ...))
     (v_r ...)
     (where (v_r ...) (get-unshared (data-elem ...)))])



  (define-metafunction esterel-eval
    delete-bad-var-call : s data call -> call
    [(delete-bad-var-call s data datum) datum]
    [(delete-bad-var-call s data (+ call ...))
     (+ (delete-bad-var-call s data call) ...)]
    [(delete-bad-var-call s data s) 1]
    [(delete-bad-var-call s_0 data s_1)
     s_1
     (where #t (∈ s_1 (get-shared data)))]
    [(delete-bad-var-call s_0 data s_1) 1])

  (define-extended-language uniquify-lang esterel-eval
    #:binding-forms
    (shared s := call pbar #:refers-to s)
    (var v := call pbar #:refers-to v))
  (define-metafunction uniquify-lang
    ;uniquify : pbar -> pbar
    [(uniquify (any ...))
     ((uniquify any) ...)]
    [(uniquify any) any])


  (define-judgment-form esterel-check
    #:mode     (okay I)
    #:contract (okay pbar)
    [(traps-okay pbar ())
     --------
     (okay pbar)]))

(module+ slow
  (require (submod ".." test))
  (test-case "slow tests"
    (time ;; failing
     (test-judgment-holds
      (cc->>
       (machine
        (par (signal TY (signal a nothing))
             (signal S (par (par (emit R) pause)
                            pause)))
        ())
       ()
       (machine (par (signal S_TY (signal S_a nothing))
                     (signal S_S (par (par (emit S_R) (hat pause))
                                      (hat pause))))
                ())
       (R)
       one)))
    (time ;; failing
     (test-judgment-holds
      (cc->>
       (machine
        (par (signal K (signal Z (par nothing pause))) (signal R nothing))
        ())
       ()
       (machine
        (par (signal S_K (signal S_Z (par nothing (hat pause)))) (signal S_R nothing))
        ())
       ()
       one)))))

(module+ random
  (require (submod ".." test))
  (define-syntax-rule (tjh e)
    (begin
      (test-judgment-holds e)
      (judgment-holds e)))
  (test-case "random tests"
    ;(current-traced-metafunctions 'all)
    (redex-check
     esterel-check
     #:satisfying (okay p-check)
     (begin
       ;(displayln `p-check)
       (tjh (cc->> (fix-env (machine (uniquify p-check) ()))
                   (random-E (free-signal-vars p-check))
                   (machine pbar data_*) (S ...) k)))
     #:attempts 333
     )
    (redex-check
     esterel-check
     #:satisfying (okay phat-check)
     (begin
       ;(displayln `phat-check)
       (tjh (cc->> (fix-env (machine (uniquify phat-check) ()))
                   (random-E (free-signal-vars phat-check))
                   (machine pbar data_*) (S ...) k)))
     #:attempts 333
     )
    (redex-check
     esterel-check
     #:satisfying (okay pbar-check)
     (begin
       ;(displayln `pbar-check)
       (tjh (cc->> (fix-env (machine (uniquify pbar-check) ()))
                   (random-E (free-signal-vars pbar-check))
                   (machine pbar data_*) (S ...) k)))
     #:attempts 333
     )))

(module+ test
  (test-case "eval part 2"
    (test-judgment-holds
     (c->>
      (machine (par (signal pQ (emit x)) (emit C)) ())
      ()
      (machine (par (signal S_pQ (emit S_x)) (emit S_C)) ())
      any
      zero))
    (test-judgment-holds
     (cc->>
      (machine (par (signal pQ (emit x)) (emit C)) ())
      ()
      (machine (par (signal S_pQ (emit S_x)) (emit S_C)) ())
      any
      zero))
    (test-judgment-holds
     (c->>
      (fix-env
       (machine
        (seq (shared c := Q nothing) (suspend pause plU))
        ()))
      ()
      (machine (seq (shared s_c := 1 nothing)
                    (suspend (hat pause) S_p))
               ((dshared s_c 1 ready)))
      ()
      (Succ zero)))
    (test-judgment-holds
     (cc->>
      (fix-env
       (machine
        (seq (shared c := Q nothing) (suspend pause plU))
        ()))
      ()
      (machine (seq (shared s_c := 1 nothing)
                    (suspend (hat pause) S_p))
               ((dshared s_c 1 ready)))
      ()
      (Succ zero)))))

(module+ all (require (submod ".." test) (submod ".." slow) (submod ".." random)))

(define-metafunction esterel-eval
  remove-selected : pdotdot -> p
  [(remove-selected p) p]
  [(remove-selected (· pbar)) (remove-selected pbar)]
  [(remove-selected (hat pause)) pause]
  [(remove-selected (present S pdotdot qdotdot))
   (present S (remove-selected pdotdot) (remove-selected qdotdot))]
  [(remove-selected (suspend S pdotdot)) (suspend S (remove-selected pdotdot))]
  [(remove-selected (seq pdotdot qdotdot))
   (seq (remove-selected pdotdot) (remove-selected qdotdot))]
  [(remove-selected (suspend pdotdot S)) (suspend (remove-selected pdotdot) S)]
  [(remove-selected (loop pdotdot)) (loop (remove-selected pdotdot))]
  [(remove-selected (loop lstat pdotdot)) (loop (remove-selected pdotdot))]
  [(remove-selected (par pdotdot qdotdot))
   (par (remove-selected pdotdot) (remove-selected qdotdot))]
  [(remove-selected (par pdotdot any_1 qdotdot any_2))
   (par (remove-selected pdotdot) (remove-selected qdotdot))]
  [(remove-selected (trap pdotdot)) (trap (remove-selected pdotdot))]
  [(remove-selected (var v := call pdotdot))
   (var v := call (remove-selected pdotdot))]
  [(remove-selected (shared s := call pdotdot))
   (shared s := call (remove-selected pdotdot))]
  [(remove-selected (signal S pdotdot))
   (signal S (remove-selected pdotdot))]
  [(remove-selected (signal S sstat pdotdot))
   (signal S (remove-selected pdotdot))])

(define-metafunction esterel-eval
  #|
  ↓ : k or (k ...) -> k or (k ...)
  |#
 [(↓ zero) zero]
 [(↓ two) zero]
 [(↓ one) one]
 [(↓ nat) (nat- nat one)]
 [(↓ (k ...)) ((↓ k) ...)])

(module+ test
  (test-case "Can bugs"
    ;(current-traced-metafunctions '(Can Can_V))
    (test-equal
     `(Can (present S pause (trap (emit A))) ())
     `( ((A (Succ zero)))
        ((Succ zero) zero)
        () ))
    (test-equal
     `(Can (suspend (loop (seq (hat pause) (emit QY))) tt) ())
     `( ((QY (Succ zero)))
        ((Succ zero))
        () ))
    (test-equal
     `(Can (suspend (hat pause) xJux) ())
     `( () ((Succ zero) zero) () ))
    (test-equal
     `(Can_S (seq (· (emit S)) pause) ((S ⊥)))
     `((S one)))
    (test-equal
     `(Can_S (seq (· (hat pause)) (emit S)) ())
     `((S one)))
    (test-equal
     `(Can_K (· (hat pause)) ())
     `(zero))
    (test-equal
     `(∉ zero (Can_K (· (hat pause)) ()))
     #f)))

(define-metafunction esterel-eval
  Can : pdotdot E -> (E K V)

  [(Can (· pbar) E) (Can pbar E)]

  [(Can (present S pdot q) E) (Can pdot E)]

  [(Can (present S p qdot) E) (Can qdot E)]

  [(Can (suspend pdot S) E) (Can pdot E)]

  [(Can (if v pdot q) E) (Can pdot E)]

  [(Can (if v p qdot) E) (Can qdot E)]

  [(Can (seq pdot q) E)
   (Can pdot E)
   (side-condition `(∉ zero (Can_K pdot E)))]

  [(Can (seq pdot q) E)
   ((U (Can_S pdot E) (Can_S q E))
    (U (without (Can_K pdot E) (zero))
       (Can_K q E))
    (U (Can_V pdot E)
       (Can_V q E)))
   (side-condition `(∈ zero (Can_K pdot E)))]

  [(Can (seq p qdot) E)
   (Can qdot E)]

  [(Can (par pdot ⊥ qdot ⊥) E)
   ((U (Can_S pdot E)
       (Can_S qdot E))
    ((meta-max (Can_K pdot E)
                (Can_K qdot E)))
    (U (Can_V pdot E)
       (Can_V qdot E)))]

  ;; TODO should this be qbar? (page 112)
  ;; FIXING, listed as q, fails if not qbar
  [(Can (par pdot ⊥ qbar k) E)
   ((Can_S pdot E)
    ((meta-max (Can_K pdot E) (k)))
    (Can_V pdot E))]

  ;; FIXING, listed as p, fails if not pbar
  [(Can (par pbar k qdot ⊥) E)
   ((Can_S qdot E)
    ((meta-max (Can_K qdot E) (k)))
    (Can_V qdot E))]

  ;; FIXING, listed as p/q, fails if not pbar/qbar
  [(Can (par pbar k qbar l) E)
   (() ((meta-max k l)) ())]

  [(Can (loop go pdot) E)
   ((U (Can_S pdot E) (Can_S p E))
    (U (without (Can_K pdot E) (zero))
       (Can_K p E))
    (U (Can_V pdot E)
       (Can_V p E)))
   (where p (remove-selected pdot))
   (side-condition `(∈ zero (Can_K pdot E)))]

  [(Can (loop lstat pdot) E)
   (Can pdot E)]

  [(Can (signal S sstat pdot) E)
   (without (Can pdot (* E (S sstat))) S)]

  [(Can (trap pdot) E)
   ((Can_S pdot E) (↓ (Can_K pdot E)) (Can_V pdot E))]

  [(Can (var v := call pdot) E)
   (Can pdot E)]

  [(Can (shared s := call pdot) E)
   (without_s (Can pdot E) s)]

  [(Can (:= v call) E)
   (() (zero) ())]

  [(Can (<= s call) E)
   (() (zero) (s))]

  [(Can (var v := call pbar) E) (Can pbar E)]
  [(Can (if v p q) E) (U (Can p E) (Can q E))]

  [(Can (if v phat q) E) (Can phat E)]

  [(Can (if v p qhat) E) (Can qhat E)]

  [(Can (shared s := call pbar) E) (without_s (Can pbar E) s)]

  ;; from ch 3 (starts at 77)
  [(Can nothing E) (() (zero) ())]

  [(Can pause E) (() (one) ())]

  [(Can (exit k) E) (() (k) ())]

  [(Can (emit S) E) (((S one)) (zero) ())]

  [(Can (present S p q) E)
   (Can p E)
   (side-condition `(∈ (S one) E))]

  [(Can (present S p q) E)
   (Can q E)
   (side-condition `(∈ (S zero) E))]

  [(Can (present S p q) E)
   (U (Can p E) (Can q E))
   (side-condition `(∈ (S ⊥) E))]

  [(Can (suspend p S) E)
   (Can p E)]

  [(Can (seq p q) E)
   (Can p E)
   (side-condition `(∉ zero (Can_K p E)))]

  [(Can (seq p q) E)
   ( (U (Can_S p E) (Can_S q E))
     (U (without (Can_K p E) (zero))
        (Can_K q E))
     (U (Can_V p E) (Can_V q E)) )]

  [(Can (loop p) E)
   (Can p E)]

  [(Can (par p q) E)
   ( (U (Can_S p E) (Can_S q E))
     ((meta-max (Can_K p E) (Can_K q E)))
     (U (Can_V p E) (Can_V q E)) )]

  [(Can (trap p) E)
   ( (Can_S p E)
     (↓ (Can_K p E))
     (Can_V p E) )]

  [(Can (signal S p) E)
   (without (Can p (* E (S zero))) S)
   (side-condition `(∉ (S one) (Can_S p (* E (S ⊥)))))]

  [(Can (signal S p) E)
   (without (Can p (* E (S ⊥))) S)]

  [(Can (hat pause) E)
   ( () (zero) () )]

  [(Can (present S phat q) E)
   (Can phat E)]

  [(Can (present S p qhat) E)
   (Can qhat E)]

  [(Can (suspend phat S) E)
   ( () (one) () )
   (side-condition `(∈ (S one) E))]

  [(Can (suspend phat S) E)
   (Can phat E)
   (side-condition `(∈ (S zero) E))]

  [(Can (suspend phat S) E)
   ( E_o (U ((Succ zero)) (k ...)) (v ...) )
   (where (E_o (k ...) (v ...)) (Can phat E))
   (side-condition `(∈ (S ⊥) E))]

  [(Can (seq p qhat) E)
   (Can qhat E)]

  [(Can (seq phat q) E)
   (Can phat E)
   (side-condition `(∉ zero (Can_K phat E)))]

  [(Can (seq phat q) E)
   ( (U (Can_S phat E) (Can_S q E))
     (U (without (Can_K phat E) (zero))
        (Can_K q E))
     (U (Can_V phat E) (Can_V q E)))]

  [(Can (loop phat) E)
   (Can phat E)
   (side-condition `(∉ zero (Can_K phat E)))]

  [(Can (loop phat) E)
   ( (U (Can_S phat E) (Can_S p E))
     (U (without (Can_K phat E) (zero)) (Can_K p E))
     (U (Can_V phat E) (Can_V p E)) )
   (where p (remove-selected phat))]

  [(Can (par phat q) E)
   (Can phat E)]

  [(Can (par p qhat) E)
   (Can qhat E)]

  [(Can (par phat qhat) E)
   ( (U (Can_S phat E) (Can_S qhat E))
     ((meta-max (Can_K phat E) (Can_K qhat E)))
     (U (Can_V phat E) (Can_V qhat E)) )]

  [(Can (trap phat) E)
   ( (Can_S phat E)
     (↓ (Can_K phat E))
     (Can_V phat E) )]

  [(Can (signal S phat) E)
   (without (Can phat (* E (S zero))) S)
   (side-condition `(∉ (S one) (Can_S phat (* E (S ⊥)))))]

  [(Can (signal S phat) E)
   (without (Can phat (* E (S ⊥))) S)])

(define-metafunction esterel-eval
  U : (any ...) (any ...) -> (any ...)
  ;; I suspect this case is wrong...?
  [(U E_1 E_2)
   (U_E E_1 E_2)]
  [(U (E_1 (k_1 ...) (v_1 ...))
      (E_2 (k_2 ...) (v_2 ...)))
   ( (U E_1 E_2)
     (U (k_1 ...) (k_2 ...))
     (U (v_1 ...) (v_2 ...)))]
  [(U () (any ...))
   (any ...)]
  [(U (any any_1 ...) (any_2 ...))
   (U (any_1 ...) (insert any (any_2 ...)))])

(define-metafunction esterel-eval
  ;; special case union for signal events
  U_E : E E -> E
  [(U_E () E) E]
  [(U_E ((S sstat) (S_1 sstat_1) ...) E)
   (U_E ((S_1 sstat_1) ...) (insert_E (S sstat) E))])

(define-metafunction esterel-eval
  insert_E : (S sstat) E -> E
  ;; if it was bot you Can replace it
  [(insert_E (S sstat) ((S_1 sstat_1) ... (S ⊥) (S_2 sstat_2) ...))
   ((S_1 sstat_1) ... (S sstat) (S_2 sstat_2) ...)]
  ;; if its present with the same sstat ignore
  [(insert_E (S sstat) ((S_1 sstat_1) ... (S sstat) (S_2 sstat_2) ...))
   ((S_1 sstat_1) ... (S sstat) (S_2 sstat_2) ...)]
  ;; if it is not present you Can add it
  [(insert_E (S sstat) ((S_1 sstat_1) ...))
   ((S sstat) (S_1 sstat_1) ...)
   (side-condition (not (member `S `(S_1 ...))))]
  ;; else idk what the behavior is
  ;; i think this means causally unsound program
  ;; so... error?
  ;; should never happen with Can?
  )

(define-metafunction esterel-eval
  insert : any (any ...) -> (any ...)
  [(insert any (any_1 ... any any_2 ...))
   (any_1 ... any any_2 ...)]
  [(insert any (any_1 ...))
   (any any_1 ...)])

(define-metafunction esterel-eval
  #|
  without :
  ((S sstat) ...) or (k ...) or (s ...) or (((S sstat) ...) (k ...) (s ...))
  S or (k ...) or s
  ->
  (k ...) or ((S sstat) ...) or (s ...) or (((S sstat) ...) (k ...) (s ...))
  |#

  [(without ((S_1 sstat_1) ... (S sstat) (S_2 sstat_2) ...) S)
   ((S_1 sstat_1) ... (S_2 sstat_2) ...)]
  [(without ((S_1 sstat_1) ... (S_2 sstat_2) ...) S)
   ((S_1 sstat_1) ... (S_2 sstat_2) ...)]

  #|
  [(without (s_1 ... s s_2 ...) s)
   (s_1 ... s_2 ...)]
  |#

  [(without (k ...) ()) (k ...)]

  [(without (k_1 ...) (k k_2 ...))
   (without (without (k_1 ...) k) (k_2 ...))]

  [(without (k_1 ... k k_2 ...) k)
   (k_1 ... k_2 ...)]

  [(without (k_1 ... k_2 ...) k)
   (k_1 ... k_2 ...)]

  [(without (E (k ...) (s ...)) S)
   ((without E S) (k ...) (s ...))]

  [(without (E (k ...) (s_1 ...)) s)
   (E (k ...) (without (s_1 ...) s))])

(define-metafunction esterel-eval
  #|
  without_s
  : (E (k ...) (s ...)) or (s ...)
  s
  -> (E (k ...) (s ...)) or (s ...)
  |#
  [(without_s (E (k ...) (s_1 ...)) s)
   (E (k ...) (without_s (s_1 ...) s))]
  [(without_s (s_1 ... s s_2 ...) s)
   (s_1 ... s_2 ...)]
  [(without_s (s_1 ...) s)
   (s_1 ...)])

(define-metafunction esterel-eval
  ∉ : any (any ...) -> boolean
  [(∉ any_1 (any_2 ...))
   ,(not `(∈ any_1 (any_2 ...)))])
(define-metafunction esterel-eval
  ∈
  : any (any ...) -> boolean
  ;; special case, page 67
  [(∈ (S ⊥) ((S_1 sstat) ...))
   #t
   (where #t (∉ S (S_1 ...)))]
  [(∈ any_1 (any_2 ... any_1 any_3 ...))
   #t]
  [(∈ any_1 (any_2 ...))
   #f])
(define-metafunction esterel-eval
  #|
  meta-max
  : (k ...) or k
  (k ...) or k
  ->
  (k) or k
  |#

  [(meta-max (k_1 ...) (k_2 ...))
   (meta-max k_1 ... k_2 ...)]
  [(meta-max k_1 k_2)
   k_2
   (where #t (nat<= k_1 k_2))]
  [(meta-max k_1 k_2)
   k_1]
  [(meta-max k_1 k_2 k_3 ...)
   (meta-max (meta-max k_1 k_2) k_3 ...)])

(define-metafunction esterel-eval
  * : E (S sstat) -> E
  [(* ((S_1 sstat_1) ...
       (S _)
       (S_2 sstat_2) ...)
      (S sstat))
   ((S_1 sstat_1) ...
    (S sstat)
    (S_2 sstat_2) ...)]
  [(* ((S_E sstat_E) ...)
      (S sstat))
   ((S sstat) (S_E sstat_E) ...)])

(define-metafunction esterel-eval
  Can_S : pdotdot E -> ((S sstat) ...)
  [(Can_S pdotdot E)
   ((S sstat) ...)
   (where (((S sstat) ...) _ _) (Can pdotdot E))])

(define-metafunction esterel-eval
  Can_K : pdotdot E -> (k ...)
  [(Can_K pdotdot E)
   (k ...)
   (where (_ (k ...) _) (Can pdotdot E))])

(define-metafunction esterel-eval
  Can_V : pdotdot E -> (s ...)
  [(Can_V pdot E)
   (s ...)
   (where (_ _ (s ...)) (Can pdot E))]
  [(Can_V pause E) ()]
  [(Can_V (hat pause) E) ()]
  [(Can_V (emit S) E) ()]
  [(Can_V (exit k) E) ()]
  [(Can_V (signal S pbar) E)
   (Can_V pbar  (* E (S ⊥)))
   (side-condition `(∈ (S one) (Can_S pbar (* E (S ⊥)))))]
  [(Can_V (signal S pbar) E)
   (Can_V pbar (* E (S zero)))]
  [(Can_V (present S p q))
   (Can_V p E)
   (side-condition `(∈ (S one) E))]
  [(Can_V (present S p q))
   (Can_V q E)
   (side-condition `(∈ (S zero) E))]
  [(Can_V (present S p q))
   (U (Can_V p E) (Can_V q E))
   (side-condition `(∈ (S ⊥) E))]
  [(Can_V (present S phat q) E)
   (Can_V phat E)]
  [(Can_V (present S p qhat) E)
   (Can_V qhat E)]
  [(Can_V (suspend S p) E)
   (Can_V p E)]
  [(Can_V (suspend S phat) E)
   ()
   (side-condition `(∈ (S one) E))]
  [(Can_V (suspend S phat) E)
   (Can_V phat E)]
  [(Can_V (trap pbar) E)
   (Can_V pbar E)]
  [(Can_V (par p q) E)
   (U (Can_V p E) (Can_V q E))]
  [(Can_V (par phat qhat) E)
   (U (Can_V phat E) (Can_V qhat E))]
  [(Can_V (par phat q))
   (Can_V phar E)]
  [(Can_V (par p qhat) E)
   (Can_V qhat E)]
  [(Can_V (seq pbar q) E)
   (U (Can_V pbar E) (Can_V q E))
   (side-condition `(∈ zero (Can_K pbar E)))]
  [(Can_V (seq pbar q) E)
   (Can_V pbar E)]
  [(Can_V (seq p qhat) E)
   (Can_V qhat E)]
  [(Can_V (loop p) E)
   (Can_V p E)]
  [(Can_V (loop phat) E)
   (U (Can_V phat E) (Can_V (remove-selected phat) E))
   (side-condition `(∈ zero (Can_K phat E)))]
  [(Can_V pdotdot E)
   V
   (where (_ _ V) (Can pdotdot E))])
