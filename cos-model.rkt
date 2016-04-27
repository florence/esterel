#lang racket
(require redex)
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
   (trap T p)
   (exit T k)
   (emit S)
   (var v p)
   (shared s p)
   (signal S p)
   (:= v call)
   (<= s call))

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
   (trap T phat)
   (var v phat)
   (shared s phat)
   (signal S phat))

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
   (trap T pdot)
   (var v pdot)
   (shared s pdot)
   (signal S sstat pdot))

  ;; for now the only value is numbers
  (call natural (+ call ...) v s)

  ((pdotdot qdotdot) pdot pbar)

  ((S T v s) variable-not-otherwise-mentioned)

  (lstat none stop go)
  (pstat ⊥ l k)
  ((l k m) nat)
  (sstat ⊥ one zero)
   #:binding-forms
   (signal S p #:refers-to S)
   (signal S phat #:refers-to S)
   (signal S sstat pdot #:refers-to S)
   (trap T p #:refers-to T)
   (trap T phat #:refers-to T)
   (trap T pdot #:refers-to T)
   )
(module+ test
  (test-case "grammar"
    (check-true
     (redex-match? esterel (exit T k) `(exit t zero)))
    (check-true
     (redex-match? esterel (exit T k) `(exit t one)))
    (check-true
     (redex-match? esterel (exit T k) `(exit t two)))
    (check-true
     (redex-match? esterel (exit T k) `(exit t (Succ (Succ zero)))))
    (check-true
     (redex-match? esterel (exit T k) `(exit t three)))))
(define-extended-language esterel-eval esterel
  ;(m P E Ss k data)
  (E ((S sstat) ...))
  (K (k ...))
  (V (v ...))
  (e ⊥ S)
  ((l k m) .... ⊥)
  (data (data-elem ...))
  (data-elem (v datum)
             (v datum shared-stat))
  (shared-stat ready old new))
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
  #:mode     (→ I       I    I O       O O O)
  #:contract (→ pdotdot data E pdotdot e k data)
  #|
  [------------
  ""
  (→ )]
  |#
  [------------
   "1"
   (→ (· nothing) data E
      nothing ⊥ zero data)]
  [------------
   "2"
   (→ (· pause) data E
      (hat pause) ⊥ (Succ zero) data)]
  [------------
   "3"
   (→ (· (hat pause)) data E
      pause ⊥ zero data)]
  [------------
   "4"
   (→ (· (seq pbar q)) data E
      (seq (· pbar) q) ⊥ ⊥ data)]

  [(→ pdot data E pdotdot e k data_*)
   (side-condition ,(not (equal? `k `zero)))
   ------------
   "5"
   (→ (seq pdot q) data E
      (seq pdotdot q) e k data_*)]

  [(→ pdot data E p e zero data_*)
   ------------
   "6"
   (→ (seq pdot q) data E
      (seq p (· q)) e ⊥ data_*)]

  [------------
   "7"
   (→ (· (seq p qhat)) data E
      (seq p (· qhat)) ⊥ ⊥ data)]
  [(→ qdot data E qdotdot e m data_*)
   ------------
   "8"
   (→ (seq p qdot) data E
      (seq p qdotdot) e m data_*)]
  [------------
  "9"
  (→ (· (par p q)) data E
     (par (· p) ⊥ (· q) ⊥) ⊥ ⊥ data)]
  [------------
  "10"
  (→ (· (par phat qhat)) data E
     (par (· phat) ⊥ (· qhat) ⊥) ⊥ ⊥ data)]
  [------------
  "11"
  (→ (· (par phat q)) data E
     (par (· phat) ⊥  q zero) ⊥ ⊥ data)]
  [------------
  "12"
  (→ (· (par p qhat)) data E
     (par p zero (· qhat) ⊥) ⊥ ⊥ data)]
  [------------
  "13"
  (→ (par pbar k qbar l) data E
     (par pbar qbar) ⊥ (meta-max k l) data)]

  [(→ pdot data E pdotdot e k data_*)
   ------------
  "14"
  (→ (par pdot ⊥ qdotdot m) data E
     (par pdotdot k qdotdot m) e ⊥ data_*)]

  [(→ qdot data E qdotdot e k data_*)
   ------------
  "15"
  (→ (par pdotdot m qdot ⊥) data E
     (par pdotdot m qdotdot k) e ⊥ data_*)]

  [------------
   "16"
   (→ (· (loop p)) data E
      (loop stop (· p)) ⊥ ⊥ data)]

  [------------
   "17"
   (→ (· (loop phat)) data E
      (loop go (· phat)) ⊥ ⊥ data)]

  [(→ pdot data E
      p e zero data_*)
   ------------
   "18"
   (→ (loop go pdot) data E
      (loop stop (· p)) e ⊥ data_*)]
  [(→ pdot data E
      pbar e k data_*)
   (side-condition ,(and (not (equal? `k `⊥))
                         (not (equal? `k `zero))))
   ------------
   "19"
   (→ (loop lstat pdot) data E
      (loop pbar) e k data_*)]

  ;; BLATANT TYPO data is missing? (page 103)
  [(→ pdot data E
      pdot_* e ⊥ data_*)
   ------------
   "20"
   (→ (loop lstat pdot) data E
      (loop lstat pdot_*) e ⊥ data_*)]

   [------------
   "21"
   (→ (· (trap T pbar)) data E
      (trap T (· pbar)) ⊥ ⊥ data)]
   [(→ pdot data E
       pdot_* e ⊥ data_*)
   ------------
   "22"
   (→  (trap T pdot) data E
       (trap T pdot_*) e ⊥ data_*)]

   ;; TODO pbar and p used in rule? does that mean remove any pauses?
   ;; (page 89)
   [(→ pdot data E
       pbar e two data_*)
   ------------
   "23"
   (→  (trap T pdot) data E
       (trap T (remove-selected pbar)) e zero data_*)]

   [(→ pdot data E
       p e zero data_*)
   ------------
   "24"
   (→  (trap T pdot) data E
       (trap T p) e zero data_*)]

   [(→ pdot data E
       phat e one data_*)
   ------------
   "25"
   (→  (trap T pdot) data E
       (trap T phat) e one data_*)]

   [(→ pdot data E
       pbar ⊥ k data)
    (where nat k)
    ;; k >= 3
    (side-condition (nat<= (Succ (Succ (Succ zero))) k))
   ------------
   "26"
   (→  (trap T pdot) data E
       (trap T pbar) ⊥ (↓ k) data)]

   [------------
   "27"
   (→ (· (exit T k)) data E
      (exit T k) ⊥ k data)]

   [------------
   "28"
   (→ (· (signal S pbar)) data E
      (signal S ⊥ (· pbar)) ⊥ ⊥ data)]

   [(→ pdot data (* E (S m))
            ;;TODO should this really be the same data?
       pdot_* S ⊥ data)
    (side-condition (∈ m (⊥ 1)))
    ------------
   "29"
   (→  (signal S m pdot) data E

       (signal S (Succ zero) pdot_*) ⊥ ⊥ data)]

   ;; TODO (page 105) confusing S should be decorated with 1, 0, or ⊥
   ;; assuming to mean (S 1) is not in Can_S?

   [(side-condition (∉ (S (Succ zero)) (Can_S pdot (* E (S ⊥)))))
    ------------
   "30"
   (→ (signal S ⊥ pdot) data E
      (signal S zero pdot) ⊥ ⊥ data)]

   [(→ pdot data (* E (S m))
       qdot e ⊥ data_*)
    (side-condition ,(not (equal? `e `S)))
    ;; added to avoid unneeded non-determinism
    (side-condition ,(or
                      (not (equal? `⊥ `m))
                      (not `(∉ (S one) (Can_S pdot (* E (S ⊥)))))))
    ------------
   "31"
   (→ (signal S m pdot) data E
      (signal S m qdot) e ⊥ data_*)]

   [(→ pdot data (* E (S m))
       qbar e k data_*)
    (side-condition ,(not (equal? `k `⊥)))
    (side-condition ,(not (equal? `e `S)))
    ;; added to avoid unneeded non-determinism
    (side-condition ,(or
                      (not (equal? `⊥ `m))
                      (not `(∉ (S one) (Can_S pdot (* E (S ⊥)))))))
    ------------
   "32"
   (→ (signal S m pdot) data E
      (signal S qbar) e k data_*)]


   [(→ pdot data (* E (S m))
       qbar S k data_*)
    (side-condition ,(not (equal? `k `⊥)))
    ;; added to avoid unneeded non-determinism
    (side-condition ,(or
                      (not (equal? `⊥ `m))
                      (not `(∉ (S one) (Can_S pdot (* E (S ⊥)))))))
    ------------
   "33"
   (→ (signal S m pdot) data E
      (signal S qbar) ⊥ k data_*)]

   [------------
   "34"
   (→ (· (emit S)) data E
      (emit S) S zero data)]
   )

(module+ test
  (default-language esterel-eval)
  (define (do t [E `()] [data `()])
    (judgment-holds (→ ,t ,E ,data pdotdot e k data_*)
                    (pdotdot e k data_*)))
  (test-case "1"
    (test-equal (do `(· nothing))
                `((nothing ⊥ zero ()))))
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
     (do `(· (trap t (par pause pause))))
     `(( (trap t (· (par pause pause))) ⊥ ⊥ ()))))
  (test-case  "22"
    (test-equal
     (do `(trap t (seq (· nothing) pause)))
     `(( (trap t (seq  nothing (· pause))) ⊥ ⊥ ()))))
  (test-case "23"
    (test-equal
     (do `(trap t (seq (· (exit t two)) pause)))
     `(( (trap t (seq (exit t two) pause)) ⊥ zero ()))))
  (test-case "24"
    (test-equal
     (do `(trap t (seq pause (· (hat pause)))))
     `(( (trap t (seq pause pause)) ⊥ zero ()))))
  (test-case "25"
    (test-equal
     (do `(trap t (seq pause (· pause))))
     `(( (trap t (seq pause (hat pause))) ⊥ one ()))))
  (test-case "26"
    (test-equal
     (do `(trap t2 (· (exit T three))))
     `(( (trap t2 (exit T three)) ⊥ (natnorm two) () ))))
  (test-case "27"
    (test-equal
     (do `(· (exit T three)))
     `(( (exit T three) ⊥ three ()))))
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




  (test-case "bugs"
    (test-equal
     (do `(trap q«749» (· (signal T (hat pause)))))
     `(( (trap q«749» (signal T ⊥ (· (hat pause))))
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
                `(( (par nothing nothing) ⊥ zero () )))))

(define-judgment-form esterel-eval
  #:mode     (→* I       I    I O       O       O O)
  #:contract (→* pdotdot data E pdotdot (S ...) k data)
  [(→ pdotdot data E
      pdotdot_* ⊥ k data)
   -----------
   (→* pdotdot data E
       pdotdot_* () k data)]

  [(→ pdotdot data E
      pdotdot_* S k data)
   -----------
   (→* pdotdot data E
       pdotdot_* (S) k data)]

  [(→ pdotdot data E
              pdotdot_* S ⊥ data_*)
   (→* pdotdot_* data_* E
       pdotdot_** (S_r ...) k data_**)
   -----------
   (→* pdotdot data E
       pdotdot_** (U (S) (S_r ...)) k data_**)]

  [(→ pdotdot data E
              pdotdot_* ⊥ ⊥ data_*)
   (→* pdotdot_* data_* E
       pdotdot_** (S ...) k data_**)
   -----------
   (→* pdotdot data E
       pdotdot_** (S ...) k data_**)])

(define-judgment-form esterel-eval
  ;; constructive ->>
  #:mode     (c->> I    O    O       O)
  #:contract (c->> pbar qbar (S ...) k)
  [(→* (· pbar) () () pbar_* (S ...) k data_*)
   (side-condition ,(not (equal? `k `⊥)))
   -------
   (c->> pbar pbar_* (S ...) k)])

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
  [(free-emitted-signals (present Spbar qbar))
   (U (free-emitted-signals pbar) (free-emitted-signals qbar))]
  [(free-emitted-signals (trap T pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (exit _ _)) ()]
  [(free-emitted-signals (emit S)) (S)]
  [(free-emitted-signals (var v pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (shared s pbar)) (free-emitted-signals pbar)]
  [(free-emitted-signals (signal S pbar)) (without_s (free-emitted-signals pbar) S)]
  [(free-emitted-signals (:= v call)) ()]
  [(free-emitted-signals (<= s call)) ()])

(module+ test
  (define-extended-language esterel-check esterel-eval
    (p-check
     nothing
     pause
     (seq p-check p-check)
     (par p-check p-check)
     ;(loop phat-check)
     (trap T p-check)
     (exit T nat)
     (signal S p-check)
     (emit S))

    (phat-check
     (hat pause)
     ;; loops only present here to force loops to be non-instantanious
     (loop phat-check)
     (seq phat-check p-check)
     (seq p-check phat-check)
     (par phat-check phat-check)
     (trap T phat-check)
     (signal S phat-check))
    (pbar-check p-check phat-check)

    (NL ()
        (nat NL)))

  (define-judgment-form esterel-eval
  ;; constructive ->>, with testing checks
  #:mode     (cc->> I    O    O       O)
  #:contract (cc->> pbar qbar (S ...) k)
  [(c->> pbar qbar (S ...) k)
   ;(side-condition ,(displayln `(free-signals pbar)))
   ;(side-condition ,(displayln `((∈ S (free-signals pbar)) ...)))
   (where (#t ...) ((∈ S (free-emitted-signals pbar)) ...))
   (where E (Can_S pbar ()))
   ;(side-condition ,(displayln `((∈ (S one) E) ...)))
   (where (#t ...) ((∈ (S (Succ zero)) E) ...))
   -------
   (cc->> pbar qbar (S ...) k)])

  #;
  (define-metafunction esterel-eval
    possibles : E -> (S ...)
    [])

  (define-metafunction esterel-eval
    eval : pbar -> (qbar (S ...) k)
    [(eval pbar)
     (qbar (S ...) k)
     (where (qbar (S ...) k)
            ,(judgment-holds (c->> (seq nothing (emit E)) any_1 any_2 any_3)
                             (any_1 any_2 any_3)))])


  (define-judgment-form esterel-check
    #:mode (traps-okay I I)
    #:contract (traps-okay pbar NL)

    [(traps-okay (exit T nat_h) NL)
     -----------
     (traps-okay (exit T nat_h) (nat_h NL))]

    [-----------
     (traps-okay (exit T nat_h) (nat_h NL))]

    [(traps-okay pbar ((Succ (Succ zero)) ()))
     ----------
     (traps-okay (trap T pbar) ())]

    [(traps-okay pbar ((Succ nat) (nat NL)))
     ----------
     (traps-okay (trap T pbar) (nat NL))]

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
     (traps-okay (par pbar_l pbar_r) NL)]

    [(traps-okay pbar NL)
     ---------
     (traps-okay (signal S pbar) NL)]
    )

  (test-case "eval bugs"
    (test-judgment-holds
     (c->>
      (seq (trap Q (hat pause)) (signal n (emit h)))
      (seq (trap T_Q pause) (signal S_n (emit S_h)))
      (S_h)
      zero))
    (test-judgment-holds
     (cc->>
      (seq (trap Q (hat pause)) (signal n (emit h)))
      (seq (trap T_Q pause) (signal S_n (emit S_h)))
      (S_h)
      zero))
    (test-judgment-holds
     (cc->>
      (seq (loop (hat pause)) (trap b nothing))
      (seq (loop (hat pause)) (trap T_b nothing))
      ()
      one))
    (test-judgment-holds
     (cc->>
      (signal A (signal Gz (emit H)))
      (signal S_A (signal S_Gz (emit S_H)))
      (S_H)
      zero))
    (test-judgment-holds
     (cc->>
      (trap x (trap OKG (exit P (Succ two))))
      (trap T_x (trap T_OKG (exit T_P (Succ two))))
      ()
      zero))

    (test-judgment-holds
     (cc->>
      (seq (trap x (trap OKG (exit P (Succ two)))) (signal A (signal Gz (emit H))))
      (seq (trap T_x (trap T_OKG (exit T_P (Succ two)))) (signal S_A (signal S_Gz (emit S_H))))
      (S_H)
      zero))

    (test-judgment-holds (cc->>
                          (loop (hat pause))
                          (loop (hat pause))
                          ()
                          one))
    (test-judgment-holds (cc->>
                          (seq (emit z) (loop pause))
                          (seq (emit S_z) (loop (hat pause)))
                          (z)
                          one))
    (test-judgment-holds (cc->>
                          (seq (emit z) (loop (hat pause)))
                          (seq (emit S_z) (loop (hat pause)))
                          ()
                          one))
    (test-judgment-holds (cc->>
                          (trap L (trap TGq (exit e (Succ two))))
                          any_1
                          any_2
                          any_3))
    (test-judgment-holds
     (cc->>
      (seq (trap L (trap TGq (exit e (Succ two)))) (signal IH nothing))
      (seq (trap T_L (trap T_TGq (exit T_e (Succ two)))) (signal S_IH nothing))
      ()
      zero))

    (test-judgment-holds
     (cc->>
      (par (seq (emit Q) (emit Q)) (signal S_v pause))
      (par (seq (emit S_Q) (emit S_Q)) (signal S_v (hat pause)))
      (Q)
      one)))

  (define-judgment-form esterel-check
    #:mode (okay I)
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
       (par (signal TY (signal a nothing))
            (signal S (par (par (emit R) pause)
                           pause)))
       (par (signal S_TY (signal S_a nothing))
            (signal S_S (par (par (emit S_R) (hat pause))
                             (hat pause))))
       (R)
       one)))
    (time ;; failing
     (test-judgment-holds
      (cc->>
       (par (signal K (signal Z (par nothing pause))) (signal R nothing))
       (par (signal S_K (signal S_Z (par nothing (hat pause)))) (signal S_R nothing))
       ()
       one)))))

(module+ random
  (require (submod ".." test))
  (test-case "random tests"
    ;(current-traced-metafunctions 'all)
    (redex-check
     esterel-check
     #:satisfying (okay p-check)
     (begin
       ;(displayln `p-check)
       (judgment-holds (cc->> p-check pbar (S ...) k)))
     #:attempts 333
     )
    (redex-check
     esterel-check
     #:satisfying (okay phat-check)
     (begin
       ;(displayln `phat-check)
       (judgment-holds (cc->> phat-check pbar (S ...) k)))
     #:attempts 333
     )
    (redex-check
     esterel-check
     #:satisfying (okay pbar-check)
     (begin
       ;(displayln `pbar-check)
       (judgment-holds (cc->> pbar-check pbar (S ...) k)))
     #:attempts 333
     )))

(module+ all (require (submod ".." test) (submod ".." slow) (submod ".." random)))

(define-metafunction esterel-eval
  remove-selected : pbar -> p
  [(remove-selected p) p]
  [(remove-selected (hat pause)) pause]
  [(remove-selected (present S pbar qbar))
   (present S (remove-selected pbar) (remove-selected qbar))]
  [(remove-selected (suspend S phat)) (suspend S (remove-selected phat))]
  [(remove-selected (seq pbar qbar))
   (seq (remove-selected pbar) (remove-selected qbar))]
  [(remove-selected (suspend phat S)) (suspend (remove-selected phat) S)]
  [(remove-selected (loop phat)) (loop (remove-selected phat))]
  [(remove-selected (par pbar qbar))
   (par (remove-selected pbar) (remove-selected qbar))]
  [(remove-selected (trap T phat)) (trap T (remove-selected phat))]
  [(remove-selected (var v phat))
   (var v (remove-selected phat))]
  [(remove-selected (shared s phat))
   (shared s (remove-selected phbar))]
  [(remove-selected (signal S phat))
   (signal S (remove-selected phat))])

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
  (test-case "Can"
    ;(current-traced-metafunctions '(Can Can_V))
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
    (U (without (Can_K pdot E) (0))
       (Can_K p E))
    (U (Can_V pdot E)
       (Can_V p E)))
   (where p (remove-selected pdot))
   (side-condition `(∈ zero (Can_K pdot E)))]

  [(Can (loop lstat pdot) E)
   (Can pdot E)]

  [(Can (signal S sstat pdot) E)
   (without (Can pdot (* E (S sstat))) S)]

  [(Can (trap t pdot) E)
   ((Can_S pdot E) (↓ (Can_K pdot E)) (Can_V pdot E))]

  [(Can (var v pdot) E)
   (Can pdot E)]

  [(Can (shared s pdot))
   (without_s (Can pdot E) s)]

  [(Can (:= v call) E)
   (() (zero) ())]

  [(Can (<= s call) E)
   (() (zero) (s))]

  [(Can (var v pbar) E) (Can pbar E)]

  [(Can (if v p q) E) (U (Can p E) (Can q E))]

  [(Can (if v phat q) E) (Can phat E)]

  [(Can (if v p qhat) E) (Can qhat E)]

  [(Can (shared s pbar) E) (without_s (Can pbar E) s)]

  ;; from ch 3 (starts at 77)
  [(Can nothing E) (() (zero) ())]

  [(Can pause E) (() (one) ())]

  [(Can (exit _ k) E) (() (k) ())]

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

  [(Can (suspend S p) E)
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

  [(Can (trap T p) E)
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

  [(Can (suspend S phat) E)
   ( () (one) () )
   (side-condition `(∈ (S one) E))]

  [(Can (suspend S phat) E)
   (Can phat E)
   (side-condition `(∈ (S zero) E))]

  [(Can (suspend S phat) E)
   ( (S_1 ...) (one k ...) (v ...) )
   (where ((S_1 ...) (k ...) (v ...)) E)
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

  [(Can (trap T phat) E)
   ( (Can_S phat E)
     (↓ (Can_K phat E))
     (Can_V phat E) )]

  [(Can (signal S phat) E)
   (without (Can phat (* E (S zero))) S)
   (side-condition `(∉ (S one) (Can_S phat (* E (S ⊥)))))]

  [(Can (signal S phat) E)
   (without (Can phat (* E (S ⊥))) S)])

(define-metafunction esterel-eval
  U  : (any ...) (any ...) -> (any ...)
  ;; I suspect this case is wrong...?
  [(U E_1 E_2)
   (U_E E_1 E_2)]
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
   (without_s (s_1 ...) s)]
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
  [(Can_V (trap T pbar) E)
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
