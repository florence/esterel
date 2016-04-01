#lang racket
(require redex)
(module+ test (require rackunit))

(define-syntax quasiquote (make-rename-transformer #'term))
(define-language esterel
  ((p q)
   nothing
   pause
   (seq p q)
   (par p q)
   (loop p)
   (suspend p S)
   (present S p q)
   (trap T p)
   (var v p)
   (shared s p)
   (signal S p))

  ((phat qhat)
   (hat pause)
   (present S phat q)
   (present S p qhat)
   (suspend S phat)
   (seq phat q)
   (seq p qhat)
   (suspend p qhat)
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
   (trap T in pdot)
   (var v pdot)
   (shared s pdot)
   (signal S sstat pdot))

  ((pdotdot qdotdot) pdot pbar)

  ((S T v s) variable-not-otherwise-mentioned)

  (lstat none stop go)
  (pstat ⊥ l k)
  ((l k) natural)
  (sstat ⊥ present absent))

(define-extended-language esterel-eval esterel
  ;(m P E Ss k data)
  (E ((S sstat) ...))
  (e ⊥ S)
  ((k l) .... ⊥)
  (m k)
  (data (data-elem ...))
  (data-elem (v datum)
             (v datum shared-stat))
  (shared-stat ready old new))

(define-judgment-form esterel-eval
  #:mode     (→ I       I    I O       O O O)
  #:contract (→ pdotdot data E pdotdot e m data)
  #|
  [------------
  ""
  (→ )]
  |#
  [------------
   "1"
   (→ (· nothing) data E
      nothing ⊥ 0 data)]
  [------------
   "2"
   (→ (· pause) data E
      (hat pause) ⊥ 1 data)]
  [------------
   "3"
   (→ (· (hat pause)) data E
      pause ⊥ 0 data)]
  [------------
   "4"
   (→ (· (seq pbar q)) data E
      (seq (· pbar) q) ⊥ ⊥ data)]
  [(→ pdot data E pdotdot e k data_*)
   (side-condition ,(not (= `k 0)))
   ------------
   "5"
   (→ (seq pdot q) data E
      (seq pdotdot q) e k data_*)]
  [(→ pdot data E p e 0 data_*)
   ------------
   "6"
   (→ (seq pdot q) data E
      (seq p (· q)) e ⊥ data_*)]
  [------------
   "7"
   (→ (· (seq p qhat)) data E
      (seq p (· qhat)) ⊥ ⊥ data)]
  ;; NOTE: book says `k`, but that fails some tests that i think should pass
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
     (par (· phat) ⊥  q 0) ⊥ ⊥ data)]
  [------------
  "12"
  (→ (· (par p qhat)) data E
     (par p 0  (· qhat) ⊥) ⊥ ⊥ data)]
  [------------
  "13"
  (→ (par pbar k qbar l) data E
     (par pbar qbar) ⊥ ,(max `k `l) data)]
  ;; (for 14 and 15) Again, the prose says k, but maybe its an m?
  ;; Forcing completion doesnt make sense here (its a microstep)
  [(→ pdot data E pdotdot e k data_*)
   ------------
  "14"
  (→ (par pdot ⊥ qdotdot m) data E
     (par pdotdot k qdotdot m) e ⊥ data_*)]
  [(→ qdot data E pdotdot e k data_*)
   ------------
  "15"
  (→ (par pdotdot m qdot ⊥) data E
     (par pdotdot m qdotdot k) e ⊥ data_*)])

(module+ test
  (define (do t [E `()] [data `()])
    (judgment-holds (→ ,t ,E ,data pdotdot e K data_*)
                    (pdotdot e K data_*)))
  (test-case "1"
    (test-equal (do `(· nothing))
                `((nothing ⊥ 0 ()))))
  (test-case "2"
    (test-equal (do `(· pause))
                `(((hat pause) ⊥ 1 ()))))
  (test-case "3"
    (test-equal (do `(· (hat pause)))
                `((pause ⊥ 0 ()))))
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
     `(( (seq (hat pause) pause) ⊥ 1 ()))))
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
     `(( (seq pause pause) ⊥ 0 ())))
    (test-equal
     (do `(seq pause (seq pause (· (hat pause)))))
     `(( (seq pause  (seq pause pause)) ⊥ 0 () )))
    (test-equal
     (do `(seq pause (seq pause (· pause))) )
     `(( (seq pause (seq pause (hat pause))) ⊥ 1 () )))
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
     `(( (par (· (hat pause)) ⊥ pause 0) ⊥ ⊥ ()))))

  (test-case "12"
    (test-equal
     (do `(· (par  pause (hat pause))))
     `(( (par pause 0 (· (hat pause)) ⊥) ⊥ ⊥ ()))))

  (test-case "13"
    (test-equal
     (do `(par pause 0 (hat pause) 1))
     `(( (par pause (hat pause)) ⊥ 1 ())))))


#|
(define-metafunction esterel-eval
  can : pdot E -> (? ? ?)
  [(can pdot E) ((can_s pdot E) (can_k pdot E) (can_v pdot E))])

(define-metafunction esterel-eval
  can_s pdot E -> ?)
(define-metafunction esterel-eval
  can_k pdot E -> ?)
(define-metafunction esterel-eval
  can_v pdot E -> ?)
|#
