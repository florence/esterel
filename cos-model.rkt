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
   (exit k)
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
  ((l k m) natural)
  (sstat ⊥ 1 0))

(define-extended-language esterel-eval esterel
  ;(m P E Ss k data)
  (E ((S sstat) ...))
  (e ⊥ S)
  ((k l m) .... ⊥)
  (data (data-elem ...))
  (data-elem (v datum)
             (v datum shared-stat))
  (shared-stat ready old new))

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
   (side-condition ,(not (equal? `k 0)))
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
   (→ (loop p) E data
      (loop stop (· p)) ⊥ ⊥ data)]
  [------------
   "17"
   (→ (loop phat) E data
      (loop go (· phat)) ⊥ ⊥ data)]
  [(→ pdot E data
      p e 0 data_*)
   ------------
   "18"
   (→ (loop go pdot) E data
      (loop stop (· p)) e ⊥ data_*)]
  [(→ pdot E data
      pbar e k data_*)
   (side-condition ,(and (not (equal? `k `⊥))
                         (not (equal? `k `0))))
   ------------
   "19"
   (→ (loop lstat pdot) E data
      (loop pbar) e k data_*)]
  ;; BLATANT TYPO data is missing? (page 103)
  [(→ pdot E data
      pdot_* e ⊥ data_*)
   ------------
   "20"
   (→ (loop lstat pdot) E data
      (loop lstat pdot_*) e ⊥ data_*)]
   [------------
   "21"
   (→ (· (trap T pbar)) E data
      (trap T (· pbar)) ⊥ ⊥ data)]
   [(→ pdot E data
       pdot_* e ⊥ data_*)
   ------------
   "22"
   (→  (trap T pdot) E data
       (trap T pdot_*) e ⊥ data_*)]

   ;; TODO pbar and p used in rule? does that mean remove any pauses?
   ;; (page 89)
   [(→ pdot E data
       pbar e 2 data_*)
   ------------
   "23"
   (→  (trap T pdot) E data
       (trap T (remove-selected pbar)) e 0 data_*)]

   [(→ pdot E data
       p e 0 data_*)
   ------------
   "24"
   (→  (trap T pdot) E data
       (trap T p) e 0 data_*)]

   [(→ pdot E data
       phat e 1 data_*)
   ------------
   "25"
   (→  (trap T pdot) E data
       (trap T phat) e 1 data_*)]

   [(→ pdot E data
       phat ⊥ k data)
    (side-condition
     ,(and (number? k) (>= k 3)))
   ------------
   "26"
   (→  (trap T pdot) E data
       (trap T phat) ⊥ (↓ k) data)]

   [------------
   "27"
   (→ (· (exit k)) E data
      (exit k) ⊥ k data)]
   )

(module+ test
  (define (do t [E `()] [data `()])
    (judgment-holds (→ ,t ,E ,data pdotdot e k data_*)
                    (pdotdot e k data_*)))
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
     `(( (par pause (hat pause)) ⊥ 1 ()))))
  (test-case "14"
    (test-equal
     (do `(par (· (seq pause pause)) ⊥ pause 0))
     `(( (par (seq (· pause) pause) ⊥ pause 0) ⊥ ⊥ ()))))
  (test-case "15"
    (test-equal
     (do `(par pause 0 (· (seq pause pause)) ⊥))
     `(( (par pause 0 (seq (· pause) pause) ⊥) ⊥ ⊥ ()))))
  (test-case "14/15"
    (test-equal
     (do `(par (· (seq pause pause)) ⊥ (· (seq pause pause)) ⊥))
     `(( (par (seq (· pause) pause) ⊥ (· (seq pause pause)) ⊥) ⊥ ⊥ ())
       ( (par (· (seq pause pause)) ⊥ (seq (· pause) pause) ⊥) ⊥ ⊥ ()))))
  (test-case "16"
    (test-equal
     (do `(loop (seq pause nothing)))
     `(( (loop stop (· (seq pause nothing))) ⊥ ⊥ ()))))
  (test-case "17"
    (test-equal
     (do `(loop (seq (hat pause) nothing)))
     `(( (loop go (· (seq (hat pause) nothing))) ⊥ ⊥ ()))))
  (test-case "18"
    (test-equal
     (do `(loop go (seq pause (· nothing))))
     `(( (loop stop (· (seq pause nothing))) ⊥ ⊥ ()))))
  (test-case "19"
    (test-equal
     (do `(loop go (seq (· pause) nothing)))
     `(( (loop (seq (hat pause) nothing)) ⊥ 1 ())))
    (test-equal
     (do `(loop stop (seq (· pause) nothing)))
     `(( (loop (seq (hat pause) nothing)) ⊥ 1 ()))))
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
     (do `(trap t (seq (· (exit 2)) pause)))
     `(( (trap t (seq (exit 2) pause)) ⊥ 0 ()))))
  (test-case "24"
    (test-equal
     (do `(trap t (seq pause (· (hat pause)))))
     `(( (trap t (seq pause pause)) ⊥ 0 ()))))
  (test-case "25"
    (test-equal
     (do `(trap t (seq pause (· pause))))
     `(( (trap t (seq pause (hat pause))) ⊥ 1 ()))))
  (test-case "26"
    (do `(trap t2 (· (exit 3))))
    `(( `(trap t2 (exit 3)) ⊥ 2 ())))
  (test-case "27"
    (do `(· (exit 3)))
    `(( (exit 3) ⊥ 3 ()))))

(define-judgment-form esterel-eval
  #:mode     (→* I       I    I O       O O O)
  #:contract (→* pdotdot data E pdotdot e k data)
  [(→ pdotdot data E
      pdotdot_* e k data)
   -----------
   (→* pdotdot data E
       pdotdot_* e k data)]
  [(→ pdotdot data E
              pdotdot_* _ ⊥ data_*)
   (→* pdotdot_* data_* E
       pdotdot_** e k data_**)
   -----------
   (→* pdotdot data E
       pdotdot_** e k data_**)])

(define-judgment-form esterel-eval
  ;; constructive ->>
  #:mode (c->> I O O)
  #:contract (c->> pbar qbar k)
  [(→* (· pbar) () () pbar_* e k data_*)
   (side-condition ,(not (equal? `k `⊥)))
   -------
   (c->> pbar pbar_* k)])

(define-extended-language check-par esterel-eval
  (p-check
   nothing
   pause
   (seq p-check p-check)
   (par  p-check p-check))
  (phat-check
   (hat pause)
   (seq phat-check p-check)
   (par phat-check phat-check)))

(module+ test
  ;(current-traced-metafunctions 'all)
  (redex-check
   check-par p-check
   (judgment-holds (c->> p-check pbar k))
   #:attempts 50))

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
  ↓ : k or (k ...) -> k or (k ...)
 [(↓ 0) 0]
 [(↓ 2) 0]
 [(↓ 1) 1]
 [(↓ natural) ,(- k 1)]
 [(↓ (k ...)) ((↓ k) ...)])

(define-metafunction esterel-eval
  Can : pdotdot E -> ((S ...) (k ...) (v ...))
  [(Can (· pbar) E) (can pbar E)]
  [(Can (present S pdot q) E) (can pdot E)]
  [(Can (present S p qdot) E) (can qdot E)]
  [(Can (suspend pdot S) E) (can pdot E)]
  [(Can (if v pdot q) E) (can pdot E)]
  [(Can (if v p qdot) E) (can qdot E)]
  [(Can (seq pdot q) E)
   (Can pdot E)
   (where (∉ 0 (Can_K pdot)))]
  [(Can (seq pdot q) E)
   ((Can_S pdot E)
    (U (without (Can_K pdot E) (0))
       (Can_K q E))
    (U (Can_V pdot E)
       (Can_V q E)))
   (where (∈ 0 (Can_K pdot)))]
  [(Can (seq p qdot) E)
   (Can qdot E)]
  [(Can (par pdot ⊥ qdot ⊥) E)
   ((U (Can_S pdot E)
       (Can_S qdot E))
    (max (Can_K pdot E)
         (Can_K qdot E))
    (U (Can_V pdot E)
       (Can_V qdot E)))]
  ;; TODO should this be qbar? (page 112)
  [(Can (par pdot ⊥ q k) E)
   ((Can_S pdot E)
    (max (Can_K pdot E) (k))
    (Can_V pdot E))]
  [(Can (par p k qdot ⊥) E)
   ((Can_S qdot E)
    (max (Can_K qdot E) (k))
    (Can_V qdot E))]
  [(Can (par p k q l) E)
   (() ((max k l)) ())]
  [(Can (loop go pdot) E)
   ((U (Can_S pdot E) (Can_S p E))
    (U (without (Can_K pdot E) (0))
       (Can_K p E))
    (U (Can_V pdot E)
       (Can_V p E)))
   (where p (remove-selected pdot))
   (side-condition (∈ 0 (Can_K pdot E)))]
  [(Can (loop lstat pdot) E)
   (Can pdot E)]
  [(Can (signal sstat S pdot) E)
   (without (Can pdot (* E (S sstat))) S)]
  [(Can (trap t pdot) E)
   ((Can_S pdot E) (↓ (Can_K pdot E)) (Can_V pdot E))]
  [(Can (var v pdot) E)
   (Can pdot E)]
  [(Can (shared s pdot))
   (without_s (Can pdot E) s)]
  [(Can (:= v call) E)
   (() (0) ())]
  [(Can (<= s call) E)
   (() (0) (s))]
  [(Can (var v pbar) E) (Can pbar E)]
  [(Can (if v p q) E) (U (Can p E) (Can q E))]
  [(Can (if v phat q) E) (Can phat E)]
  [(Can (if v p qhat) E) (Can qhat E)]
  [(Can (shared s pbar) E) (without_s (Can pbar E) s)]

  ;; from ch 3 (starts at 77
  [(Can nothing E) (() (0) ())]
  [(Can pause E) (() (1) ())]
  [(Can (exit k) E) (() (k) ())]
  [(Can (emit S) E) (((S 1)) (0) ())]
  [(Can (present S p q) E)
   (Can p E)
   (side-condition (∈ (S 1) E))]
  [(Can (present S p q) E)
   (Can q E)
   (side-condition (∈ (S 0) E))]
  [(Can (present S p q) E)
   (U (Can p E) (Can q E))
   (side-condition (∈ (S ⊥) E))])

(define-metafunction esterel-eval
  U  : (any ...) (any ...) -> (any ...)
  [(U (any_1 ...) (any_2 ...))
   (any_1 ... any_2 ...)])
(define-metafunction esterel-eval
  without : (k ...) or (S ...) or (s ...) or ((S ...) (k ...) (s ...))
  ->
  (k ...) or (S ...) or (s ...) or ((S ...) (k ...) (s ...)))
(define-metafunction esterel-eval
  ∉ : any (any ...) -> boolean
  [(∉ any_1 (any_2 ...))
   ,(not `(∈ any_1 (any_2 ...)))])
(define-metafunction esterel-eval
  ∈ : any (any ...) -> boolean
  [(∈ any_1 (any_2 ... any_1 any_3 ...))
   ,#t]
  [(∈ any_1 (any_2 ...))
   ,#f])
(define-metafunction esterel-eval
  max : (k ...) or k (k ...) or k -> (k) or k
  [(max (k_1 ...) (k_2 ...))
   ,(apply max (append `(k_1 ...) `(k_2 ...)))]
  [(max k_1 k_2)
   ,(max `k_1 `k_2)])
(define-metafunction esterel-eval
  * : E (S sstat) -> E
  )

(define-metafunction esterel-eval
  Can_S pdotdot E -> (S ...))
(define-metafunction esterel-eval
  Can_K pdotdot E ->  (k ...))

(define-metafunction esterel-eval
  Can_V pbar E -> (s ...)
  [(Can_V pause) ()]
  [(Can_V (hat pause)) ()]
  [(Can_V (emit S)) ()]
  [(Can_V (exit k)) ()]
  [(Can_V (signal S pbar) E)
   (Can_V pbar  (* E (S ⊥)))
   (where (∈ (S 1) (Can_S pbar (* E (S ⊥)))))]
  [(Can_V (signal S pbar) E)
   (Can_V pbar (* E (S 0)))]
  [(Can_V (present S p q))
   (Can_V p E)
   (side-condition (∈ (S 1) E))]
  [(Can_V (present S p q))
   (Can_V q E)
   (side-condition (∈ (S 0) E))]
  [(Can_V (present S p q))
   (U (Can_V p E) (Can_V q E))
   (side-condition (∈ (S ⊥) E))]
  [(Can_V (present S phat q) E)
   (Can_V phat E)]
  [(Can_V (present S p qhat) E)
   (Can_V qhat E)]
  [(Can_V (suspend S p) E)
   (Can_V p E)]
  [(Can_V (suspend S phat) E)
   ()
   (side-condition (∈ (S 1) E))]
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
   (Can_V pbar E)
   (U (Can_V pbar E) (Can_V q E))
   (side-condition (∈ 0 (Can_K pbar E)))]
  [(Can_V (seq pbar q) E)
   (Can_V pbar E)]
  [(Can_V (seq p qhat) E)
   (Can_V qhat E)]
  [(Can_V (loop p) E)
   (Can_V p E)]
  [(Can_V (loop phat) E)
   (U (Can_V phat E) (Can_V (remove-selected phat) E))
   (side-condition (∈ 0 (Can_K phat E)))])
