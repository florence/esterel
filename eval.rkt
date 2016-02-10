#lang debug racket
(provide eval)
(require (submod esterel/ast))
(require (submod esterel/potentials))

;; ast E -> ast S k
(define/match (eval p E)
  [((nothing _) E) (values p null 0)]
  [((exit _ _ T) E) (values p null T)]
  [((emit _ S) E) (values p (list S) 0)]
  [((pause _) E) (values (make-sel p) null 1)]
  [((sel _ (pause _)) E) (values (make-pause) null 0)]
  [((present _ S then else) E)
   (define (t)
     (define-values (p* S* k) (eval then E))
     (values (make-present S p* else) S* k))
   (define (e)
     (define-values (p* S* k) (eval else E))
     (values (make-present S then p*) S* k))
   (cond [(has-selected? then) (t)]
         [(has-selected? else) (e)]
         [else
          (case (get S E)
            [(present) (t)]
            [(absent) (e)])])]
  [((suspend _ S p) E)
   (define (e)
     (define-values (p* S* k) (eval p E))
     (values (make-suspend S p*) S* k))
   (cond [(has-selected? p)
          (case (get S E)
            [(present) (values p null 1)]
            [(absent) (e)])]
         [else (e)])]
  [((seq _ left right) E)
   (cond [(has-selected? right)
          (define-values (p* S* k) (eval right E))
          (values (make-seq left p*) S* k)]
         [else
          (define-values (p* S* k) (eval left E))
          (cond [(not (= 0 k)) (values (make-seq p* right) S* k)]
                [else
                 (define-values (p** S** k*) (eval right E))
                 (values (make-seq p* p**) (append S* S**) k*)])])]
  [((loop _ p) E)
   (define-values (p* S* k) (eval p E))
   ;; assumes valid prog where loops cannot be instantanious
   (cond [(not (has-selected? p*))
          (define-values (p** S** k*) (eval p* E))
          (values (make-loop p**) (append S* S**) (max k k*))]
         [else (values (make-loop p*) S* k)])]
  [((par _ left right) E)
   (define (b)
     (define-values (l* Sl kl) (eval left E))
     (define-values (r* Sr kr) (eval right E))
     (values (make-par l* r*) (append Sl Sr) (max kl kr)))
   (match* ((has-selected? left) (has-selected? right))
     [(#t #t) (b)]
     [(#t #f)
      (define-values (p* S* k) (eval left E))
      (values (make-par p* right) S* k)]
     [(#f #t)
      (define-values (p* S* k) (eval right E))
      (values (make-par left p*) S* k)]
     [(#f #f) (b)])]
  [((trap _ T p) E)
   (define-values (p* S* k) (eval p E))
   (cond [(= k 1)
          (values (make-trap T p*) S* k)]
         [(or (= k 0) (= k 2))
          (values (make-trap T (clear-selected p*)) S* 0)]
         [else
          (values (make-trap T p*) S* (sub1 k))])]
  [((signal _ S p) E)
   (define-values (Sm Km) (must p (add (:unknown S) E)))
   (cond [(eq? 'present (get S Sm #f))
          (define-values (p* S* k) (eval p (add (:present S) E)))
          (values (make-signal S p*) (remove S S*) k)]
         ;; logically its actuall S not present in can*
         [else
          (define-values (p* S* k) (eval p (add (:absent S) E)))
          (values (make-signal S p*) (remove S S*) k)])])

(define (clear-selected p)
  (match p
    [(nothing _) p]
    [(pause _) p]
    [(seq _ left right) (make-seq (clear-selected left) (clear-selected right))]
    [(par _ left right) (make-par (clear-selected left) (clear-selected right))]
    [(loop _ p) (make-loop (clear-selected p))]
    [(suspend _ S p) (make-suspend S (clear-selected p))]
    [(signal _ S p) (make-signal S (clear-selected p))]
    [(emit _ S) p]
    [(present _ S then else) (make-present S (clear-selected then) (clear-selected else))]
    [(trap _ T p) (make-trap T (clear-selected p))]
    [(exit _ _ _) p]
    [(sel _ p) (clear-selected p)]))
