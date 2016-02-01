#lang debug racket
(provide eval)
(require (submod esterel/ast))
(require (submod esterel/potentials))

;; ast E -> ast S k
(define/match (eval p E)
  [((nothing) E) (values p null 0)]
  [((exit T) E) (values p null T)]
  [((emit S) E) (values p (list S) 0)]
  [((pause) E) (values (sel p) null 1)]
  [((sel (pause)) E) (values (pause) null 0)]
  [((present S then else) E)
   (define (t)
     (define-values (p* S* k) (eval then E))
     (values (present S p* else) S* k))
   (define (e)
     (define-values (p* S* k) (eval else E))
     (values (present S then p*) S* k))
   (cond [(has-selected? then) (t)]
         [(has-selected? else) (e)]
         [else
          (case (get S E)
            [(present) (t)]
            [(absent) (e)])])]
  [((suspend S p) E)
   (define (e)
     (define-values (p* S* k) (eval p E))
     (values (suspend S p*) S* k))
   (cond [(has-selected? p)
          (case (get S E)
            [(present) (values p null 1)]
            [(absent) (e)])]
         [else (e)])]
  [((seq left right) E)
   (cond [(has-selected? right)
          (define-values (p* S* k) (eval right E))
          (values (seq left p*) S* k)]
         [else
          (define-values (p* S* k) (eval left E))
          (cond [(not (= 0 k)) (values (seq p* right) S* k)]
                [else
                 (define-values (p** S** k*) (eval right E))
                 (values (seq p* p**) (append S* S**) k*)])])]
  [((loop p) E)
   (define-values (p* S* k) (eval p E))
   ;; assumes valid prog where loops cannot be instantanious
   (cond [(not (has-selected? p*))
          (define-values (p** S** k*) (eval p* E))
          (values (loop p**) (append S* S**) (max k k*))]
         [else (values (loop p*) S* k)])]
  [((par left right) E)
   (define (b)
     (define-values (l* Sl kl) (eval left E))
     (define-values (r* Sr kr) (eval right E))
     (values (par l* r*) (append Sl Sr) (max kl kr)))
   (match* ((has-selected? left) (has-selected? right))
     [(#t #t) (b)]
     [(#t #f)
      (define-values (p* S* k) (eval left E))
      (values (par p* right) S* k)]
     [(#f #t)
      (define-values (p* S* k) (eval right E))
      (values (par left p*) S* k)]
     [(#f #f) (b)])]
  [((trap T p) E)
   (define-values (p* S* k) (eval p E))
   (cond [(= k 1)
          (values (trap T p*) S* k)]
         [(or (= k 0) (= k 2))
          (values (trap T (clear-selected p*)) S* 0)]
         [else
          (values (trap T p*) S* (sub1 k))])]
  [((signal S p) E)
   (define-values (Sm Km) (must p (add (:unknown S) E)))
   (cond [(eq? 'present (get S Sm #f))
          (define-values (p* S* k) (eval p (add (:present S) E)))
          (values (signal S p*) (remove S S*) k)]
         ;; logically its actuall S not present in can*
         [else
          (define-values (p* S* k) (eval p (add (:absent S) E)))
          (values (signal S p*) (remove S S*) k)])])

(define (clear-selected p)
  (match p
    [(nothing) p]
    [(pause) p]
    [(seq left right) (seq (clear-selected left) (clear-selected right))]
    [(par left right) (par (clear-selected left) (clear-selected right))]
    [(loop p) (loop (clear-selected p))]
    [(suspend S p) (suspend S (clear-selected p))]
    [(signal S p) (signal S (clear-selected p))]
    [(emit S) p]
    [(present S then else) (present S (clear-selected then) (clear-selected else))]
    [(trap T p) (trap T (clear-selected p))]
    [(exit _) p]
    [(sel p) (clear-selected p)]))
