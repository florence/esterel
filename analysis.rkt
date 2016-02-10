#lang racket
(provide loop-safe? loop-safe!)
(require esterel/ast esterel/potentials)
(define (signals-closed?) ;;TODO
  (void))
(define (loop-safe! p)
  (define c (loop-safe/node p))
  (when c
    (error 'loop-safety
           "The following loop(s) could not be proven to be non instantaneous: ~a"
           (apply ~v #:separator "\n" c))))
(define (loop-safe? p)
  (not (loop-safe/node p)))
(define (loop-safe/node p)
  (match p
    [(nothing _) #f]
    [(pause _) #f]
    [(seq _ left right) (or (loop-safe/node left) (loop-safe/node right))]
    [(par _ left right) (or (loop-safe/node left) (loop-safe/node right))]
    [(loop _ p*)
     (define c (loop-safe/node p*))
     (if  (set-member? (Ks p*) 0)
          (cons p (if c c null))
          c)]
    [(signal _ S p) (loop-safe/node p)]
    [(emit _ S) #f]
    [(suspend _ S p) (loop-safe/node p)]
    [(present _ S then else) (or (loop-safe/node then) (loop-safe/node else))]
    [(trap _ T p) (loop-safe/node p)]
    [(exit _ _ _) #f]
    ;; technically not needed
    [(sel _ _) #f]))

(define/match (Ks p)
  [((nothing _)) (set 0)]
  [((pause _)) (set 1)]
  [((exit _ _ T)) (set T)]
  [((emit _ S)) (set 0)]
  [((present _ S t e)) (set-union (Ks t) (Ks e))]
  [((suspend _ S p)) (Ks p)]
  [((seq _ l r))
   (define k* (Ks l))
   (if (set-member? k* 0)
       (set-union (set-remove k* 0) (Ks r))
       k*)]
  [((loop _ p)) (set-remove (Ks p) 0)]
  [((par _ l r)) (set (apply max (set->list (set-union (Ks l) (Ks r)))))]
  [((trap _ T p)) (list->set (set-map (Ks p) harp))]
  [((signal _ S p)) (Ks p)])

(define/match (Kd p)
  [((nothing _)) (set)]
  [((pause _)) (set 0)]
  [((exit _ _ T)) (set)]
  [((emit _ S)) (set)]
  [((present _ S t e)) (set-union (Ks t) (Ks e))]
  [((suspend _ S p)) (set-union 1 (Ks p))]
  [((seq _ l r))
   (define Ks* (Ks l))
   (define Kd* (Kd l))
   (cond [(not (set-member? (set-union Ks* Kd*) 0))
          Kd*]
         [(set-member? (set-subtract Ks Kd) 0)
          (set-union Kd* (Kd r))]
         [else
          (set-union (set-remove Kd* 0) (Kd r))])]
  [((loop _ p)) (Kd (seq p p))]
  [((par _ l r)) (list->set (apply max (set->list (set-union (Kd l) (Kd r)))))]
  [((trap _ T p)) (list->set (set-map harp (Kd p)))]
  [((signal _ S p)) (Kd p)])

(define (harp k)
  (cond [(= k 2) 0]
        [(> k 2) (sub1 k)]
        [else k]))
