#lang racket
(require esterel/ast esterel/potentials)
(define (loop-safe?)
  (match p
    [(nothing) #t]
    [(pause) #t]
    [(seq left right) (and (loop-safe? left) (loop-safe? right))]
    [(par left right) (and (loop-safe? left) (loop-safe? right))]
    [(loop p) (and (not (set-member? (Ks p) 0))
                   (loop-safe? p))]
    [(signal S p) (loop-safe? p)]
    [(emit S) #t]
    [(present S then else) (and (loop-safe? then) (loop-safe? else))]
    [(trap T p) (loop-safe? p)]
    [(exit _) #t]
    ;; technically not needed
    [(sel _) #t]))
(define/match (Ks p)
  [((nothing)) (set 0)]
  [((pause)) (set 1)]
  [((exit T)) (set T)]
  [((emit S)) (set 0)]
  [((present S t e)) (set-union (Ks t) (Ks e))]
  [((suspend S p)) (Ks p)]
  [((seq l r))
   (define k* (Ks l))
   (if (set-member? 0 l)
       (set-union (set-remove k* 0) (Ks r))
       k*)]
  [((loop p)) (set-remove (Ks p) 0)]
  [((par l r)) (list->set (apply max (set->list (set-union (Ks l) (Ks r)))))]
  [((trap T p)) (set-map harp (Ks p))]
  [((signal S p)) (Ks p)])
(define/match (Kd p)
  [((nothing)) (set)]
  [((pause)) (set 0)]
  [((exit T)) (set)]
  [((emit S)) (set)]
  [((present S t e)) (set-union (Ks t) (Ks e))]
  [((suspend S p)) (set-union 1 (Ks p))]
  [((seq l r))
   (define Ks* (Ks l))
   (define Kd* (Kd l))
   (cond [(not (set-member? (set-union Ks* Kd*) 0))
          Kd*]
         [(set-member? (set-subtract Ks Kd) 0)
          (set-union Kd* (Kd r))]
         [else
          (set-union (set-remove Kd* 0) (Kd r))])]
  [((loop p)) (Kd (seq p p))]
  [((par l r)) (list->set (apply max (set->list (set-union (Kd l) (Kd r)))))]
  [((trap T p)) (set-map harp (Kd p))]
  [((signal S p)) (Kd p)])

(define (harp k)
  (cond [(= k 2) 0]
        [(> k 2) (sub1 k)]
        [else k]))
