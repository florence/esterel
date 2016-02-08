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
    [(nothing) #f]
    [(pause) #f]
    [(seq left right) (or (loop-safe/node left) (loop-safe/node right))]
    [(par left right) (or (loop-safe/node left) (loop-safe/node right))]
    [(loop p*)
     (define c (loop-safe/node p*))
     (if  (set-member? (Ks p*) 0)
          (cons p (if c c null))
          c)]
    [(signal S p) (loop-safe/node p)]
    [(emit S) #f]
    [(suspend S p) (loop-safe/node p)]
    [(present S then else) (or (loop-safe/node then) (loop-safe/node else))]
    [(trap T p) (loop-safe/node p)]
    [(exit _ _) #f]
    ;; technically not needed
    [(sel _) #f]))

(define/match (Ks p)
  [((nothing)) (set 0)]
  [((pause)) (set 1)]
  [((exit _ T)) (set T)]
  [((emit S)) (set 0)]
  [((present S t e)) (set-union (Ks t) (Ks e))]
  [((suspend S p)) (Ks p)]
  [((seq l r))
   (define k* (Ks l))
   (if (set-member? k* 0)
       (set-union (set-remove k* 0) (Ks r))
       k*)]
  [((loop p)) (set-remove (Ks p) 0)]
  [((par l r)) (set (apply max (set->list (set-union (Ks l) (Ks r)))))]
  [((trap T p)) (list->set (set-map (Ks p) harp))]
  [((signal S p)) (Ks p)])

(define/match (Kd p)
  [((nothing)) (set)]
  [((pause)) (set 0)]
  [((exit _ T)) (set)]
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
  [((trap T p)) (list->set (set-map harp (Kd p)))]
  [((signal S p)) (Kd p)])

(define (harp k)
  (cond [(= k 2) 0]
        [(> k 2) (sub1 k)]
        [else k]))
