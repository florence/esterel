#lang racket
(provide replace-I/O)
(require esterel/ast)
(define (replace-I/O prog ins outs)
  (define-values (new subbed-ins subbed-outs) (needed+sub prog ins outs))
  (define new/ins
    (for/fold ([p new]) ([(old new) (in-hash subbed-ins)])
      (signal new
              (par p
                   (loop (present old
                                  (seq (emit new) (pause))
                                  (pause)))))))
  (define new/outs
    (for/fold ([p new/ins]) ([(old new) (in-hash subbed-outs)])
      (signal new
              (par p
                   (loop (present new (seq (emit old) (pause)) (pause)))))))
  new/outs)
(define (needed+sub p ins outs [ins-hash (hash)] [outs-hash (hash)])
  (define (recur p #:ins [in* ins-hash] #:outs [out* outs-hash])
    (needed+sub p ins outs in* out*))
  (define (get S)
    (or (hash-ref outs-hash S #f)
        (hash-ref ins-hash S #f)
        S))
  (match p
    [(nothing) (values p ins-hash outs-hash)]
    [(pause) (values p ins-hash outs-hash)]
    [(seq left right)
     (define-values (l1 l2 l3) (recur left))
     (define-values (r1 r2 r3) (recur right #:ins l2 #:outs l3))
     (values (seq l1 r1) r2 r3)]
    [(par left right)
     (define-values (l1 l2 l3) (recur left))
     (define-values (r1 r2 r3) (recur right #:ins l2 #:outs l3))
     (values (par l1 r1) r2 r3)]
    [(loop p)
     (define-values (a b c) (recur p))
     (values (loop a) b c)]
    [(suspend S p)
     (cond [(hash-ref outs-hash S #f) =>
            (lambda (nS)
              (recur (suspend nS p)))]
           [(member S outs)
            (recur p #:outs (hash-set outs-hash S (gensym S)))]
           [else
            (define-values (l1 l2 l3) (recur p))
            (values (suspend S l1) l2 l3)])]
    [(signal S p)
     (define-values (a b c) (recur p))
     (values (signal S a) b c)]
    [(emit S)
     (cond [(hash-ref ins-hash S #f) =>
            (lambda (nS)
              (values (emit nS) ins-hash outs-hash))]
           [(member S ins)
            (recur p #:ins (hash-set ins-hash S (gensym S)))]
           [(hash-ref outs-hash S #f) =>
            (lambda (nS)
              (values (emit nS) ins-hash outs-hash))]
           [else (values p ins-hash outs-hash)])]
    [(present S then else)
     (cond [(hash-ref outs-hash S #f) =>
            (lambda (nS)
              (recur (present nS then else)))]
           [(member S outs)
            (recur p #:outs (hash-set outs-hash S (gensym S)))]
           [(hash-ref ins-hash S #f) =>
            (lambda (nS)
              (recur (present nS then else)))]
           [else
            (define-values (l1 l2 l3) (recur then))
            (define-values (r1 r2 r3) (recur else #:ins l2 #:outs l3))
            (values (present S l1 r1) r2 r3)])]
    [(trap T p)
     (define-values (a b c) (recur p))
     (values (trap T a) b c)]
    [(exit _ _) (values p ins-hash outs-hash)]
    ;; technically not needed
    [(sel p)
     (define-values (a b c) (recur p))
     (values (sel a) b c)]))
