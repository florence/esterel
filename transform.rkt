#lang racket
(provide replace-I/O)
(require esterel/ast)
(define (replace-I/O prog ins outs)
  (define-values (new subbed-ins subbed-outs) (needed+sub prog ins outs))
  (define new/ins
    (for/fold ([p new]) ([(old new) (in-hash subbed-ins)])
      (make-signal new
              (make-par p
                   (make-loop (make-present old
                                  (make-seq (make-emit new) (make-pause))
                                  (make-pause)))))))
  (define new/outs
    (for/fold ([p new/ins]) ([(old new) (in-hash subbed-outs)])
      (make-signal new
                   (make-par p
                             (make-loop (make-present new
                                                      (make-seq (make-emit old) (make-pause))
                                                      (make-pause)))))))
  new/outs)
(define (needed+sub p ins outs [ins-hash (hash)] [outs-hash (hash)])
  (define (recur p #:ins [in* ins-hash] #:outs [out* outs-hash])
    (needed+sub p ins outs in* out*))
  (define (get S)
    (or (hash-ref outs-hash S #f)
        (hash-ref ins-hash S #f)
        S))
  (match p
    [(nothing _) (values p ins-hash outs-hash)]
    [(pause _) (values p ins-hash outs-hash)]
    [(seq _ left right)
     (define-values (l1 l2 l3) (recur left))
     (define-values (r1 r2 r3) (recur right #:ins l2 #:outs l3))
     (values (make-seq l1 r1) r2 r3)]
    [(par _ left right)
     (define-values (l1 l2 l3) (recur left))
     (define-values (r1 r2 r3) (recur right #:ins l2 #:outs l3))
     (values (make-par l1 r1) r2 r3)]
    [(loop _ p)
     (define-values (a b c) (recur p))
     (values (make-loop a) b c)]
    [(suspend _ S p)
     (cond [(hash-ref outs-hash S #f) =>
            (lambda (nS)
              (recur (make-suspend nS p)))]
           [(member S outs)
            (recur p #:outs (hash-set outs-hash S (gensym S)))]
           [else
            (define-values (l1 l2 l3) (recur p))
            (values (make-suspend S l1) l2 l3)])]
    [(signal _ S p)
     (define-values (a b c) (recur p))
     (values (make-signal S a) b c)]
    [(emit _ S)
     (cond [(hash-ref ins-hash S #f) =>
            (lambda (nS)
              (values (emit nS) ins-hash outs-hash))]
           [(member S ins)
            (recur p #:ins (hash-set ins-hash S (gensym S)))]
           [(hash-ref outs-hash S #f) =>
            (lambda (nS)
              (values (make-emit nS) ins-hash outs-hash))]
           [else (values p ins-hash outs-hash)])]
    [(present _ S then else)
     (cond [(hash-ref outs-hash S #f) =>
            (lambda (nS)
              (recur (make-present nS then else)))]
           [(member S outs)
            (recur p #:outs (hash-set outs-hash S (gensym S)))]
           [(hash-ref ins-hash S #f) =>
            (lambda (nS)
              (recur (make-present nS then else)))]
           [else
            (define-values (l1 l2 l3) (recur then))
            (define-values (r1 r2 r3) (recur else #:ins l2 #:outs l3))
            (values (make-present S l1 r1) r2 r3)])]
    [(trap _ T p)
     (define-values (a b c) (recur p))
     (values (make-trap T a) b c)]
    [(exit _ _ _) (values p ins-hash outs-hash)]
    ;; technically not needed
    [(sel _ p)
     (define-values (a b c) (recur p))
     (values (make-sel a) b c)]))
