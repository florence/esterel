#lang racket
(provide must can can* rem get add has-selected?)
(require esterel/ast)
(module+ test (require rackunit))

;; Must
(define/match (must ast E)
  [((nothing _) _) (values null (list 0))]
  [((pause _) _) (values null (list 1))]
  [((exit _ _ T) _) (values null (list T))]
  [((emit _ S) E) (values (list (:present S)) (list 0))]
  [((present _ S then else) _)
   (cond [(has-selected? then) (must then E)]
         [(has-selected? else) (must else E)]
         [else
          (case (get S E)
            [(present) (must then E)]
            [(absent) (must else E)]
            [(unknown) (values null null)])])]
  [((suspend _ S p) E)
   (cond [(has-selected? p)
          (case (get S E)
            [(present) (values null (list 1))]
            [(absent) (must p E)]
            [(unknown) (values null null)])]
         [else (must p E)])]
  [((seq _ left right) E)
   (define-values (S K) (must left E))
   (cond [(has-selected? right) (must right E)]
         [(not (member 0 K)) (values S K)]
         [else
          (let-values ([(Sr Kr) (must right E)])
            (values (append S Sr) Kr))])]
  [((loop _ p) E)
   (define-values (S K) (must p E))
   (cond [(has-selected? p)
          (if (not (member 0 K))
              (values S K)
              (let-values ([(S* K^) (without-selected (must p E))])
                (values (append S* S) K^)))]
         [else (values S K)])]
  [((par _ l r) E)
   (match* ((has-selected? l) (has-selected? r))
     [(#t #t) (U/max (must l E) (must r E))]
     [(#t #f) (must l E)]
     [(#f #t) (must r E)]
     [(#f #f) (U/max (must l E) (must r E))])]
  [((trap _ T p) E)
   (harp (must p E))]
  [((signal _ S p) E)
   (define-values (S^ K) (must p (add (:unknown S) E)))
   (define-values (S*^ K*) (can* p (add (:unknown S) E)))
   (cond [(eq? 'present (get S S^ #f)) (must p (add (:present S) E))]
         [(not (eq? 'present (get S S*^ #f))) (must p (add (:absent S) E))]
         [else (values S^ K)])]
  [((sel _ (pause _)) E)
   (if (skip-selected)
       (values null (list 1))
       (values null (list 0)))])

(module+ test
  (let ()
    (define-values (S K)
      (must (seq (pause)
                 (present 'hour (exit 'hour-await-trap26 2) (nothing)))
            (list (:unknown 'check-aptt1671770) (:present 'minute) (:absent 'hour))))
    (check-equal? S '())
    (check-equal? K '(1)))
  (let ()
    (define-values (S K)
      (without-selected
       (must (seq (sel (pause))
                  (present 'hour (exit 'hour-await-trap26 2) (nothing)))
             (list (:unknown 'check-aptt1671770) (:present 'minute) (:absent 'hour)))))
    (check-equal? S '())
    (check-equal? K '(1)))
  (let ()
    (define-values (S K)
      (must (loop (seq (sel (pause))
                       (present 'hour (exit 'hour-await-trap26 2) (nothing))))
            (list (:unknown 'check-aptt1671770) (:present 'minute) (:absent 'hour))))
    (check-equal? S '())
    (check-equal? K '(1))))
;; Can

(define/match (can ast E)
  [((nothing _) _) (values null (list 0))]
  [((pause _) _) (values null (list 1))]
  [((exit _ _ k) _) (values null (list k))]
  [((emit _ S) _) (values (list (:present S)) (list 0))]
  [((present _ S then else) _)
   (cond [(has-selected? then) (can then E)]
         [(has-selected? else) (can else E)]
         [else
          (case (get S E)
            [(present) (can then E)]
            [(absent) (can else E)]
            [(unknown) (U (can then E) (can else E))])])]
  [((suspend _ S p) E)
   (cond [(has-selected? p)
          (case (get S E)
            [(present) (values null (list 1))]
            [(absent) (can p E)]
            [(unknown) (values null (list 1))])]
         [else (can p E)])]
  [((seq _ left right) E)
   (define-values (S K) (can left E))
   (cond [(has-selected? right) (can right E)]
         [(not (member 0 K)) (values S K)]
         [else
          (let-values ([(Sr Kr) (can right E)])
            (values (append S Sr)
                    (append (remove 0 K) Kr)))])]
  [((loop _ p) E)
   (define-values (S K) (can p E))
   (cond [(has-selected? p)
          (if (not (member 0 K))
              (values S K)
              (let-values ([(S* K*) (without-selected (can p E))])
                (values (append S S*) (append (remove 0 K) K*))))]
         [else (values S K)])]
  [((par _ l r) E)
   (match* ((has-selected? l) (has-selected? r))
     [(#t #t) (U/max (can l E) (can r E))]
     [(#t #f) (can l E)]
     [(#f #t) (can r E)]
     [(#f #f) (U/max (can l E) (can r E))])]
  [((trap _ T p) E) (harp (can p E))]
  [((signal _ S p) E)
   (define-values (S^ K) (can p (add (:unknown S) E)))
   (cond [(eq? 'present (get S S^))
          (define-values (S^ K) (add (:absent S) E))
          (values (rem S S^) K)]
         [else (values (rem S S^) K)])]
  [((sel _ (pause _)) E) (values null (list 0))])
  ;; Can+

(define/match (can* ast E)
  [((nothing _) _) (values null (list 0))]
  [((pause _) _) (values null (list 1))]
  [((exit _ _ k) _) (values null (list k))]
  [((emit _ S) _) (values (list (:present S)) (list 0))]
  [((present _ S then else) _)
   (cond [(has-selected? then) (can then E)]
         [(has-selected? else) (can else E)]
         [else
          (case (get S E)
            [(present) (can* then E)]
            [(absent) (can* else E)]
            [(unknown) (U (can then E) (can else E))])])]
  [((suspend _ S p) E)
   (cond [(has-selected? p)
          (case (get S E)
            [(present) (values null (list 1))]
            [(absent) (can* p E)]
            [(unknown) (U (values null (list 1))
                          (can p E))])]
         [else (can* p E)])]
  [((seq _ left right) E)
   (define-values (S* K*) (can* left E))
   (define-values (Sm Km) (must left E))
   (define-values (Sr Kr) (can* right E))
   (cond [(has-selected? right) (values Sr Kr)]
         [(not (member 0 S*)) (values S* K*)]
         [(and (member 0 S*) (member 0 Km))
          (values (append S* Sr)
                  (append (remove 0 K*) Kr))]
         [else
          (define-values (Sc Kc) (can left E))
          (values (append S* Sc)
                  (values (remove 0 K*) Kc))])]
  [((loop _ p) E)
   (define-values (S K) (can* p E))
   (define-values (Sm Km) (must p E))
   (cond [(has-selected? p)
          (cond [(not (member 0 K)) (values S K)]
                [(member 0 Km)
                 (define-values (S* K*) (without-selected (can* p E)))
                 (values (append S S*) (append (remove 0 K) K*))]
                [else
                 (define-values (S* K*) (without-selected (can p E)))
                 (values (append S S*) (append (remove 0 K) K*))])]
         [else (values S K)])]
  [((par _ l r) E)
   (match* ((has-selected? l) (has-selected? r))
     [(#t #t) (U/max (can* l E) (can* r E))]
     [(#t #f) (can* l E)]
     [(#f #t) (can* r E)]
     [(#f #f) (U/max (can* l E) (can* r E))])]
  [((trap _ T p) E) (harp (can* p E))]
  [((signal _ S p) E)
   (define-values (Sm Km) (must p (add (:unknown S) E)))
   (define-values (S* K*) (can* p (add (:unknown S) E)))
   (cond
     [(eq? 'present (get S Sm #f))
      (define-values (S^ K^) (can* p (add (:present S) E)))
      (values (remove S S^) K^)]
     [(eq? 'present (get S S* #f))
      (define-values (S^ K^) (can* p (add (:absent S) E)))
      (values (rem S S^) K^)]
     [else (values (rem S S*) K*)])]
  [((sel _ (pause _)) E) (values null (list 0))])

(define-syntax-rule (U/max a b)
  (let ()
    (define-values (l1 l2) a)
    (define-values (r1 r2) b)
    (values (append l1 r1)
            (if (or (null? l2) (null? r2))
                null
                (list (apply max (append l2 r2)))))))
(define-syntax-rule (U a b)
  (let ()
    (define-values (l1 l2) a)
    (define-values (r1 r2) b)
    (values (append l1 r1)
            (append l2 r2))))

(define-syntax-rule (harp a)
  (let ()
    (define-values (S K) a)
    (values S
            (map (lambda (K) (cond [(= K 2) 0]
                                   [(> K 2) (sub1 K)]
                                   [else K]))
                 K))))

(define (rem S E)
  (filter (lambda (p) (equal? S (presence-S p))) E))
(define (add S E) (cons S E))

(define sentinal (gensym))
(define (get S E [v sentinal])
  (match (findf (lambda (x) (equal? S (presence-S x))) E)
    [(:present _) 'present]
    [(:absent _) 'absent]
    [(:unknown _) 'unknown]
    [#f (if (not (eq? v sentinal))
            v
            (error 'presence "could not find evidence of signal ~a in ~a" S E))]))
(define skip-selected (make-parameter #f))
(define (has-selected? p)
  (and (not (skip-selected))
       (ast-selected? p)))

(define-syntax-rule (without-selected e)
  (parameterize ([skip-selected #t])
    e))
