#lang racket
(provide print-as-esterel)
(require esterel/ast esterel/front-end)

(define indent (make-parameter 0))
(define-syntax-rule (inc-indent e ...)
  (parameterize ([indent (+ 2 (indent))])
    e ...))

(define (print-as-esterel name m)
  (do-print "module " (to-esterel-name name) " :\n")
  (do-print "input ")
  (pwc (machine-valid-ins m))
  (do-print ";\n")
  (do-print "output ")
  (pwc (machine-valid-outs m))
  (do-print ";\n")
  (inc-indent
   (->esterel (machine-prog m)))
  (do-print "\nend module\n"))

(define (pwc l)
  (cond [(empty? l) (void)]
        [(empty? (rest l))
         (display (to-esterel-name (first l)))]
        [else
         (display (to-esterel-name (first l)))
         (display ", ")
         (pwc (rest l))]))

(define (->esterel p)
  (match p
    [(nothing) (do-print "nothing")]
    [(pause) (do-print "pause")]
    [(seq left right)
     (->esterel left)
     (do-print "\n")
     (do-print " ;\n")
     (->esterel right)]
    [(par left right)
     (inc-indent
      (->esterel left))
     (do-print "\n")
     (do-print "||\n")
     (inc-indent
      (->esterel right))]
    [(loop p*)
     (do-print "loop\n")
     (inc-indent (->esterel p*))
     (do-print "\n")
     (do-print "end loop\n")]
    [(signal S p)
     (do-print "signal " (to-esterel-name S) " in\n")
     (inc-indent (->esterel p))
     (do-print "\n")
     (do-print "end signal\n")]
    [(emit S) (do-print "emit " (to-esterel-name S))]
    [(suspend S p)
     (do-print "suspend\n")
     (inc-indent (->esterel p))
     (do-print "\n")
     (do-print "when " (to-esterel-name S) "\n")]
    [(present S then else)
     (do-print "present " (to-esterel-name S) " then\n")
     (inc-indent (->esterel then))
     (do-print "\n")
     (do-print "else\n")
     (inc-indent (->esterel else))
     (do-print "\n")
     (do-print "end\n")]
    [(trap T p)
     (do-print "trap " (to-esterel-name T) " in\n")
     (inc-indent (->esterel p))
     (do-print "\n")
     (do-print "end trap\n")]
    [(exit T _) (do-print "exit " (to-esterel-name T))]))

(define (do-print . p)
  (for ([_ (indent)]) (display " "))
  (for ([s p]) (display s)))

(define (to-esterel-name s)
  (if (number? s)
      (string (integer->char (+ 65 s)))
      (apply string
             (flatten
              (for/list ([c (symbol->string s)])
                (match c
                  [#\- #\_]
                  [#\< (list #\L #\T)]
                  [#\> (list #\G #\T)]
                  [#\( (list #\O #\P)]
                  [#\) (list #\C #\P)]
                  [#\space (list #\S #\P #\A #\C #\E)]
                  [else (char-upcase c)]))))))
