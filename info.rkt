#lang info
(define name "esterel")
(define collection 'use-pkg-name)
(define version "0.1")

(define deps
  '("base" "rackunit-lib" "redex-lib" "redex-gui-lib"))
(define build-deps '())

(define test-omit-paths '("examples/causality.rkt"))
