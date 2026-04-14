#lang racket

(require "./set-test.rkt"
         "./tuple-test.rkt"
         "./el-test.rkt")

(require rackunit/gui)

(test/gui
  SET
  TUPLE
  EL)
