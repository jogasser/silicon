
(define-fun seq_extract_$SAN$ ((s $S$) (i Int) (j Int)) $S$
  (seq.extract s (ite (< i 0) 0 i) (ite (< j 0) 0 j )))