(set-logic ALL_SUPPORTED);
(set-option :produce-models true);
(set-option :produce-assignments true);
(set-option :interactive-mode true);
(set-option :incremental true);

(declare-sort Node 0);
(declare-fun parent (Node) Node);
(declare-fun children (Node Int) Node);

(assert
  (forall
    ((x Node))
    (and 
      (not (= (parent x) x))
      (forall
        ((i Int))
        (not (= (children x i) x))
      )
    )
  )
);

;(assert
  ;(forall 
    ;((x Node) (y Node) (i Int))
    ;(=>
      ;(distinct x y)
      ;(=>
        ;(= (children y i) x)
        ;(and 
          ;(= (parent x) y)
          ;(not
            ;(exists
              ;((j Int))
              ;(or 
                ;(and (not (= j i)) (= (children y j) x))
                ;(= (children x j) y)
              ;)
            ;)
          ;)
        ;)
      ;)
    ;)
  ;)
;);

(assert
  (forall 
    ((x Node) (y Node))
    (=>
      (distinct x y)
      (and 
        (=> (= (parent x) y) (not (= (parent y) x)))
        (=>  
          (= (parent x) y)
          (exists
            ((i Int))
            (and 
              (> i 0)
              (= (children y i) x)
            )
          )
        )
      )
    )
  )
);

;(assert 
;  (forall 
;    ((x Node) (y Node) (z Node)) 
;    (=> 
;      (distinct x y z)
;      (=> 
;       (= (parent x) y)  
;       (not (= (parent x) z))
;     )
;   )
; )
;);

(declare-const n0 Node);
(declare-const n1 Node);
(declare-const n2 Node);
(declare-const n3 Node);

(assert (distinct n0 n1 n2 n3));
(assert (or (= (parent n0) n1) (= (parent n1) n0)));
(assert (= (parent n1) n0));
(assert (= (parent n2) n0));
(assert (= (parent n3) n0));
(check-sat);
(get-model);
