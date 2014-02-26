(set-logic ALL_SUPPORTED);
(set-option :produce-models true);
(set-option :produce-assignments true);
(set-option :interactive-mode true);
(set-option :incremental true);

(declare-sort Node 0);
(declare-fun child (Node Node) Bool);
(declare-fun parent (Node Node) Bool);

(assert
  (forall
    ((x Node))
    (and 
      (not (child x x))
      (not (parent x x))
    )
  )
);

(assert
  (forall 
    ((x Node) (y Node))
    (and 
      (=> (child x y) (not (child y x)))
      (=> (parent x y) (not (parent y x)))
      (=  (child x y) (parent y x))
    )
  )
);

(assert 
  (forall 
    ((x Node) (y Node) (z Node)) 
    (=> 
      (and (child x y) (distinct y z)) 
      (not (child x z))
    )
  )
);

(declare-const n0 Node);
(declare-const n1 Node);
(declare-const n2 Node);
(declare-const n3 Node);

(assert (distinct n0 n1 n2 n3));
(assert (or (child n0 n1) (child n1 n0)));
(assert (parent n0 n1));
(assert (child n2 n0));
(assert (child n3 n0));
(check-sat);
(get-model);
