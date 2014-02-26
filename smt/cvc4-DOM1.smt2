(set-logic ALL_SUPPORTED);
(set-option :produce-models true);
(set-option :dump-models true);
(set-option :produce-assignments true);
(set-option :interactive-mode true);
(set-option :incremental true);

(declare-sort Node 0);
(declare-fun root (Node) Bool);
(declare-fun parent (Node Node) Bool);
(declare-fun child (Node Node) Bool);
(declare-fun children (Node Node Int) Bool);
(declare-fun childIndex (Node) Int);
(declare-fun childrenLength (Node) Int);

(declare-fun following-sibling (Node Node) Bool);
(declare-fun preceding-sibling (Node Node) Bool);

(declare-fun descendant (Node Node) Bool);
(declare-fun ancestor (Node Node) Bool);

(declare-fun firstChild (Node Node) Bool);
(declare-fun lastChild (Node Node) Bool);

(declare-fun nextSibling (Node Node) Bool);
(declare-fun previousSibling (Node Node) Bool);

(assert 
  (forall 
    ((x Node) (y Node)) 
    (=> 
      (and (root y) (distinct x y)) 
      (descendant x y)
    )
  )
);

(assert 
  (forall 
    ((x Node)) 
    (not (child x x))
  )
);

(assert 
  (forall 
    ((x Node) (y Node)) 
    (=> 
      (child x y) 
      (not (child y x))
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

(assert 
  (forall 
    ((x Node) (y Node))  
    (= 
      (descendant x y) 
      (or 
        (child x y) 
        (exists 
          ((z Node)) 
          (or 
            (and (descendant x z) (child z y))
            (and (child x z) (descendant z y))
          )
        )
      )
    )
  )
);

(assert 
  (forall 
    ((x Node) (y Node) (j Int))
    (=> (children x y j) (and (child x y) (>= j 0)))
  )
);

(assert 
  (forall
    ((x Node) (j Int))
    (=
      (= (childIndex x) j)
      (exists 
        ((y Node))
        (children x y j)
      )        
    )
  )
);

(assert
  (forall
    ((y Node) (j Int)) 
    (=
      (= (childrenLength y) j)
      (exists
        ((x Node))
        (and 
          (children x y (- j 1))
          (lastChild x y)
        )
      )
    )
  )
);

(assert 
  (forall 
    ((x Node) (y Node)) 
    (=
      (firstChild x y)
      (children x y 0)
    )
  )
);

(assert
  (forall
    ((x Node) (y Node))
    (=> 
      (lastChild x y)
      (exists
        ((j Int))
        (and 
          (children x y j)
          (forall
            ((z Node) (k Int))
            (=>
              (and 
                (children z y k)
                (distinct z x)
              )
              (< k j)
            )
          )
        )
      )
    )
  )
);

(assert
  (forall
    ((x Node))
    (not (following-sibling x x))
  )
);
	
(assert 
  (forall 
    ((x Node) (z Node)) 
    (=
      (following-sibling x z)
      (exists
        ((y Node) (i Int) (j Int))
        (and 
          (children x y i)
          (children z y j)
          (> i j)
        )
      )
    )
  )
);

(assert
  (forall 
    ((x Node))
    (not (nextSibling x x))
  )
);

(assert
  (forall
    ((x Node) (z Node)) 
    (=
      (nextSibling x z)
      (exists
        ((y Node) (i Int) (j Int))
        (and
          (children x y i)
          (children z y j)
          (= (+ j 1) i)
        )
      )
    )
  )
);

(assert
  (forall
    ((x Node) (y Node))
    (= (parent y x) (child x y))
  )
);

(assert
  (forall
    ((x Node) (y Node))
    (=>
      (parent y x)
      (not (parent x y))
    )
  )
);

(assert
  (forall
    ((x Node) (y Node)) 
    (= (ancestor y x) (descendant x y))   
  )
);

(assert
  (forall 
    ((x Node) (y Node))
    (=> (ancestor y x) (not (ancestor x y)))
  )
);

(assert
  (forall
    ((x Node) (z Node))
    (= (preceding-sibling z x) (following-sibling x z))
  )
);

(assert
  (forall 
    ((x Node) (z Node))
    (=>
      (preceding-sibling z x)
      (not (preceding-sibling x z))
    )
  )
);

(assert
  (forall
    ((x Node) (z Node))
    (= (previousSibling z x) (nextSibling x z))
  )
);

(assert
  (forall 
    ((x Node) (z Node))
    (=> (previousSibling z x) (not (previousSibling x z)))
  )
);

(declare-fun x1() Node);
(declare-fun y1() Node);
(assert (distinct x1 y1));
(assert (child x1 y1));
(assert (parent y1 x1));
(check-sat);
(get-model);
