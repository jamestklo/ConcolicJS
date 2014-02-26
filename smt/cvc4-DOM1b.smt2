;http://rise4fun.com/Z3/eyga empty
;http://rise4fun.com/Z3/0TJP saved text
(set-logic ALL_SUPPORTED);
(set-option :produce-models true);
(set-option :produce-assignments true);
(set-option :produce-unsat-cores true);
(set-option :interactive-mode true);
(set-option :incremental true);

(declare-sort Node 0);
(declare-fun root (Node) Bool);
(declare-fun leaf (Node) Bool);
(declare-fun parent (Node) Node);
(declare-fun children (Node Int) Node);
(declare-fun position (Node) Int);
(declare-fun length (Node) Int);

(declare-fun firstChild (Node) Node);
(declare-fun lastChild (Node) Node);
(declare-fun nextSibling (Node) Node);
(declare-fun prevSibling (Node) Node);

(declare-fun following-sibling (Node Node) Bool);
(declare-fun preceding-sibling (Node Node) Bool);

(declare-fun descendant (Node Node) Bool);
(declare-fun ancestor (Node Node) Bool);

(assert
  (forall
    ((x Node))
    (and 
      (not (= (parent x) x))
      (not (= (nextSibling x) x))
      (not (= (prevSibling x) x))
      (not (= (firstChild x) x))
      (not (= (lastChild x) x))      
      (not (descendant x x))
      (not (ancestor x x))
      (not (following-sibling x x))
      (not (preceding-sibling x x))
      (forall
        ((i Int))
        (not (= (children x i) x))
      )
      (ite 
        (exists ((y Node)) (and (distinct y x) (= (parent x) y))) 
        (> (position x) 0)
        (= (position x) 0)
      ) 
      (ite 
        (exists ((y Node)) (and (distinct y x) (= (parent y) x)))
        (> (length x) 0)
        (= (length x) 0)
      )
      (= (firstChild x) (children x 0))
      (= (lastChild x)  (children x (length x)))
      (= (root x) (= (position x) 0))
      (= (leaf x) (= (length x) 0))
    )
  )
);

(assert
  (forall 
    ((x Node) (y Node))
    (=>
      (distinct x y)
      (and
        (=> 
          (= (parent x) y) 
          (and 
            (not (= (parent y) x))
            (>  (position x) 0)
            (>  (length y) 0)
            (>= (length y) (position x))
            (= (children y (position x)) x)
          )
        )        
        (forall
          ((i Int))
          (=> 
            (= (children y i) x)
            (= (parent x) y)
          )
        )
        (=> (= (firstChild y) x) (not (= (firstChild x) y)))
        (=> (= (lastChild y) x) (not (= (lastChild x) y)))      
        (=> (descendant x y) (not (descendant y x)))
        (=> (ancestor y x) (not (ancestor x y)))
        (=  
          (descendant x y)
          (ancestor y x)
          (or 
            (= (parent x) y)
            (exists
              ((z Node))
              (and (= (parent x) z) (descendant z y))
            )
          )
        )
      )
    )
  )
);

(assert 
  (forall 
    ((x Node) (y Node) (z Node))
    (=>
      (distinct x y z)
      (and 
        (=> (= (parent x) y) (not (= (parent x) z)))
        (=> (= (nextSibling z) x) (not (= (nextSibling z) y)))
      )  
    )
  )
);

(assert
  (forall
    ((x Node) (z Node))
    (=>
      (distinct x z)
      (and 
        (=>
          (= (parent x) (parent z))
          (not (= (position x) (position z)))
        ) 
        (=> (= (nextSibling z) x) (not (= (nextSibling x) z)))
        (=> (= (prevSibling x) z) (not (= (prevSibling z) x)))
        (=
          (= (nextSibling z) x)
          (= (prevSibling x) z)
          (and (= (parent x) (parent z)) (= (position x) (+ (position z) 1)))
        )
        (=> (following-sibling x z) (not (following-sibling z x)))
        (=> (preceding-sibling z x) (not (preceding-sibling x z)))
        (=
          (following-sibling x z)
          (preceding-sibling z x)
          (and (= (parent x) (parent z)) (> (position x) (position z)))
        )
      )
    )
  )
);


(declare-const n0 Node);
(declare-const n1 Node);
(declare-const n2 Node);
(declare-const n3 Node);
(declare-const n4 Node);
(assert (distinct n0 n1 n2 n3 n4));
(assert (= (parent n1) n0));
;(assert (= (firstChild n0) n0));
;(assert (= (nextSibling n1) n2));
;(assert (= (nextSibling n2) n3));
;(assert (= (lastChild n0) n3));
;(assert (= (firstChild n3) n4));
;(assert (= (length n3) 1));
(check-sat);
(get-model);
(get-assignment);
