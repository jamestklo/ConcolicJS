(set-logic ALL_SUPPORTED);
(set-option :produce-models true);
(set-option :produce-assignments true);
(set-option :produce-unsat-cores true);
(set-option :interactive-mode true);
(set-option :incremental true);

(declare-const sessionID String);
(declare-sort Node 0);
(declare-fun root (Node) Bool);
(declare-fun leaf (Node) Bool);
(declare-fun parent (Node Node) Bool);
(declare-fun position (Node) Int);
(declare-fun length (Node) Int);

(declare-fun following-sibling (Node Node) Bool);
(declare-fun preceding-sibling (Node Node) Bool);

(declare-fun descendant (Node Node) Bool);
(declare-fun ancestor (Node Node) Bool);

(declare-fun firstChild (Node Node) Bool);
(declare-fun lastChild (Node Node) Bool);

(declare-fun nextSibling (Node Node) Bool);
(declare-fun prevSibling (Node Node) Bool);

(declare-fun id (Node) String);
(declare-fun tag (Node) String);
(assert
  (forall
    ((x Node))
    (and 
      (not (parent x x))
      (not (nextSibling x x))
      (not (prevSibling x x))
      (not (descendant x x))
      (not (ancestor x x))
      (not (following-sibling x x))
      (not (preceding-sibling x x))
      (not (firstChild x x))
      (not (lastChild x x))
      (ite 
        (exists ((y Node)) (and (distinct y x) (parent y x))) 
        (> (position x) 0)
        (= (position x) 0)
      ) 
      (ite 
        (exists ((y Node)) (and (distinct y x) (parent x y)))
        (> (length x) 0)
        (= (length x) 0)
      )
      (= (root x) (= (position x) 0))
      (= (leaf x) (= (length x) 0))
    )
  )
);

(assert
  (forall
    ((n0 Node) (n1 Node))
    (=>
      (or
        (parent n0 n1)
        (nextSibling n0 n1)
        (prevSibling n0 n1)
        (descendant n0 n1)
        (ancestor n0 n1)
        (following-sibling n0 n1)
        (preceding-sibling n0 n1)
        (firstChild n0 n1)
        (lastChild n0 n1)
        (not (= (id n0) (id n1)))
        (not (= (tag n0) (tag n1)))
		(not (= (position n0) (position n1)))
		(not (= (length n0) (length n1)))
      )
      (distinct n0 n1)
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
          (parent y x) 
          (and 
            (not (parent x y))
            (>  (position x) 0)
            (>  (length y) 0)
            (>= (length y) (position x))
          )
        )
        (=  (and (parent y x) (= (position x) 1)) (firstChild x y))
        (=> (firstChild x y) (not (firstChild y x)))
        (=  (and (parent y x) (= (position x) (length y))) (lastChild x y))
        (=> (lastChild x y) (not (lastChild y x)))      
        (=> (descendant x y) (not (descendant y x)))
        (=> (ancestor y x) (not (ancestor x y)))
        (=  
          (descendant x y)
          (ancestor y x)
          (or 
            (parent y x)
            (exists
              ((z Node))
              (and (parent z x) (ancestor y z))
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
        (=> (parent y x) (not (parent z x)))
        (=> (nextSibling x z) (not (nextSibling x y)))
        (=>
         (and (parent y x) (parent y z))
         (not (= (position x) (position z)))
        )
      )
    )
  )
);

(declare-fun parentNode (Node) Node);
(assert
  (forall
    ((x Node) (y Node))
    (=>
      (distinct x y)
      (=> (parent y x) (= (parentNode x) y))
    )
  )
);

(assert
  (forall
    ((x Node) (z Node))
    (=>
      (distinct x z)
      (and 
        (=> (nextSibling x z) (not (nextSibling z x)))
        (=> (prevSibling z x) (not (prevSibling x z)))
        (=
          (nextSibling x z)
          (prevSibling z x)
          (exists
            ((y Node))
            (and (parent y x) (parent y z) (= (position x) (+ (position z) 1)))
          )
        )
        (=> (following-sibling x z) (not (following-sibling z x)))
        (=> (preceding-sibling z x) (not (preceding-sibling x z)))
        (=
          (following-sibling x z)
          (preceding-sibling z x)
          (exists
            ((y Node))
            (and (parent y x) (parent y z) (> (position x) (position z)))
          )
        )
       (or 
          (= "" (id x))
          (= "" (id z))
          (not (= (id x) (id z)))
        )
		(or 
		  (= "" (tag x))
		  (= "" (tag z))
		  (not (= (tag x) (tag z)))
		  (not (= (position x) (position z)))
		  (not (= (length x) (length z)))
		  (not (= (parentNode x) (parentNode z)))
		  (forall
		    ((y Node))
			(and 
			  (=> (firstChild y x) (not (firstChild y z)))
			  (=> (firstChild y z) (not (firstChild y x)))
			)
		  )	  
		  (not (= (id x) (id z)))
		)
      )
    )
  )
);

(declare-fun hasClass (String Node) Bool);
(declare-fun className (Node) (Array String String));
(assert
  (forall
    ((x Node) (s String))
    (=>
      (hasClass s x)
      (= (select (className x) s) s)
    )
  )
);

(declare-fun attribute (Node String) String);
(declare-fun attributeInt (Node String) Int);
(declare-fun attributeBool (Node String) Bool);


(assert (= sessionID "sessionID"));
(declare-const n0 Node);
(declare-const n1 Node);
(declare-const n2 Node);
(declare-const n3 Node);
(declare-const n3a Node);
(declare-const n4 Node);
(declare-const n5 Node);
(declare-const n6 Node);

(assert (or (parent n0 n1) (parent n1 n0)));
(assert (parent n0 n1));
(assert (firstChild n1 n0));
(assert (nextSibling n2 n1));
(assert (nextSibling n3 n2));
(assert (lastChild n3 n0));
(assert (firstChild n4 n3));
(assert (lastChild n4 n3a));
(assert (parent n5 n6));
(assert (= (position n6) 11));
(assert (= (length n3) 1));

(assert (= (id n0)  "sessionID_n0"));
(assert (= (id n3)  "sessionID_n3"));
(assert (= (id n3a) "sessionID_n3"));

(assert (= (tag n0) "sessionID_div"));
(assert (= (tag n1) "sessionID_span")); 
(assert (= (tag n2) "sessionID_span"));
(assert (= (tag n5) "sessionID_span"));

(assert (hasClass "content" n0));
(assert (hasClass "body" n0));
(assert (hasClass "1.1" n0));
(assert (hasClass "1.2" n0));
(assert (hasClass "1.3" n0));
(assert (hasClass "1.2" n2));

(check-sat);
(get-model);
(get-assignment);
