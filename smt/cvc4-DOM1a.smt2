(set-logic ALL_SUPPORTED);
(set-option :produce-models true);
(set-option :produce-assignments true);
(set-option :produce-unsat-cores true);
(set-option :interactive-mode true);
(set-option :incremental true);

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


(declare-fun id (String Node) Bool);
(declare-fun idStr (Node) String);
(declare-fun tag (String Node) Bool);
(declare-fun tagName (Node) String);
(declare-fun hasClass (String Node) Bool);
(declare-fun classNode (Node) (Array String String));
(assert
  (forall
    ((x Node) (s String))
    (and 
      (=> (id s x) (= (idStr x) s))
      (=> (tag s x) (= (tagName x) s))
      (=>
        (hasClass s x)
        (= (select (classNode x) s) s)
      )
    )
  )
);
(assert
  (forall
    ((x Node))
    (and 
      (=
        (= (idStr x) "")
        (not 
          (exists
            ((s String))
            (id s x)
          )
        )
      )
      (=
        (= (tagName x) "")
        (not 
          (exists
            ((s String))
            (tag s x)
          )
        )
      )
    )
  )
);

(assert
  (forall
    ((x Node) (z Node))
    (and 
      (=>
        (distinct x z) 
        (or 
          (and (= (idStr x) "") (= (idStr z) ""))
          (not (= (idStr x) (idStr z)))
        )
      )
      (=>
        (or 
          (not (= (idStr x) (idStr z)))
          (not (= (tagName x) (tagName z)))
        )
        (distinct x z)
      )
    )
  )
);


(declare-fun hasttribute (Node String) String);
(declare-fun attributeInt (Node String) Int);
(declare-fun attributeBool (Node String) Bool);

(declare-const n0 Node);
(declare-const n1 Node);
(declare-const n2 Node);
(declare-const n3 Node);
(declare-const n4 Node);
(declare-const n5 Node);
(declare-const n6 Node);
(declare-const n7 Node);

(assert (distinct n0 n1 n2 n3 n4 n6 n7));
(assert (or (parent n0 n1) (parent n1 n0)));
(assert (parent n0 n1));
(assert (firstChild n1 n0));
(assert (nextSibling n2 n1));
(assert (nextSibling n3 n2));
(assert (lastChild n3 n0));
(assert (firstChild n4 n3));
(assert (lastChild n4 n5));
(assert (parent n6 n7));
(assert (= (position n7) 11));
(assert (= (length n3) 1));

(assert (id "n0" n0));
(assert (tag "div" n0));
(assert (tag "span" n1)); 
(assert (tag "span" n2)); 
(assert (tag "span" n3));
(assert (tag "span" n4));
(assert (tag "span" n5));
(assert (tag "span" n6));
(assert (tag "span" n7));
(assert (hasClass "content" n0));
(assert (hasClass "body" n0));
(assert (hasClass "1.1" n0));
(assert (hasClass "1.2" n2));
(assert (hasClass "1.3" n0));
(assert (hasClass "1.2" n0));
(check-sat);
(get-model);
(get-assignment);
