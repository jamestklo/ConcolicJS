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
(declare-fun parentElement (Node Node) Bool);
(declare-fun position (Node) Int);
(declare-fun length (Node) Int);

(declare-fun following-sibling (Node Node) Bool);
(declare-fun preceding-sibling (Node Node) Bool);

(declare-fun descendant (Node Node) Bool);
(declare-fun ancestor (Node Node) Bool);

(declare-fun firstElementChild (Node Node) Bool);
(declare-fun lastElementChild (Node Node) Bool);

(declare-fun nextElementSibling (Node Node) Bool);
(declare-fun previousElementSibling (Node Node) Bool);

(declare-fun id (Node) String);
(declare-fun tag (Node) String);

(assert
  (forall
    ((x Node))
    (and 
      (= x x)
      (not (parentElement x x))
      (not (nextElementSibling x x))
      (not (previousElementSibling x x))
      (not (descendant x x))
      (not (ancestor x x))
      (not (following-sibling x x))
      (not (preceding-sibling x x))
      (not (firstElementChild x x))
      (not (lastElementChild x x))
      (ite 
        (exists ((y Node)) (and (distinct y x) (parentElement y x))) 
        (> (position x) 0)
        (= (position x) 0)
      ) 
      (ite 
        (exists ((y Node)) (and (distinct y x) (parentElement x y)))
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
        (not (= n0 n1))
        (parentElement n0 n1)
        (nextElementSibling n0 n1)
        (previousElementSibling n0 n1)
        (descendant n0 n1)
        (ancestor n0 n1)
        (following-sibling n0 n1)
        (preceding-sibling n0 n1)
        (firstElementChild n0 n1)
        (lastElementChild n0 n1)
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
        (not (= x y))
        (=> 
          (parentElement y x) 
          (and 
            (not (parentElement x y))
            (>  (position x) 0)
            (>  (length y) 0)
            (>= (length y) (position x))
          )
        )
        (=  (and (parentElement y x) (= (position x) 1)) (firstElementChild x y))
        (=> (firstElementChild x y) (not (firstElementChild y x)))
        (=  (and (parentElement y x) (= (position x) (length y))) (lastElementChild x y))
        (=> (lastElementChild x y) (not (lastElementChild y x)))      
        (=> (descendant x y) (not (descendant y x)))
        (=> (ancestor y x) (not (ancestor x y)))
        (=  
          (descendant x y)
          (ancestor y x)
          (or 
            (parentElement y x)
            (exists
              ((z Node))
              (or 
                (and (parentElement z x) (ancestor y z))
                (and (parentElement y z) (ancestor z x))
              )
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
        (=> (parentElement y x) (not (parentElement z x)))
        (=> (nextElementSibling x z) (not (nextElementSibling x y)))
        (=>
         (and (parentElement y x) (parentElement y z))
         (not (= (position x) (position z)))
        )
      )
    )
  )
);

(declare-fun parentAlias (Node) Node);
(assert
  (forall
    ((x Node) (y Node))
    (=>
      (distinct x y)
      (=> (parentElement y x) (= (parentAlias x) y))
    )
  )
);

(assert
  (forall
    ((x Node) (z Node))
    (=>
      (distinct x z)
      (and 
        (=> (nextElementSibling x z) (not (nextElementSibling z x)))
        (=> (previousElementSibling z x) (not (previousElementSibling x z)))
        (=
          (nextElementSibling x z)
          (previousElementSibling z x)
          (exists
            ((y Node))
            (and (parentElement y x) (parentElement y z) (= (position x) (+ (position z) 1)))
          )
        )
        (=> (following-sibling x z) (not (following-sibling z x)))
        (=> (preceding-sibling z x) (not (preceding-sibling x z)))
        (=
          (following-sibling x z)
          (preceding-sibling z x)
          (exists
            ((y Node))
            (and (parentElement y x) (parentElement y z) (> (position x) (position z)))
          )
        )
        (or 
          (= " " (id x))
          (= " " (id z))
          (not (= (id x) (id z)))
        )
		(or 
		  (= " " (tag x))
		  (= " " (tag z))
		  (not (= (tag x) (tag z)))
		  (not (= (position x) (position z)))
		  (not (= (length x) (length z)))
		  (not (= (parentAlias x) (parentAlias z)))
		  (forall
		    ((y Node))
			(and 
			  (=> (firstElementChild y x) (not (firstElementChild y z)))
			  (=> (firstElementChild y z) (not (firstElementChild y x)))
			)
		  )	  
		  (not (= (id x) (id z)))
		)
      )
    )
  )
);

(declare-fun className (Node) (Array String String));
(declare-fun attribute (Node) (Array String String));
;(declare-fun attributeStr (Node String) String);
;(declare-fun attributeInt (Node String) Int);
;(declare-fun attributeBool (Node String) Bool);

;(declare-sort Object 0); 

; product:      jalangi-opensource  jalangy-private
; solvers:      jalangi-cvc4        jalangi-z3              cvc4-cloud      msz3-cloud
; data types:   jalangi-DOM         jalangi-events
; cloud:        jalangi-cloud       jalangi-parallel        jalangi-docker:[amazon, google, etc.]
; analytics:    reporting, visualization, hadoop
; workflow:     

(assert (= sessionID "sessionID_"));
(declare-const n0 Node);
(declare-const n0a Node);
(declare-const n1 Node);
(declare-const n2 Node);
(declare-const n3 Node);
(declare-const n3a Node);
(declare-const n4 Node);
(declare-const n5 Node);

(assert (or (parentElement n0 n1) (parentElement n1 n0)));
(assert (parentElement n0 n1));
(assert (firstElementChild n1 n0));
(assert (nextElementSibling n2 n1));
(assert (nextElementSibling n3 n2));
(assert (lastElementChild n3 n0));
(assert (firstElementChild n4 n3));
(assert (lastElementChild n4 n3a));
(assert (parentElement n5 n0a));
(assert (= (position n0a) 11));
(assert (= (length n5) 11));
(assert (= (length n3) 1));

(assert (= (id n0)	(str.++ sessionID "n0")));
(assert (= (id n3)	(str.++ sessionID "n3")));
(assert (= (id n3a)	(str.++ sessionID "n3")));
(assert (= (tag n0) (str.++ sessionID "t0")));
(assert (= (tag n1) (str.++ sessionID "t1"))); 
(assert (= (tag n2) (str.++ sessionID "t2")));
(assert (= (tag n4) (str.++ sessionID "t4")));

;(assert (= (select (className n0) (str.++ sessionID "body")) "body"));
;(assert (= (select (className n0) (str.++ sessionID "content")) "content"));
;(assert (= (select (className n0) (str.++ sessionID "0.0")) "0.0"));
;(assert (= (select (className n0) (str.++ sessionID "0.2")) "0.2"));
;(assert (= (select (className n0) (str.++ sessionID "0.3")) "0.3"));
;(assert (= (select (className n2) (str.++ sessionID "0.2")) "0.2"));
;(assert (= (select (className n2) (str.++ sessionID "2.2")) "2.2"));
;(assert (= (select (className n2) (str.++ sessionID "body")) "body"));
;(assert (= (select (className n4) (str.++ sessionID "body")) "body"));
;(assert (= (select (className n0a) "n0a") " "));
;(assert (= (select (className n1) "n1") " "));
;(assert (= (select (className n3) "n3") " "));
;(assert (= (select (className n3a) "n3a") " "));
;(assert (= (select (className n5) "n5") " "));

(declare-const v00 String);
(assert (= (select (attribute n0) (str.++ sessionID "k00")) v00));
(assert (= (select (attribute n0) (str.++ sessionID "k01")) "v01"));
(assert (= (select (attribute n0a)  "n0a") " "));
(assert (= (select (attribute n1)   "n1") " "));
(assert (= (select (attribute n2) (str.++ sessionID "k00")) "k00"));
(assert (= (select (attribute n2) (str.++ sessionID "k20")) "k21"));
(assert (= (select (attribute n3)   "n3") " "));
(assert (= (select (attribute n3a)  "n3a") " "));
(assert (= (select (attribute n4)   "n4") " "));
(assert (= (select (attribute n5)   "n5") " "));

(declare-const s0 String);
(declare-const s1 String);
(assert (= v00 "v00"));
(assert (= (str.++ "abc" s1) s0));
(assert (= (str.len s1) 3));

(check-sat);
(get-model);
(get-assignment);
