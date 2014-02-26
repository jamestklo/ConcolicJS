(set-logic ALL_SUPPORTED);
(set-option :produce-models true);
(set-option :produce-assignments true);
(set-option :produce-unsat-cores true);
(set-option :interactive-mode true);
(set-option :incremental true);

(declare-sort Node 0);
(declare-fun hasClass (String Node) Bool);
(declare-fun classNode (Node) (Array String String));
(declare-fun attribute (Node String) String);
(declare-fun attrsNode (Node) (Array String String));

(assert 
  (forall 
    ((x Node) (s String))
    (=>
      (hasClass s x)
      (= (select (classNode x) s) s)
    )
  )
);

(declare-const n0 Node);
(declare-const n1 Node);
(declare-const n2 Node);
(declare-const n3 Node);
(declare-const n4 Node);
(declare-const n5 Node);
(declare-const n6 Node);
(declare-const n7 Node);
(assert (distinct n0 n1 n2 n3 n4 n5 n6 n7));

(assert (hasClass "body" n0));
(assert (hasClass "content" n0));
(assert (hasClass "1.1" n0));
(assert (hasClass "1.1" n1));
(assert (hasClass "1.1" n2));
(assert (hasClass "1.2" n0));
(assert (hasClass "1.2" n2));
(assert (hasClass "1.3" n0));

(assert (hasClass " " n3));
(assert (hasClass " " n4));
(assert (hasClass " " n5));
(assert (hasClass " " n6));
(assert (hasClass " " n7));

(check-sat);
(get-model);
(get-assignment);
