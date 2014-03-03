(set-logic ALL_SUPPORTED);
(set-option :produce-models true);
(set-option :produce-assignments true);
(set-option :produce-unsat-cores true);
(set-option :interactive-mode true);
(set-option :incremental true);

(declare-sort Node 0);
(declare-sort Object 0);

(declare-fun hasClass (String Node) Bool);
(declare-fun classNode (Node) (Array String String));
(assert 
  (forall 
    ((x Node) (s String))
    (=>
      (hasClass s x)
      (= (select (classNode x) s) s)
    )
  )
);

(define-fun booleanToNumber ((x Bool)) Real     (ite x 1        0));
(define-fun booleanToString ((x Bool)) String   (ite x "true"   "false"));
(define-fun numberToBoolean ((x Real)) Bool     (ite (= x 0) false true));
(define-fun decimalToString ((x Real)) String
  ite (= x 0) "0" "1"
);
(define-fun numberToString  ((x Real)) String   
  (ite (= x 0) "0"
  (ite (and (> x 0) (< x 1)) (str.++ "0." (decimalToString x))
  (ite (= x 1) "1"
  (ite (and (> x 1) (< x 2)) (str.++ "1." (decimalToString (- x 1)))
  (ite (= x 2) "2"
  (ite (and (> x 2) (< x 3)) (str.++ "2." (decimalToString (- x 2)))
  (ite (= x 3) "3"
  (ite (and (> x 3) (< x 4)) (str.++ "3." (decimalToString (- x 3)))
  (ite (= x 4) "4"
  (ite (and (> x 4) (< x 5)) (str.++ "4." (decimalToString (- x 4)))
  (ite (= x 5) "5"
  (ite (and (> x 5) (< x 6)) (str.++ "5." (decimalToString (- x 5)))
  (ite (= x 6) "6"
  (ite (and (> x 6) (< x 7)) (str.++ "6." (decimalToString (- x 6)))
  (ite (= x 7) "7"
  (ite (= x 8) "8"
  (ite (= x 9) "9"
  (ite (< x 0)  (str.++ "-" (numberToString 0-x))
  (ite (> x 10) "10"
  ))))))))))))
);
(define-fun objectToBoolean ((x Object)) Bool);
(declare-const null String);
(declare-const n0 Node);
(declare-const n1 Node);
(declare-const n2 Node);
(declare-const n3 Node);
(declare-const n4 Node);
(declare-const n5 Node);
(declare-const n6 Node);
(declare-const n7 Node);
(declare-const n8 Node);

(declare-const boolean0 Bool);
(declare-const number1 Real);
(declare-const string2 String);
(assert boolean0);
(assert (= (ite boolean0 1 0) number1));
(assert (= string2 (numberToString 1)));
;(assert (distinct n0 n1 n2 n3 n4 n5 n6 n7));

(assert (hasClass "body" n0));
(assert (hasClass "content" n0));
(assert (hasClass "1.1" n0));
(assert (hasClass "1.2" n0));
(assert (hasClass "1.3" n0));
(assert (hasClass "1.1" n1));
(assert (hasClass "1.1" n2));
(assert (hasClass "1.2" n2));
(assert (hasClass " " n3));
(assert (hasClass " " n4));
(assert (hasClass " " n5));
(assert (hasClass " " n6));
(assert (hasClass " " n7));

(check-sat);
(get-model);
(get-assignment);
