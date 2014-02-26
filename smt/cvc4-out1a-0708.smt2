unsupported
unknown
(model
; cardinality of Node is 8
(declare-sort Node 0)
; rep: @uc_Node_0
; rep: @uc_Node_1
; rep: @uc_Node_2
; rep: @uc_Node_3
; rep: @uc_Node_4
; rep: @uc_Node_5
; rep: @uc_Node_6
; rep: @uc_Node_7
(define-fun hasClass (($x1 String type) ($x2 Node)) Bool (ite (= "body" $x1) (= @uc_Node_0 $x2) (ite (= "content" $x1) (= @uc_Node_0 $x2) (ite (= "1.1" $x1) (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (ite (= @uc_Node_6 $x2) false (not (= @uc_Node_7 $x2)))))) (ite (= "1.2" $x1) (ite (= @uc_Node_0 $x2) true (= @uc_Node_2 $x2)) (ite (= "1.3" $x1) (= @uc_Node_0 $x2) (ite (= " " $x1) (ite (= @uc_Node_3 $x2) true (ite (= @uc_Node_4 $x2) true (ite (= @uc_Node_5 $x2) true (ite (= @uc_Node_6 $x2) true (= @uc_Node_7 $x2))))) false)))))))
(define-fun classNode ((_ufmt_1 Node)) (Array String type String type) (ite (= @uc_Node_0 _ufmt_1) (store (store (store (store (store (store (__array_store_all__ (Array String type String type) "B") "" "AAAAAAAAAAAA") "body" "body") "content" "content") "1.1" "1.1") "1.2" "1.2") "1.3" "1.3") (ite (= @uc_Node_2 _ufmt_1) (store (store (store (__array_store_all__ (Array String type String type) "C") "" "AAAAAAAAAAA") "1.1" "1.1") "1.2" "1.2") (ite (= @uc_Node_3 _ufmt_1) (store (store (store (__array_store_all__ (Array String type String type) "D") "" "AAAAAAAAAAAAA") "1.1" "AAAAAAAAA") " " " ") (ite (= @uc_Node_4 _ufmt_1) (store (store (store (__array_store_all__ (Array String type String type) "E") "" "AAAAAAAAAAAAAA") "1.1" "AAAAAAAA") " " " ") (ite (= @uc_Node_5 _ufmt_1) (store (store (store (__array_store_all__ (Array String type String type) "F") "" "AAAAAAAAAAAAAAA") "1.1" "AAAAAA") " " " ") (ite (= @uc_Node_6 _ufmt_1) (store (store (store (__array_store_all__ (Array String type String type) "G") "" "AAAAAAAAAAAAAAAA") "1.1" "AAAAA") " " " ") (ite (= @uc_Node_7 _ufmt_1) (store (store (store (__array_store_all__ (Array String type String type) "H") "" "AAAAAAAAAAAAAAAAA") "1.1" "AA") " " " ") (store (store (__array_store_all__ (Array String type String type) "") "" "AAAAAAAAAA") "1.1" "1.1")))))))))
(define-fun attribute ((BOUND_VARIABLE_73477 Node) (BOUND_VARIABLE_73478 String type)) String type "")
(define-fun attrsNode ((BOUND_VARIABLE_73481 Node)) (Array String type String type) (__array_store_all__ (Array String type String type) ""))
(define-fun n0 () Node @uc_Node_0)
(define-fun n1 () Node @uc_Node_1)
(define-fun n2 () Node @uc_Node_2)
(define-fun n3 () Node @uc_Node_3)
(define-fun n4 () Node @uc_Node_4)
(define-fun n5 () Node @uc_Node_5)
(define-fun n6 () Node @uc_Node_6)
(define-fun n7 () Node @uc_Node_7)
)
()
