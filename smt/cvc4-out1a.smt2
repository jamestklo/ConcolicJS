unsupported
unknown
(model
; cardinality of Node is 7
(declare-sort Node 0)
; rep: @uc_Node_0
; rep: @uc_Node_1
; rep: @uc_Node_2
; rep: @uc_Node_3
; rep: @uc_Node_4
; rep: @uc_Node_5
; rep: @uc_Node_6
(define-fun root (($x1 Node)) Bool (ite (= @uc_Node_0 $x1) true (= @uc_Node_5 $x1)))
(define-fun leaf (($x1 Node)) Bool (ite (= @uc_Node_0 $x1) false (ite (= @uc_Node_3 $x1) false (not (= @uc_Node_5 $x1)))))
(define-fun parent (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (not (= @uc_Node_6 $x2))))) (ite (= @uc_Node_3 $x1) (= @uc_Node_4 $x2) (ite (= @uc_Node_5 $x1) (= @uc_Node_6 $x2) false))))
(define-fun position ((_ufmt_1 Node)) Int (ite (= @uc_Node_0 _ufmt_1) 0 (ite (= @uc_Node_1 _ufmt_1) 1 (ite (= @uc_Node_2 _ufmt_1) 2 (ite (= @uc_Node_4 _ufmt_1) 1 (ite (= @uc_Node_5 _ufmt_1) 0 (ite (= @uc_Node_6 _ufmt_1) 11 3)))))))
(define-fun length ((_ufmt_1 Node)) Int (ite (= @uc_Node_0 _ufmt_1) 3 (ite (= @uc_Node_1 _ufmt_1) 0 (ite (= @uc_Node_2 _ufmt_1) 0 (ite (= @uc_Node_3 _ufmt_1) 1 (ite (= @uc_Node_4 _ufmt_1) 0 (ite (= @uc_Node_6 _ufmt_1) 0 12)))))))
(define-fun following-sibling (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_2 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_2 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (not (= @uc_Node_6 $x2))))))) (ite (= @uc_Node_3 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (not (= @uc_Node_6 $x2)))))) false)))
(define-fun preceding-sibling (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) false (ite (= @uc_Node_1 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_1 $x2) false (ite (= @uc_Node_2 $x2) true (ite (= @uc_Node_3 $x2) true (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (ite (= @uc_Node_6 $x2) false (ite (= @uc_Node_2 $x2) true (= @uc_Node_3 $x2))))))))) (ite (= @uc_Node_2 $x1) (= @uc_Node_3 $x2) (ite (= @uc_Node_3 $x1) false (ite (= @uc_Node_4 $x1) false (ite (= @uc_Node_5 $x1) false (ite (= @uc_Node_6 $x1) false (ite (= @uc_Node_2 $x2) true (= @uc_Node_3 $x2))))))))))
(define-fun descendant (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) false (ite (= @uc_Node_1 $x1) (ite (= @uc_Node_0 $x2) true (ite (= @uc_Node_1 $x2) false (ite (= @uc_Node_2 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (ite (= @uc_Node_6 $x2) false (= @uc_Node_0 $x2)))))))) (ite (= @uc_Node_2 $x1) (= @uc_Node_0 $x2) (ite (= @uc_Node_3 $x1) (= @uc_Node_0 $x2) (ite (= @uc_Node_4 $x1) (ite (= @uc_Node_0 $x2) true (= @uc_Node_3 $x2)) (ite (= @uc_Node_5 $x1) false (ite (= @uc_Node_6 $x1) (= @uc_Node_5 $x2) (= @uc_Node_0 $x2)))))))))
(define-fun ancestor (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_5 $x2) false (not (= @uc_Node_6 $x2)))) (ite (= @uc_Node_3 $x1) (= @uc_Node_4 $x2) (ite (= @uc_Node_5 $x1) (= @uc_Node_6 $x2) false))))
(define-fun firstChild (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) false (ite (= @uc_Node_1 $x1) (ite (= @uc_Node_0 $x2) true (ite (= @uc_Node_1 $x2) false (ite (= @uc_Node_2 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (ite (= @uc_Node_6 $x2) false (= @uc_Node_0 $x2)))))))) (ite (= @uc_Node_2 $x1) false (ite (= @uc_Node_3 $x1) false (ite (= @uc_Node_4 $x1) (= @uc_Node_3 $x2) (ite (= @uc_Node_5 $x1) false (ite (= @uc_Node_6 $x1) false (= @uc_Node_0 $x2)))))))))
(define-fun lastChild (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_3 $x1) (= @uc_Node_0 $x2) (ite (= @uc_Node_4 $x1) (= @uc_Node_3 $x2) false)))
(define-fun nextSibling (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_2 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_2 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (not (= @uc_Node_6 $x2))))))) (ite (= @uc_Node_3 $x1) (= @uc_Node_2 $x2) false)))
(define-fun prevSibling (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) false (ite (= @uc_Node_1 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_1 $x2) false (ite (= @uc_Node_2 $x2) true (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (ite (= @uc_Node_6 $x2) false (= @uc_Node_2 $x2)))))))) (ite (= @uc_Node_2 $x1) (= @uc_Node_3 $x2) (ite (= @uc_Node_3 $x1) false (ite (= @uc_Node_4 $x1) false (ite (= @uc_Node_5 $x1) false (ite (= @uc_Node_6 $x1) false (= @uc_Node_2 $x2)))))))))
(define-fun parentNode (($x1 Node)) Node (ite (= @uc_Node_4 $x1) @uc_Node_3 (ite (= @uc_Node_6 $x1) @uc_Node_5 @uc_Node_0)))
(define-fun id (($x1 String type) ($x2 Node)) Bool (ite (= "n0" $x1) (= @uc_Node_0 $x2) (ite (= "AAAAAAAA" $x1) (= @uc_Node_6 $x2) (ite (= "AAAAAAAAA" $x1) (= @uc_Node_4 $x2) (ite (= "AAAAAAAAAA" $x1) (= @uc_Node_2 $x2) false)))))
(define-fun idStr ((_ufmt_1 Node)) String type (ite (= @uc_Node_0 _ufmt_1) "n0" (ite (= @uc_Node_1 _ufmt_1) "" (ite (= @uc_Node_3 _ufmt_1) "" (ite (= @uc_Node_4 _ufmt_1) "AAAAAAAAA" (ite (= @uc_Node_5 _ufmt_1) "" (ite (= @uc_Node_6 _ufmt_1) "AAAAAAAA" "AAAAAAAAAA")))))))
(define-fun tag (($x1 String type) ($x2 Node)) Bool (ite (= "div" $x1) (= @uc_Node_0 $x2) (ite (= "span" $x1) (not (= @uc_Node_0 $x2)) false)))
(define-fun tagName ((_ufmt_1 Node)) String type (ite (= @uc_Node_1 _ufmt_1) "span" (ite (= @uc_Node_2 _ufmt_1) "span" (ite (= @uc_Node_3 _ufmt_1) "span" (ite (= @uc_Node_4 _ufmt_1) "span" (ite (= @uc_Node_5 _ufmt_1) "span" (ite (= @uc_Node_6 _ufmt_1) "span" "div")))))))
(define-fun hasClass (($x1 String type) ($x2 Node)) Bool (ite (= "content" $x1) (= @uc_Node_0 $x2) (ite (= "body" $x1) (= @uc_Node_0 $x2) (ite (= "1.1" $x1) (= @uc_Node_0 $x2) (ite (= "1.2" $x1) (ite (= @uc_Node_0 $x2) true (= @uc_Node_2 $x2)) (ite (= "1.3" $x1) (= @uc_Node_0 $x2) false))))))
(define-fun classNode ((_ufmt_1 Node)) (Array String type String type) (ite (= @uc_Node_0 _ufmt_1) (store (store (store (store (store (store (__array_store_all__ (Array String type String type) "B") "" "AAAAA") "content" "content") "body" "body") "1.1" "1.1") "1.2" "1.2") "1.3" "1.3") (ite (= @uc_Node_1 _ufmt_1) (store (__array_store_all__ (Array String type String type) "") "" "AAAAAA") (store (store (__array_store_all__ (Array String type String type) "C") "" "A") "1.2" "1.2"))))
(define-fun hasttribute ((BOUND_VARIABLE_141264 Node) (BOUND_VARIABLE_141265 String type)) String type "")
(define-fun attributeInt ((BOUND_VARIABLE_141268 Node) (BOUND_VARIABLE_141269 String type)) Int 0)
(define-fun attributeBool ((BOUND_VARIABLE_141272 Node) (BOUND_VARIABLE_141273 String type)) Bool false)
(define-fun n0 () Node @uc_Node_0)
(define-fun n1 () Node @uc_Node_1)
(define-fun n2 () Node @uc_Node_2)
(define-fun n3 () Node @uc_Node_3)
(define-fun n4 () Node @uc_Node_4)
(define-fun n5 () Node @uc_Node_3)
(define-fun n6 () Node @uc_Node_5)
(define-fun n7 () Node @uc_Node_6)
)
()
