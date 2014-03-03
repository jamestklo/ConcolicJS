unsupported
sat
(model
(define-fun sessionID () String type "sessionID_")
; cardinality of Node is 6
(declare-sort Node 0)
; rep: @uc_Node_0
; rep: @uc_Node_1
; rep: @uc_Node_2
; rep: @uc_Node_3
; rep: @uc_Node_4
; rep: @uc_Node_5
(define-fun root (($x1 Node)) Bool (= @uc_Node_5 $x1))
(define-fun leaf (($x1 Node)) Bool (ite (= @uc_Node_0 $x1) false (ite (= @uc_Node_3 $x1) false (not (= @uc_Node_5 $x1)))))
(define-fun parentElement (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_4 $x2) false (not (= @uc_Node_5 $x2)))) (ite (= @uc_Node_3 $x1) (= @uc_Node_4 $x2) (ite (= @uc_Node_5 $x1) (= @uc_Node_0 $x2) false))))
(define-fun position ((_ufmt_1 Node)) Int (ite (= @uc_Node_0 _ufmt_1) 11 (ite (= @uc_Node_1 _ufmt_1) 1 (ite (= @uc_Node_3 _ufmt_1) 3 (ite (= @uc_Node_4 _ufmt_1) 1 (ite (= @uc_Node_5 _ufmt_1) 0 2))))))
(define-fun length ((_ufmt_1 Node)) Int (ite (= @uc_Node_1 _ufmt_1) 0 (ite (= @uc_Node_2 _ufmt_1) 0 (ite (= @uc_Node_3 _ufmt_1) 1 (ite (= @uc_Node_4 _ufmt_1) 0 (ite (= @uc_Node_5 _ufmt_1) 11 3))))))
(define-fun following-sibling (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_2 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_2 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (not (= @uc_Node_5 $x2)))))) (ite (= @uc_Node_3 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (not (= @uc_Node_5 $x2))))) false)))
(define-fun preceding-sibling (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) false (ite (= @uc_Node_1 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_1 $x2) false (ite (= @uc_Node_2 $x2) true (ite (= @uc_Node_3 $x2) true (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (ite (= @uc_Node_2 $x2) true (= @uc_Node_3 $x2)))))))) (ite (= @uc_Node_2 $x1) (= @uc_Node_3 $x2) (ite (= @uc_Node_3 $x1) false (ite (= @uc_Node_4 $x1) false (ite (= @uc_Node_5 $x1) false (ite (= @uc_Node_2 $x2) true (= @uc_Node_3 $x2)))))))))
(define-fun descendant (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) (= @uc_Node_5 $x2) (ite (= @uc_Node_1 $x1) (ite (= @uc_Node_0 $x2) true (ite (= @uc_Node_1 $x2) false (ite (= @uc_Node_2 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) true (ite (= @uc_Node_0 $x2) true (= @uc_Node_5 $x2)))))))) (ite (= @uc_Node_2 $x1) (ite (= @uc_Node_0 $x2) true (= @uc_Node_5 $x2)) (ite (= @uc_Node_3 $x1) (ite (= @uc_Node_0 $x2) true (= @uc_Node_5 $x2)) (ite (= @uc_Node_4 $x1) (ite (= @uc_Node_0 $x2) true (ite (= @uc_Node_3 $x2) true (= @uc_Node_5 $x2))) (ite (= @uc_Node_5 $x1) false (ite (= @uc_Node_0 $x2) true (= @uc_Node_5 $x2)))))))))
(define-fun ancestor (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) (ite (= @uc_Node_0 $x2) false (not (= @uc_Node_5 $x2))) (ite (= @uc_Node_3 $x1) (= @uc_Node_4 $x2) (ite (= @uc_Node_5 $x1) (not (= @uc_Node_5 $x2)) false))))
(define-fun firstElementChild (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) false (ite (= @uc_Node_1 $x1) (ite (= @uc_Node_0 $x2) true (ite (= @uc_Node_1 $x2) false (ite (= @uc_Node_2 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (= @uc_Node_0 $x2))))))) (ite (= @uc_Node_2 $x1) false (ite (= @uc_Node_3 $x1) false (ite (= @uc_Node_4 $x1) (= @uc_Node_3 $x2) (ite (= @uc_Node_5 $x1) false (= @uc_Node_0 $x2))))))))
(define-fun lastElementChild (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) (= @uc_Node_5 $x2) (ite (= @uc_Node_3 $x1) (= @uc_Node_0 $x2) (ite (= @uc_Node_4 $x1) (= @uc_Node_3 $x2) false))))
(define-fun nextElementSibling (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_2 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_2 $x2) false (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (not (= @uc_Node_5 $x2)))))) (ite (= @uc_Node_3 $x1) (= @uc_Node_2 $x2) false)))
(define-fun previousElementSibling (($x1 Node) ($x2 Node)) Bool (ite (= @uc_Node_0 $x1) false (ite (= @uc_Node_1 $x1) (ite (= @uc_Node_0 $x2) false (ite (= @uc_Node_1 $x2) false (ite (= @uc_Node_2 $x2) true (ite (= @uc_Node_3 $x2) false (ite (= @uc_Node_4 $x2) false (ite (= @uc_Node_5 $x2) false (= @uc_Node_2 $x2))))))) (ite (= @uc_Node_2 $x1) (= @uc_Node_3 $x2) (ite (= @uc_Node_3 $x1) false (ite (= @uc_Node_4 $x1) false (ite (= @uc_Node_5 $x1) false (= @uc_Node_2 $x2))))))))
(define-fun id ((_ufmt_1 Node)) String type (ite (= @uc_Node_0 _ufmt_1) "sessionID_n0" (ite (= @uc_Node_1 _ufmt_1) "AAAAAAAAA" (ite (= @uc_Node_2 _ufmt_1) "AAAAAAAA" (ite (= @uc_Node_3 _ufmt_1) "sessionID_n3" (ite (= @uc_Node_4 _ufmt_1) "AAAAAAA" "AAAAAAAAAAAAAAAAA"))))))
(define-fun tag ((_ufmt_1 Node)) String type (ite (= @uc_Node_0 _ufmt_1) "sessionID_t0" (ite (= @uc_Node_1 _ufmt_1) "sessionID_t1" (ite (= @uc_Node_2 _ufmt_1) "sessionID_t2" (ite (= @uc_Node_3 _ufmt_1) "AAAAAAAAAAA" (ite (= @uc_Node_4 _ufmt_1) "sessionID_t4" "AAAAAAAAAAAAAAAA"))))))
(define-fun parentAlias (($x1 Node)) Node (ite (= @uc_Node_0 $x1) @uc_Node_5 (ite (= @uc_Node_4 $x1) @uc_Node_3 (ite (= @uc_Node_5 $x1) @uc_Node_1 @uc_Node_0))))
(define-fun attribute ((_ufmt_1 Node)) (Array String type String type) (ite (= @uc_Node_1 _ufmt_1) (store (store (__array_store_all__ (Array String type String type) "B") "" "AAAAA") "n1" " ") (ite (= @uc_Node_2 _ufmt_1) (store (store (store (__array_store_all__ (Array String type String type) "C") "" "AAAA") "sessionID_k00" "k00") "sessionID_k20" "k21") (ite (= @uc_Node_3 _ufmt_1) (store (store (store (__array_store_all__ (Array String type String type) "D") "" "AAAAAAAAAAAAAAA") "n3" " ") "n3a" " ") (ite (= @uc_Node_4 _ufmt_1) (store (store (__array_store_all__ (Array String type String type) "E") "" "AAAAAAAAAA") "n4" " ") (ite (= @uc_Node_5 _ufmt_1) (store (store (__array_store_all__ (Array String type String type) "F") "" "AAAAAAAAAAAAAA") "n5" " ") (store (store (store (store (__array_store_all__ (Array String type String type) "") "" "AAAAAA") "n0a" " ") "sessionID_k00" "v00") "sessionID_k01" "v01")))))))
(define-fun n0 () Node @uc_Node_0)
(define-fun n0a () Node @uc_Node_0)
(define-fun n1 () Node @uc_Node_1)
(define-fun n2 () Node @uc_Node_2)
(define-fun n3 () Node @uc_Node_3)
(define-fun n3a () Node @uc_Node_3)
(define-fun n4 () Node @uc_Node_4)
(define-fun n5 () Node @uc_Node_5)
(define-fun v00 () String type "v00")
(define-fun s0 () String type "abcv01")
(define-fun s1 () String type "v01")
)
()
