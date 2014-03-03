<?xml version="1.0" encoding="UTF-8"?>
<a>
    <a/>
    <a/>
    <a/>
    <a/>
    <a/>
    <a/>
    <a/>
    <a/>
    <a/>
    <a/>
    <t0 class="content body 1.0 1.3 1.2" id="n0">
        <t1 class="body"/>
        <t2 class="body 1.2 2.2"/>
        <a class="body" id="n3">
            <t4 class="body"/>
        </a>
    </t0>
</a>

Algorithm
1. Every condition inside a if or for would generate 1 assert statement.
2. To deal with typing
    number to boolean   => (not (= n 0))?true:false
    string to boolean   => (not (= s ""))?true:false
    null   to boolean   => false
    undefined to boolean => false
3. To deal with OR, AND
   (a || b) => (or  a b)    _OR(a, b)
   (a && b) => (and a b)    _AND(a, b)
4. To deal with comparators
   (a == b)     => (= a b)
   (a === b)    => (= a b)
   (a != b)     => (not (= a b))
   (a > b)      => (> a b)
   ... etc.
5. To deal with getters
    document.getElementById(id)
    _CALLGET(document, "getElementById", id)
        (declare-const n_k Node);
        (assert (= (id n_k) id));
    element.getElementsByTagName(tagName)[i]
    _GET(_CALLGET(element, "getElementsByTagName", tagName), i)
        (declare-const n_j Node);
        (assert (and (ancestor n_k, n_j) (= (tag n_j) (str.++ sessionID tagName)));
        // optional, if element is n_k instead of document
    element.getElementsByClassName(className)[i]
    _GET(_CALLGET(element, "getElementsByClassName", className), i)
        (declare-const n_j Node);
        (assert (hasClass className n_j));
        (assert (descendant n_j n_k)); // optional, if element is n_k instead of not document
    document.createElement(tagName);
    _CALLGET(document, "createElement", tagName);
        (declare-const n_j Node);
        (assert (= (tag n_j) (str.++ sessionID tagName)));
6. To deal with DOM accessors:
    element.parentElement 
    _GET(element, "parentElement");
        (declare-const n_j Node);
        (parent n_j n_k); assume element is n_k
    element.children[i]
    _GET(_GET(element, children), i)
        (declare-const n_j Node);
        (and (= (position n_j) i) (parentElement n_k n_j))
7. To deal with DOM chains
    element.parentElement.nextElementSibling
    _GET(_GET(element, "parentElement"), "nextElementSibling");
        (declare-const n_a Node); assume node.parent already has an alias (e.g. n_j) in SMT2.
        (nextElementSibling n_a n_j);
8. CSS selectors
    Zen coding
