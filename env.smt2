
(define-sorts ((char_array (Array Int Int))))
(define-sorts ((int BitVec[32])))
(define-sorts ((num Real)))

(declare-datatypes ((string
  (mk-string (length Int) (at char_array))
)))

(declare-datatypes ((err
  ErrExpectedBool
)))

(declare-datatypes ((jsVal
  VUndefined
  VNull
  (VBool (b Bool))
  (VInt (i int))
  (VNum (n num))
  (VString (s string))
  (VErr (e err))
)))

(declare-fun iZero () int)
(assert (= iZero bv0[32]))
;(define-fun iZero () int bv0[32])
;(define-fun nZero () num Real[0])

;(define-fun VErrToBool ((e err)) Bool false)
(declare-fun VErrToBool (err) Bool)
(assert (forall ((e err)) (= (VErrToBool e) false)))

;(define-fun ValToBool ((v jsVal)) Bool
;  (and (not (or (is_VUndefined v) (is_VNull v)))
;  (ite (is_VBool v) (b v)
;  (ite (is_VInt v) (not (= (i v) iZero))
;  (ite (is_VNum v) (not (= (n v) nZero))
;  (ite (is_VString v) (not (= (length (s v)) Int[0]))
;  (VErrToBool (e v))
;))))))
(declare-fun ValToBool (jsVal) Bool)
(assert (forall ((v jsVal)) (= (ValToBool v) (and (not (or (is_VUndefined v) (is_VNull v)))
  (ite (is_VBool v) (b v)
  (ite (is_VInt v) (not (= (i v) iZero))
  (VErrToBool (e v))))))))

(declare-fun primitive? (jsVal) jsVal)
(assert (forall ((v jsVal)) (= (primitive? v) (VBool true))))
;(define-fun primitive? ((v jsVal)) jsVal (VBool true))


;(declare-fun A () jsVal)  
;(assert (not (ValToBool (primitive? A))))
