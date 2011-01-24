
(define-sorts ((int BitVec[32])))
(define-sorts ((num Real))) ; todo +/-infty, +/-0, nan

(declare-datatypes ((string
  (mk-string (length int) (beg BitVec[128]))
)))

(declare-datatypes ((err
  ErrExpectedBool
  ErrExpectedNum
  ErrExpectedString
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

(define-fun iZero () int bv0[32])
(define-fun iOne () int bv1[32])

(define-fun nZero () num 0.0)
(define-fun nOne () num 1.0)
(declare-fun nNaN () num)
(declare-fun nInfinity () num)
(assert (distinct nZero nOne nNaN nInfinity))

(define-fun |str:| () string (mk-string bv0[32] |bvstr:|[128]))
(define-fun |str:true| () string (mk-string bv4[32] |bvstr:true|[128]))
(define-fun |str:false| () string (mk-string bv5[32] |bvstr:false|[128]))
(define-fun |str:0| () string (mk-string bv1[32] |bvstr:0|[128]))
(define-fun |str:1| () string (mk-string bv1[32] |bvstr:1|[128]))
(define-fun |str:NaN| () string (mk-string bv3[32] |bvstr:NaN|[128]))
(define-fun |str:Infinity| () string (mk-string bv8[32] |bvstr:Infinity|[128]))
(define-fun |str:undefined| () string (mk-string bv9[32] |bvstr:undefined|[128]))
(define-fun |str:null| () string (mk-string bv4[32] |bvstr:null|[128]))
(define-fun |str:boolean| () string (mk-string bv7[32] |bvstr:boolean|[128]))
(define-fun |str:number| () string (mk-string bv6[32] |bvstr:number|[128]))
(define-fun |str:string| () string (mk-string bv6[32] |bvstr:string|[128]))
(define-fun str-ERROR () string (mk-string (bvsub bv0[32] bv1[32]) (bvsub bv0[128] bv1[128])))

(define (primitive? (v jsVal)) (VBool true))
(define (is-callable (v jsVal)) (VBool false))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Conversions
;;  x-to-y are of type x -> y
;;    if x is prim, its type is jsVal
;;  x->y are of type jsVal -> jsVal
;;    if x is not prim, x is assuming to be is_Vx
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (int-to-bool (i int)) (not (= i iZero)))
(define (num-to-bool (n num)) (not (or (= n nZero) (= n nNaN))))
(define (str-to-bool (s string)) (not (= s |str:|)))
(declare-fun err-to-bool (err) Bool)
(define (prim-to-bool (v jsVal))
  (and (not (is_VUndefined v)) (not (is_VNull v))
  (ite (is_VBool v) (b v)
  (ite (is_VInt v) (int-to-bool v)
  (ite (is_VNum v) (num-to-bool v)
  (ite (is_VString v) (str-to-bool v)
  (err-to-bool v)
))))))
(define (int->bool (v jsVal)) (VBool (int-to-bool (i v))))
(define (num->bool (v jsVal)) (VBool (num-to-bool (n v))))
(define (str->bool (v jsVal)) (VBool (str-to-bool (s v))))
(define (err->bool (v jsVal)) (VBool (err-to-bool (e v))))
(define (prim->bool (v jsVal)) (VBool (prim-to-bool v)))
(define (ValToBool (v jsVal))
  (and (not (is_VUndefined v)) (not (is_VNull v))
  (ite (is_VBool v) (b v)
  (ite (is_VInt v) (int-to-bool (i v))
  (ite (is_VNum v) (num-to-bool (n v))
  (ite (is_VString v) (str-to-bool (s v))
  (err-to-bool (e v))
))))))


(define (num-to-int (n number)) (int2bv[32] (real2int n)))
(define (num->int32 (v jsVal)) (VInt (num-to-int (n v))))
(define (number->int32 (v jsVal))
  (ite (is_VInt v) v
  (ite (is_VNum v) (num->int32 v)
  ErrExpectedNum
)))
(define (to-int32 (v jsVal)) (number->int32 v))


(define (bool-to-num (b Bool)) (ite b nOne nZero))
(define (int-to-num (i int))
  (ite (= i iZero) nZero
  (ite (= i iOne) nOne
  (to_real (bv2int[Int] i))
)))
(declare-fun uninterpreted-str-to-num (string) num)
(define (str-to-num (s string))
  (ite (or (= s |str:|) (= s |str:0|)) nZero
  (ite (= s |str:1|) nOne
  (uninterpreted-str-to-num s)
)))
(define (prim-to-num (v jsVal))
  (ite (is_VBool v) (bool-to-num (b v))
  (ite (is_VInt v) (int-to-num (i v))
  (ite (is_VNum v) (n v)
  (ite (is_VString v) (str-to-num (s v))
  (ite (is_VUndefined v) nNaN
  (ite (is_VNull v) nZero
  nZero
)))))))
(define (bool->num (v jsVal)) (VNum (bool-to-num (b v))))
(define (int->num (v jsVal)) (VNum (int-to-num (i v))))
(define (str->num (v jsVal)) (VNum (str-to-num (s v))))
(define (prim->num (v jsVal)) (VNum (prim-to-num v)))


(define (bool-to-str (b Bool)) (ite b |str:true| |str:false|))
(declare-fun uninterpreted-int-to-str (int) string)
(define (int-to-str (i int))
  (ite (= i iZero) |str:0|
  (ite (= i iOne) |str:1|
  (uninterpreted-int-to-str i)
)))
(declare-fun uninterpreted-num-to-str (num) string)
(define (num-to-str (n num))
  (ite (= n nZero) |str:0|
  (ite (= n nOne) |str:1|
  (ite (= n nNaN) |str:NaN|
  (ite (= n nInfinity) |str:Infinity|
  (uninterpreted-num-to-str n)
)))))
(define (prim-to-str (v jsVal))
  (ite (is_VNull v) |str:null|
  (ite (is_VUndefined v) |str:undefined|
  (ite (is_VBool v) (bool-to-str (b v))
  (ite (is_VInt v) (int-to-str (i v))
  (ite (is_VNum v) (num-to-str (n v))
  (ite (is_VString v) (s v)
  str-ERROR
)))))))
(define (bool->str (v jsVal)) (VString (bool-to-str (b v))))
(define (int->str (v jsVal)) (VString (int-to-str (i v))))
(define (num->str (v jsVal)) (VString (num-to-str (n v))))
(define (prim->str (v jsVal)) (VString (prim-to-str v)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (js+ (n1 jsVal) (n2 jsVal))
  (ite (and (is_VInt n1) (is_VInt n2))
    (VInt (bvadd (i n1) (i n2)))
  (ite (and (is_VNum n1) (is_VNum n2))
    (VNum (+ (n n1) (n n2)))
  (ite (and (is_VInt n1) (is_VNum n2))
    (VNum (+ (int-to-num (i n1)) (n n2)))
  (ite (and (is_VNum n1) (is_VInt n2))
    (VNum (+ (n n1) (int-to-num (i n2))))
  (VErr ErrExpectedNum)
)))))

(define (js- (n1 jsVal) (n2 jsVal))
  (ite (and (is_VInt n1) (is_VInt n2))
    (VInt (bvsub (i n1) (i n2)))
  (ite (and (is_VNum n1) (is_VNum n2))
    (VNum (- (n n1) (n n2)))
  (ite (and (is_VInt n1) (is_VNum n2))
    (VNum (- (int-to-num (i n1)) (n n2)))
  (ite (and (is_VNum n1) (is_VInt n2))
    (VNum (- (n n1) (int-to-num (i n2))))
  (VErr ErrExpectedNum)
)))))

(define (stx-eq (v1 jsVal) (v2 jsVal))
  (or (= v1 v2)
      (ite (and (is_VNum v1) (is_VInt v2))
         (= (n v1) (int-to-num (i v2)))
      (and (is_VInt v1) (is_VNum v2)
         (= (int-to-num (i v1)) (n v2)))
)))
(define (stx= (v1 jsVal) (v2 jsVal)) (VBool (stx-eq v1 v2)))

(define (abs-eq-bool-int (b Bool) (i int))
  (or (and (not b) (= i iZero))
      (and b (= i iOne))
))
(define (abs-eq-bool-num (b Bool) (n num))
  (or (and (not b) (= n nZero))
      (and b (= n nOne))
))
(define (abs-eq-int-num (i int) (n num))
  (or (and (= i iZero) (= n nZero))
      (and (= i iOne) (= n nOne))
      (= n (int-to-num i))
))
(declare-fun uninterpreted-abs-eq-int-str (int string) Bool)
(define (abs-eq-int-str (i int) (s string))
  (or (and (= i iZero) (or (= s |str:|) (= s |str:0|)))
      (and (= i iOne) (= s |str:1|))
      (uninterpreted-abs-eq-int-str i s)
))
(declare-fun uninterpreted-abs-eq-num-str (num string) Bool)
(define (abs-eq-num-str (n num) (s string))
  (or (and (= n nZero) (or (= s |str:|) (= s |str:0|)))
      (and (= n nOne) (= s |str:1|))
      (and (= n nInfinity) (= s |str:Infinity|))
      (and (= n nNaN) (= s |str:NaN|))
      (uninterpreted-abs-eq-num-str n s)
))
(define (abs-eq (v1 jsVal) (v2 jsVal))
  (or (stx-eq v1 v2)
      (and (is_VNull v1) (is_VUndefined v2))
      (and (is_VUndefined v1) (is_VNull v2))
      (ite (and (is_VString v1) (is_VNum v2))
        (abs-eq-num-str (n v2) (s v1))
      (ite (and (is_VNum v1) (is_VString v2))
        (abs-eq-num-str (n v1) (s v2))
      (ite (and (is_VString v1) (is_VInt v2))
        (abs-eq-int-str (i v2) (s v1))
      (ite (and (is_VInt v1) (is_VString v2))
        (abs-eq-int-str (i v1) (s v2))
      (ite (and (is_VNum v1) (is_VBool v2))
        (abs-eq-bool-num (b v2) (n v1))
      (ite (and (is_VBool v1) (is_VNum v2))
        (abs-eq-bool-num (b v1) (n v2))
      (ite (and (is_VInt v1) (is_VBool v2))
        (abs-eq-bool-int (b v2) (i v1))
      (ite (and (is_VBool v1) (is_VInt v2))
        (abs-eq-bool-int (b v1) (i v2))
      (ite (and (is_VNum v1) (is_VInt v2))
        (abs-eq-int-num (i v2) (n v1))
      (ite (and (is_VInt v1) (is_VNum v2))
        (abs-eq-int-num (i v1) (n v2))
      false
))))))))))))
(define (abs= (v1 jsVal) (v2 jsVal)) (VBool (abs-eq v1 v2)))

(define (typeof (v jsVal))
  (ite (is_VUndefined v) (VString |str:undefined|)
  (ite (is_VNull v) (VString |str:null|)
  (ite (is_VBool v) (VString |str:boolean|)
  (ite (is_VString v) (VString |str:string|)
  (ite (or (is_VNum v) (is_VInt v)) (VString |str:number|)
  (VErr (e v))
))))))
(define (surface-typeof (v jsVal)) (typeof v))

(define (string-concat (s1 string) (s2 string))
  (mk-string (bvadd (length s1) (length s2))
             (bvor (beg s1) (bvshl (beg s2) (zero_ext[96] (bvshl (length s1) bv3[32]))))
))

(define (string+ (v1 jsVal) (v2 jsVal))
  (ite (and (is_VString v1) (is_VString v2))
    (VString (string-concat (s v1) (s v2)))
  (VErr ErrExpectedString)
))

(define (get-field (v1 jsVal) (v2 jsVal))
  (ite (is_VString v2)
    VUndefined
  (VErr ErrExpectedString)
))
