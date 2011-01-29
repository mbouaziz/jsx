
(define-sorts ((int BitVec[32])))
(define-sorts ((num Real))) ; todo +/-infty, +/-0, nan

(declare-datatypes ((string
  (mk-string (length int) (beg BitVec[128]))
)))

(define-sorts ((heaplabel Int)))

(declare-datatypes ((err
  ErrExpectedBool
  ErrExpectedNum
  ErrExpectedString
  ErrExpectedPrim
  ErrExpectedRef
)))

(declare-datatypes ((jsVal
  VUndefined
  VNull
  (VBool (b Bool))
  (VInt (i int))
  (VNum (n num))
  (VString (s string))
  (VRef (r heaplabel))
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
(define-fun |str:object| () string (mk-string bv6[32] |bvstr:object|[128]))
(define-fun |str:function| () string (mk-string bv8[32] |bvstr:function|[128]))
(define-fun |str:code| () string (mk-string bv4[32] |bvstr:code|[128]))
(define-fun str-ERROR () string (mk-string (bvsub bv0[32] bv1[32]) (bvsub bv0[128] bv1[128])))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Misc
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (bool_neg-bool->bool (b Bool)) (not b))
(define (bool_neg (v jsVal))
  (ite (is_VBool v) (VBool (bool_neg-bool->bool (b v)))
  (VErr ErrExpectedBool)
))

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
(define (ref-to-bool (r heaplabel)) true)
(declare-fun err-to-bool (err) Bool)
(define (prim-to-bool (v jsVal))
  (and (not (is_VUndefined v)) (not (is_VNull v))
  (ite (is_VBool v) (b v)
  (ite (is_VInt v) (int-to-bool (i v))
  (ite (is_VNum v) (num-to-bool (n v))
  (ite (is_VString v) (str-to-bool (s v))
  (ite (is_VRef v) (ref-to-bool (r v))
  (err-to-bool (e v))
)))))))
(define (int->bool (v jsVal)) (VBool (int-to-bool (i v))))
(define (num->bool (v jsVal)) (VBool (num-to-bool (n v))))
(define (str->bool (v jsVal)) (VBool (str-to-bool (s v))))
(define (prim->bool (v jsVal))
  (ite (or (is_VUndefined v) (is_VNull v)) (VBool false)
  (ite (is_VBool v) v
  (ite (is_VInt v) (int->bool v)
  (ite (is_VNum v) (num->bool v)
  (ite (is_VString v) (str->bool v)
  (VErr ErrExpectedPrim)
))))))
(define (ValToBool (v jsVal))
  (and (not (is_VUndefined v)) (not (is_VNull v))
  (ite (is_VBool v) (b v)
  (ite (is_VInt v) (int-to-bool (i v))
  (ite (is_VNum v) (num-to-bool (n v))
  (ite (is_VString v) (str-to-bool (s v))
  (is_VRef v)
))))))
(define (NotValToBool (v jsVal))
  (or (is_VUndefined v) (is_VNull v)
  (ite (is_VBool v) (not (b v))
  (ite (is_VInt v) (not (int-to-bool (i v)))
  (ite (is_VNum v) (not (num-to-bool (n v)))
  (ite (is_VString v) (not (str-to-bool (s v)))
  false
))))))


(define (num-to-int (n number)) (int2bv[32] (real2int n)))
(define (num->int32 (v jsVal)) (VInt (num-to-int (n v))))
(define (number->int32 (v jsVal))
  (ite (is_VInt v) v
  (ite (is_VNum v) (num->int32 v)
  (ite (is_VErr v) v
  (VErr ErrExpectedNum)
))))
(define (to-int32 (v jsVal)) (number->int32 v))


(define (int-to-num (i int))
  (ite (= i iZero) nZero
  (ite (= i iOne) nOne
  (to_real (bv2int[Int] i))
)))


; to num here means to number (int or num)
(define (bool-to-num (b Bool)) (VInt (ite b iOne iZero)))
(declare-fun uninterpreted-str-to-num (string) num)
(define (str-to-num (s string))
  (ite (or (= s |str:|) (= s |str:0|)) (VInt iZero)
  (ite (= s |str:1|) (VInt iOne)
  (VNum (uninterpreted-str-to-num s))
)))
(define (prim->num (v jsVal))
  (ite (is_VBool v) (bool-to-num (b v))
  (ite (is_VInt v) v
  (ite (is_VNum v) v
  (ite (is_VString v) (str-to-num (s v))
  (ite (is_VUndefined v) (VNum nNaN)
  (ite (is_VNull v) (VInt iZero)
  (ite (is_VRef v) (VErr ErrExpectedPrim)
  v ; VErr gives the same VErr
))))))))
(define (bool->num (v jsVal)) (bool-to-num (b v)))
(define (int->num (v jsVal)) (int-to-num (i v)))
(define (str->num (v jsVal)) (str-to-num (s v)))


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
(define (prim->str (v jsVal))
  (ite (is_VNull v) (VString |str:null|)
  (ite (is_VUndefined v) (VString |str:undefined|)
  (ite (is_VBool v) (bool->str v)
  (ite (is_VInt v) (int->str v)
  (ite (is_VNum v) (num->str v)
  (ite (is_VString v) v
  (ite (is_VRef v) (VErr ErrExpectedPrim)
  v ; VErr
))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Arithmetic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: check for overflows on Int operations (in such cases, cast to Num)
; if done, change type flags in xDelta

(define (js+ (v1 jsVal) (v2 jsVal))
  (ite (and (is_VInt v1) (is_VInt v2)) (VInt (bvadd (i v1) (i v2)))
  (ite (and (is_VNum v1) (is_VNum v2)) (VNum (+ (n v1) (n v2)))
  (ite (and (is_VInt v1) (is_VNum v2)) (VNum (+ (int-to-num (i v1)) (n v2)))
  (ite (and (is_VNum v1) (is_VInt v2)) (VNum (+ (n v1) (int-to-num (i v2))))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VErr ErrExpectedNum)
)))))))


(define (js- (v1 jsVal) (v2 jsVal))
  (ite (and (is_VInt v1) (is_VInt v2)) (VInt (bvsub (i v1) (i v2)))
  (ite (and (is_VNum v1) (is_VNum v2)) (VNum (- (n v1) (n v2)))
  (ite (and (is_VInt v1) (is_VNum v2)) (VNum (- (int-to-num (i v1)) (n v2)))
  (ite (and (is_VNum v1) (is_VInt v2)) (VNum (- (n v1) (int-to-num (i v2))))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VErr ErrExpectedNum)
)))))))


(define (js* (v1 jsVal) (v2 jsVal))
  (ite (and (is_VInt v1) (is_VInt v2)) (VInt (bvmul (i v1) (i v2)))
  (ite (and (is_VNum v1) (is_VNum v2)) (VNum (* (n v1) (n v2)))
  (ite (and (is_VInt v1) (is_VNum v2)) (VNum (* (int-to-num (i v1)) (n v2)))
  (ite (and (is_VNum v1) (is_VInt v2)) (VNum (* (n v1) (int-to-num (i v2))))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VErr ErrExpectedNum)
)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Comparison
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (smt= (v1 jsVal) (v2 jsVal)) (VBool (= v1 v2)))

(define (stx-eq (v1 jsVal) (v2 jsVal))
  (or (= v1 v2)
      (ite (and (is_VNum v1) (is_VInt v2))
         (= (n v1) (int-to-num (i v2)))
      (and (is_VInt v1) (is_VNum v2)
         (= (int-to-num (i v1)) (n v2)))
)))
(define (stx= (v1 jsVal) (v2 jsVal))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VBool (stx-eq v1 v2))
)))


(define (abs-eq-bool-int (b Bool) (i int))
  (or (and (not b) (= i iZero)) (and b (= i iOne)))
)
(define (abs-eq-bool-num (b Bool) (n num))
  (or (and (not b) (= n nZero)) (and b (= n nOne)))
)
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
      (ite (and (is_VString v1) (is_VNum v2)) (abs-eq-num-str (n v2) (s v1))
      (ite (and (is_VNum v1) (is_VString v2)) (abs-eq-num-str (n v1) (s v2))
      (ite (and (is_VString v1) (is_VInt v2)) (abs-eq-int-str (i v2) (s v1))
      (ite (and (is_VInt v1) (is_VString v2)) (abs-eq-int-str (i v1) (s v2))
      (ite (and (is_VNum v1) (is_VBool v2)) (abs-eq-bool-num (b v2) (n v1))
      (ite (and (is_VBool v1) (is_VNum v2)) (abs-eq-bool-num (b v1) (n v2))
      (ite (and (is_VInt v1) (is_VBool v2)) (abs-eq-bool-int (b v2) (i v1))
      (ite (and (is_VBool v1) (is_VInt v2)) (abs-eq-bool-int (b v1) (i v2))
      (ite (and (is_VNum v1) (is_VInt v2)) (abs-eq-int-num (i v2) (n v1))
      (ite (and (is_VInt v1) (is_VNum v2)) (abs-eq-int-num (i v1) (n v2))
      false
))))))))))))
(define (abs= (v1 jsVal) (v2 jsVal))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VBool (abs-eq v1 v2))
)))


; Arithmetic comparisons

(define (js< (v1 jsVal) (v2 jsVal))
  (ite (and (is_VInt v1) (is_VInt v2)) (VBool (bvslt (i v1) (i v2)))
  (ite (and (is_VNum v1) (is_VNum v2)) (VBool (< (n v1) (n v2)))
  (ite (and (is_VInt v1) (is_VNum v2)) (VBool (< (int-to-num (i v1)) (n v2)))
  (ite (and (is_VNum v1) (is_VInt v2)) (VBool (< (n v1) (int-to-num (i v2))))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VErr ErrExpectedNum)
)))))))

(define (js<= (v1 jsVal) (v2 jsVal))
  (ite (and (is_VInt v1) (is_VInt v2)) (VBool (bvsle (i v1) (i v2)))
  (ite (and (is_VNum v1) (is_VNum v2)) (VBool (<= (n v1) (n v2)))
  (ite (and (is_VInt v1) (is_VNum v2)) (VBool (<= (int-to-num (i v1)) (n v2)))
  (ite (and (is_VNum v1) (is_VInt v2)) (VBool (<= (n v1) (int-to-num (i v2))))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VErr ErrExpectedNum)
)))))))

(define (js> (v1 jsVal) (v2 jsVal))
  (ite (and (is_VInt v1) (is_VInt v2)) (VBool (bvsgt (i v1) (i v2)))
  (ite (and (is_VNum v1) (is_VNum v2)) (VBool (> (n v1) (n v2)))
  (ite (and (is_VInt v1) (is_VNum v2)) (VBool (> (int-to-num (i v1)) (n v2)))
  (ite (and (is_VNum v1) (is_VInt v2)) (VBool (> (n v1) (int-to-num (i v2))))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VErr ErrExpectedNum)
)))))))

(define (js>= (v1 jsVal) (v2 jsVal))
  (ite (and (is_VInt v1) (is_VInt v2)) (VBool (bvsge (i v1) (i v2)))
  (ite (and (is_VNum v1) (is_VNum v2)) (VBool (>= (n v1) (n v2)))
  (ite (and (is_VInt v1) (is_VNum v2)) (VBool (>= (int-to-num (i v1)) (n v2)))
  (ite (and (is_VNum v1) (is_VInt v2)) (VBool (>= (n v1) (int-to-num (i v2))))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VErr ErrExpectedNum)
)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Objects
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun has-attr (heaplabel string) Bool)

(define (is-function (r heaplabel)) (has-attr r |str:code|))
(define (ref-is-callable (v jsVal)) (VBool (is-function (r v))))
(define (is-callable (v jsVal))
  (ite (is_VErr v) v
  (ite (is_VRef v) (ref-is-callabel v)
  (VBool false)
)))


(declare-fun uninterpreted-get-field (heaplabel string) jsVal)
(define (ref-str-get-field (v1 jsVal) (v2 jsVal))
  (uninterpreted-get-field (r v1) (s v2))
)
(define (get-field (v1 jsVal) (v2 jsVal))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (ite (is_VRef v1)
    (ite (is_VString v2)
      (ref-str-get-field v1 v2)
    (VErr ErrExpectedString)
    )
  (VErr ErrExpectedRef)
))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (primitive? (v jsVal))
  (ite (is_VErr v) v
  (VBool (not (is_VRef v)))
))


(define (typeof (v jsVal))
  (ite (is_VUndefined v) (VString |str:undefined|)
  (ite (is_VNull v) (VString |str:null|)
  (ite (is_VBool v) (VString |str:boolean|)
  (ite (is_VString v) (VString |str:string|)
  (ite (or (is_VNum v) (is_VInt v)) (VString |str:number|)
  (ite (is_VRef v) (VString |str:object|)
  v ; VErr
)))))))
(define (ref-surface-typeof (v jsVal)) (VString (ite (is-function (r v)) |str:function| |str:object|)))
(define (surface-typeof (v jsVal))
  (ite (is_VUndefined v) (VString |str:undefined|)
  (ite (is_VNull v) (VString |str:null|)
  (ite (is_VBool v) (VString |str:boolean|)
  (ite (is_VString v) (VString |str:string|)
  (ite (or (is_VNum v) (is_VInt v)) (VString |str:number|)
  (ite (is_VRef v) (ref-surface-typeof v)
  v ; VErr
)))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Strings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (string-concat (s1 string) (s2 string))
  (mk-string (bvadd (length s1) (length s2))
             (bvor (beg s1) (bvshl (beg s2) (zero_ext[96] (bvshl (length s1) bv3[32]))))
))
(define (string+ (v1 jsVal) (v2 jsVal))
  (ite (and (is_VString v1) (is_VString v2))
    (VString (string-concat (s v1) (s v2)))
  (ite (is_VErr v1) v1
  (ite (is_VErr v2) v2
  (VErr ErrExpectedString)
))))
