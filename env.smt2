
(declare-datatypes ((unit unit)))

(define-sorts ((int BitVec[32])))
(declare-datatypes ((num
  (NReal (real Real))
  NNaN
  (NInfty (infty-positive Bool)) ; true for +oo, false for -oo
)))

(declare-datatypes ((string
  (mk-string (length int) (beg BitVec[128]))
)))

(define-sorts ((heaplabel Int)))

(declare-datatypes ((err
  ErrExpectedBool
  ErrExpectedNumber
  ErrExpectedString
  ErrExpectedPrim
  ErrExpectedRef
)))

(declare-datatypes ((jsNumber	; M
  (VInt (i int))		; I
  (VNum (n num))		; N
)))
(declare-datatypes ((jsPrim	; P
  VUndefined	   		; U
  VNull				; L
  (VBool (b Bool))		; B
  (VNumber (m jsNumber))	; M
  (VString (s string))		; S
)))
(declare-datatypes ((jsVal	; V
  (VPrim (p jsPrim))		; P
  (VRef (r heaplabel))		; O
)))
(declare-datatypes ((jsRVal	; R
  (RVal (val jsVal))		; V
  (RErr (e err))		; E
)))

(define (iZero) bv0[32])
(define (iOne) bv1[32])

(define (nZero) (NReal 0.0))
(define (nOne) (NReal 1.0))
(define (nNaN) NNaN)
(define (nInfinity) (NInfty true))
(define (nMInfinity) (NInfty false))

(define (|str:|) (mk-string bv0[32] |bvstr:|[128]))
(define (|str:true|) (mk-string bv4[32] |bvstr:true|[128]))
(define (|str:false|) (mk-string bv5[32] |bvstr:false|[128]))
(define (|str:0|) (mk-string bv1[32] |bvstr:0|[128]))
(define (|str:1|) (mk-string bv1[32] |bvstr:1|[128]))
(define (|str:NaN|) (mk-string bv3[32] |bvstr:NaN|[128]))
(define (|str:Infinity|) (mk-string bv8[32] |bvstr:Infinity|[128]))
(define (|str:-Infinity|) (mk-string bv9[32] |bvstr:-Infinity|[128]))
(define (|str:undefined|) (mk-string bv9[32] |bvstr:undefined|[128]))
(define (|str:null|) (mk-string bv4[32] |bvstr:null|[128]))
(define (|str:boolean|) (mk-string bv7[32] |bvstr:boolean|[128]))
(define (|str:number|) (mk-string bv6[32] |bvstr:number|[128]))
(define (|str:string|) (mk-string bv6[32] |bvstr:string|[128]))
(define (|str:object|) (mk-string bv6[32] |bvstr:object|[128]))
(define (|str:function|) (mk-string bv8[32] |bvstr:function|[128]))
(define (|str:code|) (mk-string bv4[32] |bvstr:code|[128]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; functions xxx~XY have type X -> Y
; functions xxx~XYZ have type X * Y -> Z
;
; for all xxx~IX, there must a xxx~NX and vice versa
; (idem for xxx~IXY, xxx~XIY)
;
; functions xxx~RR are deduced from xxx~VR
; in the following way:
; (define (xxx~RR (r jsRVal))
;   (ite (is_RErr r) r (xxx~VR (val r)))
; )
;
; functions xxx~RRR are deduced from xxx~VVR
; in the following way:
; (define (xxx~RRR (r1 jsRVal) (r2 jsRVal))
;   (ite (is_RErr r1) r1
;   (ite (is_RErr r2) r2
;   (xxx~VVR (val r1) (val r2))
; )))
;
; functions xxx~XR are deduced from xxx~XV
; in the following way:
; (define (xxx~XR (x X))
;   (RVal (xxx~XV x))
; )
;
; functions xxx~VR are deduced from xxx~PR (if there is no xxx~OR)
; in the following way:
; (define (xxx~VR (v jsVal))
;   (ite (is_VPrim v) (xxx~PR (p v))
;   (RErr ErrExpectedPrim)
; ))
;
; functions xxx~MX are deduced from xxx~IX and xxx~NX
; in the following way:
; (define (xxx~MX (v jsNumber))
;   (ite (is_VInt v) (xxx~IX (i v))
;     (xxx~NX (n v))
; ))
;
; xxx~PX are deduced from xxx~UX, xxx~LX, xxx~BX, xxx~MX, xxx~SX (if they all exist)
; (not done for binary functions)
; xxx~PR are deduced from one of xxx~UR, xxx~LR, xxx~BR, xxx~MR, xxx~SR (if only one exists)
; (done for binary functions too)
;
; and so on...
;
; however, functions used here must be defined here even if they could have been deduced
;
; there are two phases of deductions
; - 1. deduce.X<Y : from a type to a lower type
; - 2. deduce.X>Y : from a type to a higher type 
; (I, N < M ; U, L, B, M, S < P ; P, O < V < R)
; X, Y, Z are reserved for type variables
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(macro (deduce.IX<MX mx v) (mx (VInt v)))
(macro (deduce.NX<MX mx v) (mx (VNum v)))
(macro (deduce.BX<PX px v) (px (VBool v)))
(macro (deduce.MX<PX px v) (px (VNumber v)))
(macro (deduce.SX<PX px v) (px (VString v)))
(macro (deduce.PX<VX vx v) (vx (VPrim v)))
(macro (deduce.OX<VX vx v) (vx (VRef v)))
(macro (deduce.VX<RX vx v) (vx (RVal v)))

(macro (deduce.IXY<MXY* mxy v w) (mxy (VInt v) w))
(macro (deduce.NXY<MXY* mxy v w) (mxy (VNum v) w))
(macro (deduce.BXY<PXY* pxy v w) (pxy (VBool v) w))
(macro (deduce.MXY<PXY* pxy v w) (pxy (VNumber v) w))
(macro (deduce.SXY<PXY* pxy v w) (pxy (VString v) w))
(macro (deduce.PXY<VXY* vxy v w) (vxy (VPrim v) w))
(macro (deduce.OXY<VXY* vxy v w) (vxy (VRef v) w))
(macro (deduce.VXY<RXY* rxy v w) (rxy (RVal v) w))
(macro (deduce.XIY<XMY xmy v w) (xmy v (VInt w)))
(macro (deduce.XNY<XMY xmy v w) (xmy v (VNum w)))
(macro (deduce.XBY<XPY xpy v w) (xpy v (VBool w)))
(macro (deduce.XMY<XPY xpy v w) (xpy v (VNumber w)))
(macro (deduce.XSY<XPY xpy v w) (xpy v (VString w)))
(macro (deduce.XPY<XVY xvy v w) (xvy v (VPrim w)))
(macro (deduce.XOY<XVY xvy v w) (xvy v (VRef w)))
(macro (deduce.XVY<XRY xry v w) (xry v (RVal w)))


(macro (deduce.MX>IX+NX* ix nx v) (ite (is_VInt v) (ix (i v)) (nx (n v))))
(macro (deduce.PX>UX+LX+BX+MX+SX* ux lx bx mx sx v)
  (ite (is_VUndefined v) (ux unit)
  (ite (is_VNull v) (lx unit)
  (ite (is_VBool v) (bx (b v))
  (ite (is_VNumber v) (mx (m v))
  (sx (s v))
)))))
(macro (deduce.PR>BR-UR-LR-MR-SR* br v) (ite (is_VBool v) (br (b v)) (RErr ErrExpectedBool)))
(macro (deduce.PR>MR-UR-LR-BR-SR* mr v) (ite (is_VNumber v) (mr (m v)) (RErr ErrExpectedNumber)))
(macro (deduce.PR>SR-UR-LR-BR-MR* sr v) (ite (is_VString v) (sr (s v)) (RErr ErrExpectedString)))
(macro (deduce.VX>PX+OX* px ox v) (ite (is_VPrim v) (px (p v)) (ox (r v))))
(macro (deduce.VR>PR-OR* pr v) (ite (is_VPrim v) (pr (p v)) (RErr ErrExpectedPrim)))
(macro (deduce.VR>OR-PR* o_r v) (ite (is_VRef v) (o_r (r v)) (RErr ErrExpectedRef)))
(macro (deduce.RR>VR* vr v) (ite (is_RErr v) v (vr (val v))))
(macro (deduce.XM>XI xi v) (VInt (xi v)))
(macro (deduce.XM>XN xn v) (VNum (xn v)))
(macro (deduce.XP>XB xb v) (VBool (xb v)))
(macro (deduce.XP>XM xm v) (VNumber (xm v)))
(macro (deduce.XP>XS xs v) (VString (xs v)))
(macro (deduce.XV>XP xp v) (VPrim (xp v)))
(macro (deduce.XV>XO xo v) (VRef (xo v)))
(macro (deduce.XR>XV xv v) (RVal (xv v)))

(macro (deduce.MXY>IXY+NXY** ixy nxy v w) (ite (is_VInt v) (ixy (i v) w) (nxy (n v) w)))
(macro (deduce.XMY>XIY+XNY*** xiy xny v w) (ite (is_VInt w) (xiy v (i w)) (xny v (n w))))
(macro (deduce.MMX>IIX+INX+NIX+NNX* iix inx nix nnx v w)
  (ite (and (is_VInt v) (is_VInt w)) (iix (i v) (i w))
  (ite (and (is_VInt v) (is_VNum w)) (inx (i v) (n w))
  (ite (and (is_VNum v) (is_VInt w)) (nix (n v) (i w))
  (nnx (n v) (n w))
))))
(macro (deduce.PXR>MXR-UXR-LXR-BXR-SXR** mxr v w) (ite (is_VNumber v) (mxr (m v) w) (RErr ErrExpectedNumber)))
(macro (deduce.PXR>SXR-UXR-LXR-BXR-MXR** sxr v w) (ite (is_VString v) (sxr (s v) w) (RErr ErrExpectedString)))
(macro (deduce.VXR>PXR-OXR** pxr v w) (ite (is_VPrim v) (pxr (p v) w) (RErr ErrExpectedPrim)))
(macro (deduce.RXR>VXR** vxr v w) (ite (is_RErr v) v (vxr (val v) w)))
(macro (deduce.XPR>XMR-XUR-XLR-XBR-XSR* xmr v w) (ite (is_VNumber w) (xmr v (m w)) (RErr ErrExpectedNumber)))
(macro (deduce.XPR>XSR-XUR-XLR-XBR-XMR* xsr v w) (ite (is_VString w) (xsr v (s w)) (RErr ErrExpectedString)))
(macro (deduce.XVR>XPR-XOR* xpr v w) (ite (is_VPrim w) (xpr v (p w)) (RErr ErrExpectedPrim)))
(macro (deduce.XRR>XVR* xvr v w) (ite (is_RErr w) w (xvr v (val w))))
; add more deduction rules if you need them
(macro (deduce.XYM>XYI xyi v w) (VInt (xyi v w)))
(macro (deduce.XYM>XYN xyn v w) (VNum (xyn v w)))
(macro (deduce.XYP>XYB xyb v w) (VBool (xyb v w)))
(macro (deduce.XYP>XYM xym v w) (VNumber (xym v w)))
(macro (deduce.XYP>XYS xys v w) (VString (xys v w)))
(macro (deduce.XYV>XYP xyp v w) (VPrim (xyp v w)))
(macro (deduce.XYR>XYV xyv v w) (RVal (xyv v w)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Misc
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (bool_neg~BB (b Bool)) (not b))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Conversions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (prim->bool~BB (b Bool)) b)
(define (prim->bool~IB (i int)) (<> i iZero))
(define (prim->bool~NB (n num)) (and (<> n nZero) (<> n nNaN)))
(define (prim->bool~MB (v jsNumber))
  (ite (is_VInt v) (prim->bool~IB (i v))
  (prim->bool~NB (n v)) ; num
))
(define (prim->bool~SB (s string)) (<> s |str:|))
(define (prim->bool~OB (r heaplabel)) true)
(define (prim->bool~PB (v jsPrim))
  (ite (is_VBool v) (b v)
  (ite (is_VNumber v) (prim->bool~MB (m v))
  (ite (is_VString v) (prim->bool~SB (s v))
  false ; undef, null
))))
(define (val->bool~BB (b Bool)) (prim->bool~BB b))
(define (val->bool~IB (i int)) (prim->bool~IB i))
(define (val->bool~NB (n num)) (prim->bool~NB n))
(define (val->bool~MB (v jsNumber)) (prim->bool~MB v))
(define (val->bool~SB (s string)) (prim->bool~SB s))
(define (val->bool~OB (r heaplabel)) (prim->bool~OB r))
(define (val->bool~VB (v jsVal))
  (=> (is_VPrim v) (prim->bool~PB (p v)))
)
(define (val->bool~RB (r jsRVal))
  (or (is_RErr r) (val->bool~VB (val r)))
)
(define (not-val->bool~UB (x unit)) true)
(define (not-val->bool~LB (x unit)) true)
(define (not-val->bool~BB (b Bool)) (not b))
(define (not-val->bool~IB (i int)) (= i iZero))
(define (not-val->bool~NB (n num)) (or (= n nZero) (= n nNaN)))
(define (not-val->bool~SB (s string)) (= s |str:|))
(define (not-val->bool~OB (r heaplabel)) false)
(define (not-val->bool~RB (r jsRVal))
  (or (is_RErr r) (not (val->bool~VB (val r))))
)


(define (num-to-int (n num))
  (ite (or (= n nZero) (is_NInfty n) (= n nNaN)) iZero
  (ite (= n nOne) iOne
  (int2bv[32] (real2int (real n)))
)))
(define (num->int32~II (i int)) i)
(define (num->int32~NI (n num)) (num-to-int n))


(define (int-to-num (i int))
  (ite (= i iZero) nZero
  (ite (= i iOne) nOne
  (NReal (to_real (bv2int[Int] i)))
)))


; to num here means to number (int or num)
(define (prim->num~UN (x unit)) nNaN)
(define (prim->num~LI (x unit)) iZero)
(define (prim->num~BI (b Bool)) (ite b iOne iZero))
(define (prim->num~II (i int)) i)
(define (prim->num~NN (n num)) n)
(define (prim->num~MM (v jsNumber)) v)
(declare-fun uninterpreted-str->num~SM (string) jsNumber)
(define (prim->num~SM (s string))
  (ite (or (= s |str:|) (= s |str:0|)) (VInt iZero)
  (ite (= s |str:1|) (VInt iOne)
  (ite (= s |str:Infinity|) (VNum nInfinity)
  (ite (= s |str:-Infinity|) (VNum nMInfinity)
  (ite (= s |str:NaN|) (VNum nNaN)
  (uninterpreted-str->num~SM s)
))))))


(define (prim->str~US (x unit)) |str:undefined|)
(define (prim->str~LS (x unit)) |str:null|)
(define (prim->str~BS (b Bool)) (ite b |str:true| |str:false|))
(declare-fun uninterpreted-int->str~IS (int) string)
(define (prim->str~IS (i int))
  (ite (= i iZero) |str:0|
  (ite (= i iOne) |str:1|
  (uninterpreted-int->str~IS i)
)))
(declare-fun uninterpreted-num->str~NS (num) string)
(define (prim->str~NS (n num))
  (ite (= n nZero) |str:0|
  (ite (= n nOne) |str:1|
  (ite (= n nNaN) |str:NaN|
  (ite (= n nInfinity) |str:Infinity|
  (ite (= n nMInfinity) |str:-Infinity|
  (uninterpreted-num->str~NS n)
))))))
(define (prim->str~SS (s string)) s)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Arithmetic
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; TODO: check for overflows on Int operations (in such cases, cast to Num)
; if done, change type flags in xDelta
; TODO: do not approximate floats by reals

; works only for NInfty and NReal, returns true if the number > 0
(define (is-positive (n num)) (ite (is_NInfty n) (infty-positive n) (> (real n) 0.0)))


(define (+~III (i1 int) (i2 int)) (bvadd i1 i2))
(define (+~NNN (n1 num) (n2 num))
  (ite (and (is_NReal n1) (is_NReal n2)) (NReal (+ (real n1) (real n2)))
  (ite (or (is_NNaN n1) (is_NNaN n2)) NNaN
  (ite (is_NInfty n1) (ite (or (is_NReal n2) (= n1 n2)) n1 NNaN) n2)
)))
(define (+~INN (i1 int) (n2 num)) (+~NNN (int-to-num i1) n2))
(define (+~NIN (n1 num) (i2 int)) (+~NNN n1 (int-to-num i2)))

(define (-~III (i1 int) (i2 int)) (bvsub i1 i2))
(define (-~NNN (n1 num) (n2 num))
  (ite (and (is_NReal n1) (is_NReal n2)) (NReal (- (real n1) (real n2)))
  (ite (or (is_NNaN n1) (is_NNaN n2)) NNaN
  (ite (is_NInfty n1) (ite (= n1 n2) NNaN n1) n2)
)))
(define (-~INN (i1 int) (n2 num)) (-~NNN (int-to-num i1) n2))
(define (-~NIN (n1 num) (i2 int)) (-~NNN n1 (int-to-num i2)))

(define (*~III (i1 int) (i2 int)) (bvmul i1 i2))
(define (*~NNN (n1 num) (n2 num))
  (ite (and (is_NReal n1) (is_NReal n2)) (NReal (* (real n1) (real n2)))
  (ite (or (is_NNaN n1) (is_NNaN n2)) NNaN
  (ite (or (and (is_NInfty n1) (= n2 nZero)) (and (is_NInfty n2) (= n1 nZero))) NNaN
  (NInfty (= (is-positive n1) (is-positive n2)))
))))
(define (*~NIN (n1 num) (i2 int)) (*~NNN n1 (int-to-num i2)))
(define (*~INN (i1 int) (n2 num)) (*~NNN (int-to-num i1) n2))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Comparison
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define (eq~INB (i int) (n num))
  (or (and (= i iZero) (= n nZero))
      (and (= i iOne) (= n nOne))
      (= n (int-to-num i))
))
(define (eq~NNB (n1 num) (n2 num)) (and (= n1 n2) (<> n1 nNaN) (<> n2 nNaN)))
(define (eq~IMB (i1 int) (v jsNumber)) (ite (is_VInt v) (= i1 (i v)) (eq~INB i1 (n v))))
(define (eq~MMB (v1 jsNumber) (v2 jsNumber))
  (ite (is_VInt v1)
    (ite (is_VInt v2) (= v1 v2) (eq~INB (i v1) (n v2)))
    (ite (is_VInt v2) (eq~INB (i v2) (n v1)) (eq~NNB (n v1) (n v2)))
))

(define (stx=~BBB (b1 Bool) (b2 Bool)) (= b1 b2))
(define (stx=~IIB (i1 int) (i2 int)) (= i1 i2))
(define (stx=~NNB (n1 num) (n2 num)) (eq~NNB n1 n2))
(define (stx=~SSB (s1 string) (s2 string)) (= s1 s2))
(define (stx=~INB (i int) (n num)) (eq~INB i n))
(define (stx=~NIB (n num) (i int)) (eq~INB i n))
(define (stx=~NNB (n1 num) (n2 num)) (eq~NNB n1 n2))
(define (stx=~MMB (v1 jsNumber) (v2 jsNumber)) (eq~MMB v1 v2))
(define (stx=~PPB (v1 jsPrim) (v2 jsPrim))
  (ite (and (is_VNumber v1) (is_VNumber v2)) (stx=~MMB (m v1) (m v2))
  (= v1 v2)
))
(define (stx=~VVB (v1 jsVal) (v2 jsVal))
  (ite (and (is_VPrim v1) (is_VPrim v2)) (stx=~PPB (p v1) (p v2))
  (= v1 v2)
))


(define (abs=~BIB (b Bool) (i int)) (= i (ite b iOne iZero)))
(define (abs=~BNB (b Bool) (n num)) (= n (ite b nOne nZero)))
(define (abs=~BMB (b Bool) (v jsNumber))
  (ite (is_VInt v) (abs=~BIB b (i v)) (abs=~BNB b (n v)))
)
(define (abs=~BSB (b Bool) (s string)) (eq~IMB (ite b iOne iZero) (prim->num~SM s)))
(define (abs=~IBB (i int) (b Bool)) (abs=~BIB b i))
(define (abs=~INB (i int) (n num)) (eq~INB i n))
(declare-fun uninterpreted-abs=~ISB (int string) Bool)
(define (abs=~ISB (i int) (s string))
  (or (and (= i iZero) (or (= s |str:|) (= s |str:0|)))
      (and (= i iOne) (= s |str:1|))
      (uninterpreted-abs=~ISB i s)
))
(define (abs=~NBB (n num) (b Bool)) (abs=~BNB b n))
(define (abs=~NIB (n num) (i int)) (abs=~INB i n))
(define (abs=~NNB (n1 num) (n2 num)) (eq~NNB n1 n2))
(declare-fun uninterpreted-abs=~NSB (num string) Bool)
(define (abs=~NSB (n num) (s string))
  (or (and (= n nZero) (or (= s |str:|) (= s |str:0|)))
      (and (= n nOne) (= s |str:1|))
      (and (= n nInfinity) (= s |str:Infinity|))
      (and (= n nNaN) (= s |str:NaN|))
      (uninterpreted-abs=~NSB n s)
))
(define (abs=~MBB (v jsNumber) (b Bool)) (abs=~BMB b v))
(define (abs=~MMB (v1 jsNumber) (v2 jsNumber)) (eq~MMB v1 v2))
(define (abs=~MSB (v jsNumber) (s string))
  (ite (is_VInt v) (abs=~ISB (i v) s) (abs=~NSB (n v) s))
)
(define (abs=~SBB (s string) (b Bool)) (abs=~BSB b s))
(define (abs=~SIB (s string) (i int)) (abs=~ISB i s))
(define (abs=~SNB (s string) (n num)) (abs=~NSB n s))
(define (abs=~SMB (s string) (v jsNumber)) (abs=~MSB v s))
(define (abs=~PPB (v1 jsPrim) (v2 jsPrim))
  (ite (and (is_VNumber v1) (is_VNumber v2)) (abs=~MMB (m v1) (m v2))
    (or (= v1 v2)
        (and (is_VNull v1) (is_VUndefined v2))
        (and (is_VUndefined v1) (is_VNull v2))
        (ite (and (is_VBool v1) (is_VNumber v2)) (abs=~BMB (b v1) (m v2))
	(ite (and (is_VBool v1) (is_VString v2)) (abs=~BSB (b v1) (s v2))
        (ite (and (is_VNumber v1) (is_VBool v2)) (abs=~MBB (m v1) (b v2))
        (ite (and (is_VNumber v1) (is_VString v2)) (abs=~MSB (m v1) (s v2))
	(ite (and (is_VString v1) (is_VBool v2)) (abs=~SBB (s v1) (b v2))
        (ite (and (is_VString v1) (is_VNumber v2)) (abs=~SMB (s v1) (m v2))
        false
)))))))))
(define (abs=~VVB (v1 jsVal) (v2 jsVal))
  (ite (and (is_VPrim v1) (is_VPrim v2)) (abs=~PPB (p v1) (p v2))
  (= v1 v2)
))


; Arithmetic comparisons

(define (<~IIB (i1 int) (i2 int)) (bvslt i1 i2))
(define (<~NNB (n1 num) (n2 num))
  (ite (and (is_NReal n1) (is_NReal n2)) (< (real n1) (real n2))
  (and (<> n1 nNaN nInfinity) (<> n2 nNaN nMInfinity))
))
(define (<~INB (i1 int) (n2 num)) (<~NNB (int-to-num i1) n2))
(define (<~NIB (n1 num) (i2 int)) (<~NNB n1 (int-to-num i2)))

(define (<=~IIB (i1 int) (i2 int)) (bvsle i1 i2))
(define (<=~NNB (n1 num) (n2 num))
  (ite (and (is_NReal n1) (is_NReal n2)) (<= (real n1) (real n2))
  (and (<> n1 nNaN) (<> n2 nNaN) (or (<> n1 nInfinity) (<> n2 nMInfinity)))
))
(define (<=~INB (i1 int) (n2 num)) (<=~NNB (int-to-num i1) n2))
(define (<=~NIB (n1 num) (i2 int)) (<=~NNB n1 (int-to-num i2)))

(define (>~IIB (i1 int) (i2 int)) (bvsgt i1 i2))
(define (>~NNB (n1 num) (n2 num))
  (ite (and (is_NReal n1) (is_NReal n2)) (> (real n1) (real n2))
  (and (<> n1 nNaN nMInfinity) (<> n2 nNaN nInfinity))
))
(define (>~INB (i1 int) (n2 num)) (>~NNB (int-to-num i1) n2))
(define (>~NIB (n1 num) (i2 int)) (>~NNB n1 (int-to-num i2)))

(define (>=~IIB (i1 int) (i2 int)) (bvsge i1 i2))
(define (>=~NNB (n1 num) (n2 num))
  (ite (and (is_NReal n1) (is_NReal n2)) (>= (real n1) (real n2))
  (and (<> n1 nNaN) (<> n2 nNaN) (or (<> n1 nMInfinity) (<> n2 nInfinity)))
))
(define (>=~INB (i1 int) (n2 num)) (>=~NNB (int-to-num i1) n2))
(define (>=~NIB (n1 num) (i2 int)) (>=~NNB n1 (int-to-num i2)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Objects
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(declare-fun has-attr (heaplabel string) Bool)

(define (is-function (r heaplabel)) (has-attr r |str:code|))
(define (is-callable~VB (v jsVal))
  (ite (is_VRef v) (is-function (r v))
  false
))


(declare-fun uninterpreted-get-field (heaplabel string) jsVal)
(define (get-field~OSV (r heaplabel) (s string)) (uninterpreted-get-field r s))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (primitive?~PB (v jsPrim)) true)
(define (primitive?~OB (r heaplabel)) false)
(define (primitive?~VB (v jsVal)) (is_VPrim v))


(define (typeof~US (x unit)) |str:undefined|)
(define (typeof~LS (x unit)) |str:null|)
(define (typeof~BS (b Bool)) |str:boolean|)
(define (typeof~MS (i int)) |str:number|)
(define (typeof~SS (s string)) |str:string|)
(define (typeof~OS (r heaplabel)) |str:object|)

(define (surface-typeof~US (x unit)) |str:undefined|)
(define (surface-typeof~LS (x unit)) |str:null|)
(define (surface-typeof~BS (b Bool)) |str:boolean|)
(define (surface-typeof~MS (i int)) |str:number|)
(define (surface-typeof~SS (s string)) |str:string|)
(define (surface-typeof~OS (l heaplabel)) (ite (is-function l) |str:function| |str:object|))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;  Strings
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (string+~SSS (s1 string) (s2 string))
  (mk-string (bvadd (length s1) (length s2))
             (bvor (beg s1) (bvshl (beg s2) (zero_ext[96] (bvshl (length s1) bv3[32]))))
))
