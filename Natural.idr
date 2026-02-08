module Natural

import Common

%default total

export
(..>) : {0 x1, x2, x3 : N} -> x1 = x2 -> x2 = x3 -> x1 = x3
(..>) Refl Refl = Refl

export
(!.>) : {0 x1, x2, x3 : N} -> x2 = x1 -> x2 = x3 -> x1 = x3
(!.>) Refl Refl = Refl

export
(.!>) : {0 x1, x2, x3 : N} -> x1 = x2 -> x3 = x2 -> x1 = x3
(.!>) Refl Refl = Refl

export
(!!>) : {0 x1, x2, x3 : N} -> x2 = x1 -> x3 = x2 -> x1 = x3
(!!>) Refl Refl = Refl

export
vAs : {a1, a2 : N} -> S a1 = S a2 -> a1 = a2
vAs Refl = Refl

export
xAs : {a1, a2 : N} -> a1 = a2 -> S a1 = S a2
xAs Refl = Refl

export
(+) : (x1, x2 : N) -> N
(+) Z x2 = x2
(+) (S x1) x2 = S (x1 + x2)

export
tz1p : Z + x1 = x1
tz1p = Refl

export
t1zp : {x1 : N} -> x1 + Z = x1
t1zp {x1 = Z} = Refl
t1zp {x1 = S x1} = xAs t1zp

export
t1s2p : S x1 + x2 = S (x1 + x2)
t1s2p = Refl

export
t12sp : {x1, x2 : N} -> x1 + S x2 = S (x1 + x2)
t12sp {x1 = Z} = Refl
t12sp {x1 = S x1} = xAs t12sp

export
c21p : {x1, x2 : N} -> x1 + x2 = x2 + x1
c21p {x2 = Z} = t1zp
c21p {x2 = S x2} = t12sp ..> xAs c21p

export
v1Ap : {x1, a1, a2 : N} -> x1 + a1 = x1 + a2 -> a1 = a2
v1Ap {x1 = Z} prf = prf
v1Ap {x1 = S x1} prf = v1Ap (vAs prf)

export
aP : {x1, x2, x3 : N} -> (x1 + x2) + x3 = x1 + (x2 + x3)
aP {x1 = Z} = Refl
aP {x1 = S x1} = xAs aP

export
xA1p : {a1, x1, a2 : N} -> a1 = a2 -> a1 + x1 = a2 + x1
xA1p Refl = Refl

export
x1Ap : {x1, a1, a2 : N} -> a1 = a2 -> x1 + a1 = x1 + a2
x1Ap Refl = Refl

export
c213pp : {x1, x2, x3 : N} -> x1 + (x2 + x3) = x2 + (x1 + x3)
c213pp = aP !.> xA1p c21p ..> aP

export
(*) : (x1, x2 : N) -> N
(*) Z x2 = Z
(*) (S x1) x2 = x2 + (x1 * x2)

export
tz1m : Z * x = Z
tz1m = Refl

export
t1zm : {x1 : N} -> x1 * Z = Z
t1zm {x1 = Z} = Refl
t1zm {x1 = S x1} = t1zm

export
t1s2m : S x1 * x2 = x2 + x1 * x2
t1s2m = Refl

export
t12sm : {x1, x2 : N} -> x1 * S x2 = x1 + x1 * x2
t12sm {x1 = Z} = Refl
t12sm {x1 = S x1} = xAs (x1Ap t12sm ..> c213pp)

export
c21m : {x1, x2 : N} -> x1 * x2 = x2 * x1
c21m {x1 = Z} = sym t1zm
c21m {x1 = S x1} = x1Ap c21m .!> t12sm

export
t1s2sm : S x1 * S x2 = S (x2 + x1 * S x2)
t1s2sm = Refl

export
t1s2sm3sm : (S x1 * S x2) * S x3 = S (x3 + ((x2 + (x1 * S x2)) * S x3))
t1s2sm3sm = Refl

export
t1s2s3smm : S x1 * (S x2 * S x3) = S ((x3 + (x2 * S x3)) + (x1 * S (x3 + (x2 * S x3))))
t1s2s3smm = Refl

export
x1Am : {x0 : N} -> x1 = x2 -> x0 * x1 = x0 * x2
x1Am Refl = Refl

export
xA1m : {x0 : N} -> x1 = x2 -> x1 * x0 = x2 * x0
xA1m Refl = Refl

export
t12p3m : {x1, x2, x3 : N} -> (x1 + x2) * x3 = x1 * x3 + x2 * x3
t12p3m {x1 = Z} = Refl
t12p3m {x1 = S x1} = x1Ap t12p3m .!> aP

export
vA1sm : {a1, a2, x1 : N} -> a1 * S x1 = a2 * S x1 -> a1 = a2
vA1sm p {a1 = Z, a2 = Z} = p
vA1sm Refl {a1 = Z, a2 = S a2} impossible
vA1sm Refl {a1 = S a1, a2 = Z} impossible
vA1sm p {a1 = S a1, a2 = S a2} = xAs $ vA1sm $ v1Ap $ vAs p

export
aM : {x1, x2, x3 : N} -> (x1 * x2) * x3 = x1 * (x2 * x3)
aM {x1 = Z} = Refl
aM {x1 = S x1} = t12p3m ..> x1Ap aM

export
div : (x, y : N) -> 