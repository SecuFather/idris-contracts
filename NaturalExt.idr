module NaturalExt

import Common
import Natural

%default total

public export
record Sub (x, y : N) where
    constructor MkSub

public export
(-) : (x, y : N) -> Sub x y
(-) x y = MkSub

namespace Sub
  public export
  (==) : (z : N) -> {x, y : N} -> (s : Sub x y) -> Type
  (==) z xy = y + z = x

public export
record Lte (x, y : N) where
    constructor MkLte

public export
(<=) : (x, y : N) -> Lte x y
(<=) x y = MkLte

namespace Lte
  public export
  (==) : (z : N) -> {x, y : N} -> (s : Lte x y) -> Type
  (==) z xy = x + z = y

public export
record Div (x, y : N) where
    constructor MkDiv

public export
(/) : (x, y : N) -> Div x y
(/) x y = MkDiv

namespace Div
  public export
  (==) : (abc : (N, N, N)) -> {x, y : N} -> (d : Div x y) -> Type
  (==) (a, b, c) xy = (x = a * y + b, y = b + S c)

export
tu1m : {x1 : N} -> S Z * x1 = x1
tu1m = t1s2m ..> x1Ap tz1m ..> t1zp

export
t1um : {x1 : N} -> x1 * S Z = x1
t1um = c21m ..> tu1m

export
t12umm : {x1, x2 : N} -> x1 * (x2 * S Z) = x1 * x2
t12umm = x1Am t1um

export
t1u2mp : {x1, x2 : N} -> x1 + (S Z * x2) = x1 + x2
t1u2mp = x1Ap tu1m

export
t1um2p : {x1, x2 : N} -> (x1 * S Z) + x2 = x1 + x2
t1um2p = xA1p t1um

export
t1z2mp : {x1, x2 : N} -> x1 + (Z * x2) = x1
t1z2mp = x1Ap tz1m ..> t1zp

export
t12ump : {x1, x2 : N} -> x1 + (x2 * S Z) = x1 + x2
t12ump = x1Ap t1um

export
t12ump3m : {x1, x2, x3 : N} -> (x1 + (x2 * S Z)) * x3 = (x1 + x2) * x3
t12ump3m = xA1m t12ump

export
tz1m2p : {x1, x2 : N} -> (Z * x1) + x2 = x2
tz1m2p = xA1p tz1m ..> tz1p

export
tz1m2p3m : {x1, x2, x3 : N} -> ((Z * x1) + x2) * x3 = x2 * x3
tz1m2p3m = xA1m tz1m2p

export
xABp : {a1, a2, b1, b2 : N} -> a1 = a2 -> b1 = b2 -> a1 + b1 = a2 + b2
xABp p1 p2 = xA1p p1 ..> x1Ap p2

export
c21m43mp : {x1, x2, x3, x4 : N} -> (x1 * x2) + (x3 * x4) = (x2 * x1) + (x4 * x3)
c21m43mp = xABp c21m c21m

export
t1um2m : {x1, x2 : N} -> (x1 * S Z) * x2 = x1 * x2
t1um2m = xA1m t1um

export
c13m2m : {x1, x2, x3 : N} -> (x1 * x2) * x3 = (x1 * x3) * x2
c13m2m = aM ..> x1Am c21m .!> aM

export
c21m3m : {x1, x2, x3 : N} -> (x1 * x2) * x3 = (x2 * x1) * x3
c21m3m = xA1m c21m

export
c23m1m : {x1, x2, x3 : N} -> (x1 * x2) * x3 = (x2 * x3) * x1
c23m1m = c21m3m ..> c13m2m

export
c31m2m : {x1, x2, x3 : N} -> (x1 * x2) * x3 = (x3 * x1) * x2
c31m2m = c13m2m ..> c21m3m

export
c32m1m : {x1, x2, x3 : N} -> (x1 * x2) * x3 = (x3 * x2) * x1
c32m1m = aM ..> x1Am c21m ..> c21m

export
c13m2mA : {x1, x2, x3 : N} -> x1 * (x2 * x3) = x1 * (x3 * x2)
c13m2mA = aM !.> c13m2m ..> aM

export
c21m3mA : {x1, x2, x3 : N} -> x1 * (x2 * x3) = x2 * (x1 * x3)
c21m3mA = aM !.> c21m3m ..> aM

export
c23m1mA : {x1, x2, x3 : N} -> x1 * (x2 * x3) = x2 * (x3 * x1)
c23m1mA = aM !.> c23m1m ..> aM

export
c31m2mA : {x1, x2, x3 : N} -> x1 * (x2 * x3) = x3 * (x1 * x2)
c31m2mA = aM !.> c31m2m ..> aM

export
c32m1mA : {x1, x2, x3 : N} -> x1 * (x2 * x3) = x3 * (x2 * x1)
c32m1mA = aM !.> c32m1m ..> aM

export
t123pm : {x1, x2, x3 : N} -> x1 * (x2 + x3) = x1 * x2 + x1 * x3
t123pm = c21m ..> t12p3m ..> c21m43mp

export
v1sAm : {x1, a1, a2 : N} -> S x1 * a1 = S x1 * a2 -> a1 = a2
v1sAm prf = vA1sm $ c21m ..> prf ..> c21m

export
v1sAmBm : {x1, a1, a2, b1, b2 : N} -> (S x1 * a1) * b1 = (S x1 * a2) * b2 -> a1 * b1 = a2 * b2
v1sAmBm prf = v1sAm $ aM !.> prf ..> aM

export
c321mm : {x1, x2, x3 : N} -> x1 * (x2 * x3) = x3 * (x2 * x1)
c321mm = c21m ..> xA1m c21m ..> aM

export
c321mm4p : {x1, x2, x3, x4 : N} -> x1 * (x2 * x3) + x4 = x3 * (x2 * x1) + x4
c321mm4p = xA1p c321mm

export
vAB1smm : {x1, a1, a2, b1, b2 : N} -> a1 * (b1 * S x1) = a2 * (b2 * S x1) -> a1 * b1 = a2 * b2
vAB1smm prf = vA1sm $ aM ..> prf .!> aM

export
xABm : {a1, a2, b1, b2 : N} -> a1 = a2 -> b1 = b2 -> a1 * b1 = a2 * b2
xABm p1 p2 = x1Am p2 ..> xA1m p1

export
t123p4mp : {x1, x2, x3, x4 : N} -> x1 + ((x2 + x3) * x4) = x1 + (x2 * x4 + x3 * x4)
t123p4mp = x1Ap t12p3m

export
t12p3m4p : {x1, x2, x3, x4 : N} -> ((x1 + x2) * x3) + x4 = (x1 * x3 + x2 * x3) + x4
t12p3m4p = xA1p t12p3m

export
c312pp : {x1, x2, x3 : N} -> x1 + (x2 + x3) = x3 + (x1 + x2)
c312pp = aP !.> c21p

export
c13p2p : {x1, x2, x3 : N} -> (x1 + x2) + x3 = (x1 + x3) + x2
c13p2p = aP ..> x1Ap c21p .!>aP

export
c31p2p : {x1, x2, x3 : N} -> (x1 + x2) + x3 = (x3 + x1) + x2
c31p2p = aP ..> c312pp .!> aP

export
xA1pBp : {x1, a1, a2, b1, b2 : N} -> a1 + b1 = a2 + b2 -> (a1 + x1) + b1 = (a2 + x1) + b2
xA1pBp prf = c13p2p ..> xA1p prf ..> c13p2p

export
xA1Bpp : {x1, a1, a2, b1, b2 : N} -> a1 + b1 = a2 + b2 -> a1 + (x1 + b1) = a2 + (x1 + b2)
xA1Bpp prf = c213pp ..> x1Ap prf ..> c213pp

export
xABCpp : {a1, a2, b1, b2, c1, c2 : N} -> a1 = a2 -> b1 = b2 -> c1 = c2 -> a1 + (b1 + c1) = a2 + (b2 + c2)
xABCpp p1 p2 p3 = xA1p p1 ..> x1Ap (xABp p2 p3)

export
c21p3p : {x1, x2, x3 : N} -> (x1 + x2) + x3 = (x2 + x1) + x3
c21p3p = xA1p c21p

export
vA1p : {x1, a1, a2 : N} -> a1 + x1 = a2 + x1 -> a1 = a2
vA1p prf = v1Ap $ c21p ..> prf ..> c21p

export
c23p1p : {x1, x2, x3 : N} -> (x1 + x2) + x3 = (x2 + x3) + x1
c23p1p = aP ..> c21p

export
c32p1p : {x1, x2, x3 : N} -> (x1 + x2) + x3 = (x3 + x2) + x1
c32p1p = aP ..> c21p ..> xA1p c21p

export
c143pp2p : {x1, x2, x3, x4 : N} -> (x1 + (x2 + x3)) + x4 = (x1 + (x4 + x3)) + x2
c143pp2p = c32p1p ..> xA1p c213pp ..> c32p1p

export
c231pp : {x1, x2, x3 : N} -> x1 + (x2 + x3) = x2 + (x3 + x1)
c231pp = c21p ..> aP

export
c213mm : {x1, x2, x3 : N} -> x1 * (x2 * x3) = x2 * (x1 * x3)
c213mm = aM !.> xA1m c21m ..> aM

export
tz1m2m : {x1, x2 : N} -> (Z * x1) * x2 = Z
tz1m2m = aM ..> tz1m

export
c13m24mm : {x1, x2, x3, x4 : N} -> (x1 * x2) * (x3 * x4) = (x1 * x3) * (x2 * x4)
c13m24mm = aM ..> x1Am c213mm .!> aM

export
c231mm : {x1, x2, x3 : N} -> x1 * (x2 * x3) = x2 * (x3 * x1)
c231mm = c21m ..> aM

export
c43m21mm : {x1, x2, x3, x4 : N} -> (x1 * x2) * (x3 * x4) = (x4 * x3) * (x2 * x1)
c43m21mm = xABm c21m c21m ..> c21m

export
c32m14mm : {x1, x2, x3, x4 : N} -> (x1 * x2) * (x3 * x4) = (x3 * x2) * (x1 * x4)
c32m14mm = c13m24mm ..> c21m3m ..> c13m24mm

export
c13p24pp : {x1, x2, x3, x4 : N} -> (x1 + x2) + (x3 + x4) = (x1 + x3) + (x2 + x4)
c13p24pp = aP ..> x1Ap c213pp .!> aP

export
c43p2p1p : {x1, x2, x3, x4 : N} -> ((x1 + x2) + x3) + x4 = ((x4 + x3) + x2) + x1

export
xA1d : {x1, x2, x3 : N} -> x1 = x2 -> div x1 x3 = div x2 x3
xA1d Refl = Refl

export
x1Ad : {x1, x2, x3 : N} -> x1 = x2 -> div x3 x1 = div x3 x2
x1Ad Refl = Refl

export
t12p3d : {x1, x2, x3 : N} -> (x1 + x2) `div` x3 = (x1 `div` x3 + x2 `div` x3) + (x1 `mod` x3 + x2 `mod` x3) `div` x3 
t12p3d = xA1d (xABp t12d2sm t12d2sm !.> (c13p24pp .!> x1Ap t12p3m)) ..> t123smp3d ..> c21p

export
t12sm2d : {x1, x2 : N} -> x1 * S x2 `div` x2 = x1
t12sm2d = v1Ap $ xA1p tz1d ..> tz1p ..> xA1d (tz1p !!> xA1p tz1m) ..> t123smp3d