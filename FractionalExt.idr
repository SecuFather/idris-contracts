module FractionalExt

import Common
import Natural
import NaturalExt
import Fractional

%default total

public export
record Sub (x, y : F) where
    constructor MkSub

public export
(-) : (x, y : F) -> Sub x y
(-) x y = MkSub

namespace Sub
  public export
  (==) : (z : F) -> {x, y : F} -> (s : Sub x y) -> Type
  (==) z xy = y + z == x

export
xA1m : {x1, x2, x0 : F} -> x1 == x2 -> x1 * x0 == x2 * x0
xA1m p = c21m ..> x1Am p ..> c21m

export
vA1sm : {x1, x2, x0 : F} -> (sx0 : SF x0) -> x1 * x0 == x2 * x0 -> x1 == x2
vA1sm sx0 p = v1sAm sx0 (c21m ..> p ..> c21m)

export
xAf : {a1, a2 : N} -> a1 = a2 -> a1.fr == a2.fr
xAf Refl = refl

export
t1zp : {x1 : F} -> x1 + (Z).fr == x1
t1zp = c21p ..> tz1p

export
(.add) : {x1 : F} -> SF x1 -> {x2 : F} -> SF (x1 + x2)
(.add) sx1 = sx1 + _

export
xA1p : {x1, x2, x0 : F} -> x1 == x2 -> x1 + x0 == x2 + x0
xA1p p = c21p ..> x1Ap p ..> c21p

export
c213pp : {x1, x2, x3 : F} -> x1 + (x2 + x3) == x2 + (x1 + x3)
c213pp = aP !.> xA1p c21p ..> aP

export
c13p24pp : {x1, x2, x3, x4 : F} -> (x1 + x2) + (x3 + x4) == (x1 + x3) + (x2 + x4)
c13p24pp = aP ..> x1Ap c213pp .!> aP

export
xABp : {x1, x2, x3, x4 : F} -> x1 == x2 -> x3 == x4 -> x1 + x3 == x2 + x4
xABp p1 p2 = xA1p p1 ..> x1Ap p2

export
tz1m2m : {x1, x2 : F} -> ((Z).fr * x1) * x2 == (Z).fr
tz1m2m = aM ..> tz1m

export
c13m2m : {x1, x2, x3 : F} -> (x1 * x2) * x3 == (x1 * x3) * x2
c13m2m = aM ..> x1Am c21m .!> aM

export
t12m1im : {x1, x2 : F} -> {sx1 : SF x1} -> (x1 * x2) * sx1.inv == x2 
t12m1im = c13m2m ..> t11im2m

export
t12m2im : {x1, x2 : F} -> {sx1 : SF x1} -> (x2 * x1) * sx1.inv == x2 
t12m2im = xA1m c21m ..> t12m1im

export
t12im2m : {x1, x2 : F} -> {sx1 : SF x1} -> (x2 * sx1.inv) * x1 == x2 
t12im2m = c13m2m ..> xA1m c21m ..> t12m1im

export
t12im : {x1, x2, x3 : F} -> {sx2 : SF x2} -> x1 == x3 * x2 -> x1 * sx2.inv == x3
t12im p = vA1sm sx2 (t12im2m ..> p)

export
x1ApBp : {x1, x2, x3, x4, x5 : F} -> x2 + x3 == x4 + x5 -> (x1 + x2) + x3 == (x1 + x4) + x5
x1ApBp p = aP ..> x1Ap p .!> aP

export
t123pm : {x1, x2, x0 : F} -> x0 * (x1 + x2)  == x0 * x1 + x0 * x2
t123pm = c21m ..> t12p3m ..> xA1p c21m ..> x1Ap c21m

export
xAB1mm : {x1, x2, x3, x4, x5 : F} -> x1 * x2 == x3 * x4 -> x1 * (x2 * x5) == x3 * (x4 * x5)
xAB1mm p = aM !.> xA1m p ..> aM

export
c213mm : {x1, x2, x3 : F} -> x1 * (x2 * x3) == x2 * (x1 * x3)
c213mm = aM !.> xA1m c21m ..> aM

export
xA1Bmm : {x1, x2, x3, x4, x5 : F} -> x1 * x2 == x3 * x4 -> x1 * (x5 * x2) == x3 * (x5 * x4)
xA1Bmm p = c213mm ..> x1Am p ..> c213mm

export
c213m4mm : {x1, x2, x3, x4 : F} -> x1 * ((x2 * x3) * x4) == x2 * ((x1 * x3) * x4)
c213m4mm = aM !.> xA1m c213mm ..> aM

export
c13m24mm : {x1, x2, x3, x4 : F} -> (x1 * x2) * (x3 * x4) == (x1 * x3) * (x2 * x4)
c13m24mm = aM ..> x1Am c213mm .!> aM

export
t12im3m : {x1, x2, x3, x4 : F} -> {sx2 : SF x2} -> x1 * x3 == x4 * x2 -> (x1 * sx2.inv) * x3 == x4
t12im3m p = c13m2m ..> t12im p

export
x1AmBm : {x1, x2, x3, x4, x5 : F} -> x2 * x3 == x4 * x5 -> (x1 * x2) * x3 == (x1 * x4) * x5
x1AmBm p = aM ..> x1Am p .!> aM

export
c13p2p : {x1, x2, x3 : F} -> (x1 + x2) + x3 == (x1 + x3) + x2
c13p2p = aP ..> x1Ap c21p .!> aP

export
c31m2m : {x1, x2, x3 : F} -> (x1 * x2) * x3 == (x3 * x1) * x2
c31m2m = c13m2m ..> xA1m c21m

export
x1Ap2p : {x1, x2, x3, x4, x5 : F} -> x2 == x4 -> (x1 + x2) + x3 == (x1 + x4) + x3
x1Ap2p x = c13p2p ..> x1Ap x ..> c13p2p

export
t1232m1imm : {x1, x2, x3 : F} -> {sx1 : SF x1} -> x1 * (x2 + ((x3 * x2) * sx1.inv)) == (x1 + x3) * x2
t1232m1imm = t123pm ..> x1Ap (c21m ..> t12im2m) .!> t12p3m

export
t112m3im3m : {x1, x2, x3 : F} -> {sx3 : SF x3} -> (x1 + ((x1 * x2) * sx3.inv)) * x3 == x1 * (x3 + x2)
t112m3im3m = c21m ..> x1Am (x1Ap (xA1m c21m)) ..> t1232m1imm ..> c21m

export
c321mm : {x1, x2, x3 : F} -> x1 * (x2 * x3) == x3 * (x2 * x1)
c321mm = c21m ..> xA1m c21m ..> aM

export
c14m23mm : {x1, x2, x3, x4 : F} -> (x1 * x2) * (x3 * x4) == (x1 * x4) * (x3 * x2)
c14m23mm = aM ..> x1Am c321mm .!> aM

export
xABm : {a1, a2, b1, b2 : F} -> a1 == a2 -> b1 == b2 -> a1 * b1 == a2 * b2
xABm p1 p2 = xA1m p1 ..> x1Am p2

export
c31p2p : {x1, x2, x3 : F} -> (x1 + x2) + x3 == (x3 + x1) + x2

export
c23p1p : {x1, x2, x3 : F} -> (x1 + x2) + x3 == (x2 + x3) + x1
