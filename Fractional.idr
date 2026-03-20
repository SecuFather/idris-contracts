module Fractional

import Natural
import NaturalExt
import Common

%default total

export
(+) : F -> F -> F
(+) (Fr x1 y1 p1) (Fr x2 y2 p2) =
  Fr (x1 * y2 + x2 * y1) (y1 * y2) (xABm p1 p2 ..> t1s2sm)

export
data (==) : (x1, x2 : F) -> Type where
  Feq : x1 * y2 = y1 * x2 -> Fr x1 y1 q == Fr x2 y2 r

export
sym : {x1, x2 : F} -> x1 == x2 -> x2 == x1
sym (Feq p) = Feq $ c21m .!> c21m ..> p

export
refl : {x : F} -> x == x
refl {x = Fr x y p} = Feq c21m

export
(.fr) : N -> F
(.fr) x = Fr x (S Z) Refl

export
t1f2fp : {x1, x2 : N} -> x1.fr + x2.fr == (x1 + x2).fr
t1f2fp = Feq $ t1um ..> t1um2p ..> t12ump .!> t1um2m ..> tu1m

export
(..>) : {x1, x2, x3 : F} -> x1 == x2 -> x2 == x3 -> x1 == x3
(..>) (Feq p1) (Feq p2) {x1 = Fr x1 (S y1) Refl, x2 = Fr x2 (S y2) Refl, x3 = Fr x3 (S y3) Refl} = 
  Feq $ vA1sm $ c13m2m ..> xA1m p1 ..> c23m1m ..> xA1m p2 ..> c32m1m

export
(.!>) : {x1, x2, x3 : F} -> x1 == x2 -> x3 == x2 -> x1 == x3
(.!>) p1 p2 = p1 ..> sym p2

export
(!.>) : {x1, x2, x3 : F} -> x2 == x1 -> x2 == x3 -> x1 == x3
(!.>) p1 p2 = sym p1 ..> p2

export
(!!>) : {x1, x2, x3 : F} -> x2 == x1 -> x3 == x2 -> x1 == x3
(!!>) p1 p2 = sym p1 ..> sym p2

export
tz1p : {x1 : F} -> (Z).fr + x1 == x1
tz1p {x1 = Fr x (S y) Refl} = Feq $ t12ump3m ..> tz1m2p3m ..> c21m .!> xA1m tu1m

export
c21p : {x1, x2 : F} -> x1 + x2 == x2 + x1
c21p {x1 = Fr x1 (S y1) Refl, x2 = Fr x2 (S y2) Refl} = Feq $ c21m ..> c21m3m ..> x1Am c21p

export
v1Ap : {x1, a1, a2 : F} -> x1 + a1 == x1 + a2 -> a1 == a2
v1Ap {x1 = Fr x1 (S y1) Refl, a1 = Fr ax1 (S ay1) Refl, a2 = Fr ax2 (S ay2) Refl} (Feq p) =
  Feq $ c21m ..> (vAB1smm $ v1Ap $ c321mm4p ..> t123pm !.> (v1sAmBm $ c21m ..> p) ..> t123pm)

export
aP : {x1, x2, x3 : F} -> (x1 + x2) + x3 == x1 + (x2 + x3)
aP {x1 = Fr x1 y1 p1, x2 = Fr x2 y2 p2, x3 = Fr x3 y3 p3} =
  Feq $ c21m .!> xABm aM (t123p4mp ..> c312pp ..> xABCpp (aM !.> c13m2m) aM c13m2m !.> t123p4mp !.> c21p)

export
(*) : (x1, x2 : F) -> F
(*) (Fr x1 y1 p1) (Fr x2 y2 p2) = Fr (x1 * x2) (y1 * y2) (xABm p1 p2 ..> t1s2sm)

export
aM : {x1, x2, x3 : F} -> (x1 * x2) * x3 == x1 * (x2 * x3)
aM {x1 = Fr x1 y1 p1, x2 = Fr x2 y2 p2, x3 = Fr x3 y3 p3} = Feq $ c21m ..> xABm (sym aM) aM

export
x1Ap : {x1, x2, x0 : F} -> x1 == x2 -> x0 + x1 == x0 + x2
x1Ap (Feq q) {x0 = Fr x0 (S y0) Refl, x1 = Fr x1 (S y1) Refl, x2 = Fr x2 (S y2) Refl} = let
  p0 = t12p3m ..> cong2 (+) aM aM ..> cong2 (+) c213mm c213mm ..> x1Ap (x1Am q ..> c231mm)  .!> t123pm
  p = c213mm ..> x1Am p0 .!> aM
  in Feq p

export
(.inv) : {x1 : F} -> SF x1 -> F
(.inv) (SFr p {x,y}) = Fr y x p

export
(.sinv) : {x1 : F} -> (sx1 : SF x1) -> SF sx1.inv
(.sinv) (SFr p {q}) = SFr q

namespace SFPlus
  export
  (+) : {x1 : F} -> SF x1 -> (x2 : F) -> SF (x1 + x2)
  (+) (SFr Refl) {x1 = Fr Z (S y1) Refl} (Fr x2 (S y2) Refl) impossible
  (+) (SFr Refl) {x1 = Fr (S x1) (S y1) Refl} (Fr x2 (S y2) Refl) = SFr (xA1p t1s2sm ..> t1s2p)

export
tz1m : {x1 : F} -> (Z).fr * x1 == (Z).fr
tz1m {x1 = Fr x1 (S y1) Refl} = Feq (tz1m2m .!> t1zm)

export
t12p3m : {x1, x2, x0 : F} -> (x1 + x2) * x0 == x1 * x0 + x2 * x0
t12p3m {x1 = Fr x1 (S y1) Refl, x2 = Fr x2 (S y2) Refl, x0 = Fr x0 (S y0) Refl} = 
  Feq (x1Am c13m24mm ..> c213mm ..> x1Am (c213mm ..> x1Am (aM ..> t12p3m ..> cong2 (+) c13m24mm c13m24mm)) .!> aM)

export
t11im2m : {x1, x2 : F} -> {sx1 : SF x1} -> (x1 * sx1.inv) * x2 == x2 
t11im2m {x1 = Fr Z y1 q1, sx1 = SFr Refl} impossible
t11im2m {x1 = Fr (S x1) (S y1) Refl, sx1 = SFr Refl, x2 = Fr x2 (S y2) Refl} = 
  Feq (xA1m c21m3m ..> c13m2m)

export
c21m : {x1, x2 : F} -> x1 * x2 == x2 * x1
c21m {x1 = Fr x1 (S y1) Refl, x2 = Fr x2 (S y2) Refl} = Feq c43m21mm

export
x1Am : {x1, x2, x0 : F} -> x1 == x2 -> x0 * x1 == x0 * x2
x1Am (Feq p) {x0 = Fr x0 (S y0) Refl} = let
  p2 = c13m24mm ..> cong2 (*) c21m p ..> c13m24mm
  in Feq p2

export
v1sAm : {x1, x2, x0 : F} -> (sx0 : SF x0) -> x0 * x1 == x0 * x2 -> x1 == x2
v1sAm (SFr Refl) _ {x0 = Fr Z (S y0) Refl, x1 = Fr x1 (S y1) Refl, x2 = Fr x2 (S y2) Refl} impossible
v1sAm (SFr Refl) (Feq p) {x0 = Fr (S x0) (S y0) Refl, x1 = Fr x1 (S y1) Refl, x2 = Fr x2 (S y2) Refl} = let
  p2 = c13m24mm ..> c32m14mm ..> p ..> c13m24mm
  p3 = v1sAm $ xA1m t1s2sm !.> p2 ..> xA1m t1s2sm
  in Feq p3

export
sfr : {x : N} -> SF ((S x).fr)
sfr = SFr Refl

export
t1f2fm : {x1, x2 : N} -> x1.fr * x2.fr == (x1 * x2).fr
t1f2fm = Feq $ c21m .!> xA1m t1um

export
vAf : {x1, x2 : N} -> x1.fr == x2.fr -> x1 = x2
vAf (Feq p) = t1um !.> p ..> tu1m