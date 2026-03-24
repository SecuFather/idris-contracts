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
natContra1 : {x : N} -> Z = S x -> Void
natContra1 Refl impossible

export
natContra2 : {x : N} -> S x = Z -> Void
natContra2 Refl impossible

export
natContra3 : {x1, x2 : N} -> (x1 = x2 -> Void) -> S x1 = S x2 -> Void
natContra3 contra Refl = contra Refl

export
natEq : (x1, x2 : N) -> Dec (x1 = x2)
natEq Z Z = Yes Refl
natEq Z (S x2) = No natContra1
natEq (S x1) Z = No natContra2
natEq (S x1) (S x2) = case natEq x1 x2 of
  Yes prf => Yes (xAs prf)
  No contra => No (natContra3 contra)

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
contra2nat : {x1 : N} -> (x1 = Z -> Void) -> (x2 ** x1 = S x2)
contra2nat f {x1 = Z} = void (f Refl)
contra2nat f {x1 = S x1} = (x1 ** Refl)

export
sub : (x1, x2 : N) -> N
sub x1 Z = x1
sub Z (S x2) = Z
sub (S x1) (S x2) = sub x1 x2

export
esubs : (x1, x2 : N) -> (x3 ** Either (x1 = x2 + S x3) (x2 = x1 + x3))
esubs Z x2 = (x2 ** Right Refl)
esubs (S x1) Z = (x1 ** Left Refl)
esubs (S x1) (S x2) = let (x4 ** p) = esubs x1 x2 in case p of
  Left p1 => (x4 ** Left $ xAs p1)
  Right p2 => (x4 ** Right $ xAs p2)

export
divf : (x1, x2 : N) -> {x3, x4 : N} -> {p : x3 = x1 + x4} -> N
divf Z x2 = Z
divf (S x1) x2 {x3 = Z} = void (natContra1 p)
divf (S x1) x2 {x3 = S x3} = let (x5 ** e) = esubs (S x1) x2 in case e of
  Left p1 => S $ divf x5 x2 {x3, p = vAs p ..> xA1p (vAs $ p1 ..> c21p) ..> aP}
  Right p2 => Z

export
modf : (x1, x2 : N) -> {x3, x4 : N} -> {p : x3 = x1 + x4} -> N
modf Z x2 = Z
modf (S x1) x2 {x3 = Z} = void (natContra1 p)
modf (S x1) x2 {x3 = S x3} = let (x5 ** e) = esubs (S x1) x2 in case e of
  Left p1 => modf x5 x2 {x3, p = vAs p ..> xA1p (vAs $ p1 ..> c21p) ..> aP}
  Right p2 => S x1

export
modz : (x1, x2 : N) -> {x3, x4 : N} -> {p : x3 = x1 + x4} -> N
modz Z x2 = Z
modz (S x1) x2 {x3 = Z} = void (natContra1 p)
modz (S x1) x2 {x3 = S x3} = let (x5 ** e) = esubs (S x1) x2 in case e of
  Left p1 => modz x5 x2 {x3, p = vAs p ..> xA1p (vAs $ p1 ..> c21p) ..> aP}
  Right p2 => S Z

export
modr : (x1, x2 : N) -> {x3, x4 : N} -> {p : x3 = x1 + x4} -> N
modr Z x2 = x2
modr (S x1) x2 {x3 = Z} = void (natContra1 p)
modr (S x1) x2 {x3 = S x3} = let (x5 ** e) = esubs (S x1) x2 in case e of
  Left p1 => modr x5 x2 {x3, p = vAs p ..> xA1p (vAs $ p1 ..> c21p) ..> aP}
  Right p2 => x5

export
div : (x1, x2 : N) -> N
div x1 x2 = divf x1 x2 {p = sym t1zp}

export
mod : (x1, x2 : N) -> N
mod x1 x2 = modf x1 x2 {p = sym t1zp}

export
divc : (x1, x2 : N) -> N
divc x1 x2 = divf (x1 + x2) x2 {p = sym t1zp}

export
modc : (x1, x2 : N) -> N
modc x1 x2 = modr (x1 + x2) x2 {p = sym t1zp}

export
tdivf : {x1, x2, x3, x4 : N} -> {p : x3 = x1 + x4} -> x1 = divf x1 x2 {p} * (S x2) + modf x1 x2 {p}
tdivf {x1 = Z} = Refl
tdivf {x1 = S x, x3 = Z} = void (natContra1 p)
tdivf {x1 = S x, x3 = S x3} with (esubs (S x) x2)
  tdivf {x1 = S x, x3 = S x3} | (x5 ** Left p1) = p1 ..> t12sp ..> (xAs $ x1Ap tdivf .!> aP)
  tdivf {x1 = S x, x3 = S x3} | (x5 ** Right p2) = Refl

export
tmodf : {x1, x2, x3, x4 : N} -> {p : x3 = x1 + x4} -> x2 = modf x1 x2 {p} + modr x1 x2 {p}
tmodf {x1 = Z} = Refl
tmodf {x1 = S x, x3 = Z} = void (natContra1 p)
tmodf {x1 = S x, x3 = S x3} with (esubs (S x) x2)
  tmodf {x1 = S x, x3 = S x3} | (x5 ** Left p1) = tmodf
  tmodf {x1 = S x, x3 = S x3} | (x5 ** Right p2) = p2

export
t12d2sm : {x1, x2 : N} -> mod x1 x2 + div x1 x2 * (S x2) = x1
t12d2sm = c21p .!> tdivf

export
t12c2sm : {x1, x2 : N} -> divc x1 x2 * (S x2) = x1 + modc x1 x2
t12c2sm = v1Ap $ t12d2sm ..> x1Ap tmodf ..> c213pp

export
congDivL : {a1, a2, x2, x3, x4, x5, x6: N} -> {p : x3 = a1 + x4} -> {pp : x5 = a2 + x6} -> a1 = a2 -> divf a1 x2 {p,x4} = divf a2 x2 {p=pp,x4=x6}
congDivL Refl {a2 = Z} = Refl
congDivL Refl {a2 = S a2, x3 = Z} = void (natContra1 p)
congDivL Refl {a2 = S a2, x3 = S x3, x5 = Z} = void (natContra1 pp)
congDivL Refl {a2 = S a2, x3 = S x3, x5 = S x5} with (esubs (S a2) x2)
  congDivL Refl {a2 = S a2, x3 = S x3, x5 = S x5} | (x7 ** Left p1) = xAs $ congDivL Refl
  congDivL Refl {a2 = S a2, x3 = S x3, x5 = S x5} | (x7 ** Right p2) = Refl

export
tdivm : {x1, x2, x3, x4 : N} -> {p : x3 = (x1 * S x2) + x4} -> divf (x1 * S x2) x2 {p,x4} = x1
tdivm {x1 = Z} = Refl
tdivm {x1 = S x, x3 = Z} = void (natContra1 p)
tdivm {x1 = S x, x3 = S x3} with (esubs (S (x2 + (x * S x2))) x2)
  tdivm {x1 = S x, x3 = S x3} | (x5 ** Left p1) = let
    v1 = vAs $ v1Ap $ p1 !!> t12sp
    v2 = vAs $ p ..> xAs (aP ..> c213pp)
    in xAs $ congDivL v1 ..> tdivm {p = v2}
  tdivm {x1 = S x, x3 = S x3} | (x5 ** Right p2) = void $ natContra1 $ v1Ap $ t1zp ..> p2 ..> xAs aP .!> t12sp

export
tdivp : {x1, x2, x3, x4, x5, x6 : N} -> {p : x3 = (x1 + x5 * S x2) + x4} -> {pp : x3 = x1 + x6} -> 
divf (x1 + x5 * S x2) x2 {p,x4} = (divf x1 x2 {p=pp}) + x5
tdivp {x5 = Z} = congDivL t1zp .!> t1zp
tdivp {x5 = S x5, x3 = Z} = void $ natContra1 $ p ..> xA1p t12sp
tdivp {x5 = S x5, x3 = S x3} with (x1 + S (x2 + (x5 * S x2))) proof v1
  tdivp {x5 = S x5, x3 = S x3} | Z = void $ natContra1 $ v1 !.> t12sp
  tdivp {x5 = S x5, x3 = S x3} | (S x7) with (esubs (S x7) x2)
    tdivp {x5 = S x5, x3 = S x3} | (S x7) | (x8 ** Left p1) = let
      v2 = vAs $ p1 ..> t12sp
      v4 = vAs $ t12sp !.> v1
      v5 = p .!> t12sp ..> xAs (aP !.> xA1p (c21p ..> c213pp ..> v4))
      v6 = v1Ap $ v2 !.> v4 !.> c213pp
      in xAs (congDivL {pp = v5} v6 ..> tdivp) .!> t12sp
    tdivp {x5 = S x5, x3 = S x3} | (S x7) | (x8 ** Right p2) = 
      void $ natContra1 $ v1Ap $ t1zp ..> vAs (v1 !.> t12sp ..> xAs (c213pp ..> xA1p p2 ..> xAs aP .!> t12sp))


export
t123smp3d : {x1, x2, x3 : N} -> (x1 + x2 * S x3) `div` x3 = x1 `div` x3 + x2
t123smp3d = tdivp ..> xA1p (congDivL Refl {p = Refl})

export
tz1d : {x1 : N} -> Z * x1 `div` x1 = Z
tz1d = Refl