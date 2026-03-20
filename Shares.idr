module Shares

import Common
import Natural
import NaturalExt
import Fractional
import FractionalExt

%default total

record RootShare where
  constructor RootShr
  {b : F}
  sb : SF b
  r : F

mutual
  export
  data Shares : N -> Type where
    Shar : (acc : RootShare) -> Shares Z
    (::) : (shr : Shares n) -> (acc : UserShare shr) -> Shares (S n)

  export
  record UserShare (shr : Shares n) where
    constructor UserShr
    {b, r : F}
    bs : shr.share b + r == b

  export
  (.ts) : Shares n -> F
  (.ts) (Shar acc) = acc.b
  (.ts) (shr :: acc) = shr.ts + shr.share acc.b

  export
  (.tb) : Shares n -> F
  (.tb) (Shar acc) = acc.b + acc.r
  (.tb) (shr :: acc) = shr.tb + acc.b

  export
  (.stb) : (shr : Shares n) -> SF shr.tb
  (.stb) (Shar acc) = acc.sb.add
  (.stb) (shr :: acc) = shr.stb + acc.b

  export
  (.share) : Shares n -> F -> F
  (.share) shr x = x * shr.ts * shr.stb.inv

export
(.us) : (shr : Shares n) -> Fi n -> F
(.us) (shr :: acc) FZ = shr.share acc.b
(.us) (shr :: acc) (FS u) = shr.us u

export
(.sts) : (shr : Shares n) -> SF shr.ts
(.sts) (Shar acc) = acc.sb
(.sts) (shr :: acc) = shr.sts + shr.share acc.b

export
(.tr) : (shr : Shares n) -> F
(.tr) (Shar acc) = acc.r
(.tr) (shr :: acc) = shr.tr + acc.r

export
(.tbts) : (shr : Shares n) -> shr.tr == shr.tb - shr.ts
(.tbts) (Shar acc) = refl
(.tbts) (shr :: acc) = c13p24pp ..> xABp shr.tbts acc.bs

public export
record DeployPre (n : N) (b : F) where
  constructor Deploying
  sb : SF b

public export
record Deploy (n : N) (b : F) (shr : Shares n) where
  constructor Deployed
  tb : shr.tb == b
  ts : shr.ts == b
  us : (w : Fi n) -> shr.us w == (Z).fr
  tbts : shr.tb == shr.ts

export
deploy : (n : N) -> (b : F) -> DeployPre n b -> (shr ** shr <<< Deploy n b)
deploy Z b p = (Shar (RootShr p.sb (Z).fr) ** Deployed t1zp refl (\w => fiVoid w) t1zp)
deploy (S n) b p = let
  (shr ** vshr) = deploy n b (Deploying p.sb)
  tb = t1zp ..> vshr.tb
  ts = x1Ap tz1m2m ..> t1zp ..> vshr.ts
  bs = t1zp ..> tz1m2m
  tbts = tb .!> ts
  in (shr :: UserShr bs ** Deployed tb ts (\w => case w of
    FZ => tz1m2m
    FS w => vshr.us w) tbts)

public export
record Donate (shr : Shares n) (a : F) (shr2 : ty shr) where
  constructor Donated
  tba : shr2.tb == shr.tb + a
  ts : shr2.ts == shr.ts
  us : (w : Fi n) -> shr2.us w == shr.us w

export
(.donate) : (shr : Shares n) -> (a : F) -> (shr2 ** shr2 <<< Donate shr a)
(.donate) (Shar acc) a = let
  tb = sym aP
  us = \w => fiVoid w
  in (Shar (RootShr acc.sb (acc.r + a)) ** Donated tb refl us)
(.donate) (shr :: acc) a = let
  (shr2 ** vshr2) = shr.donate (a * shr.tb * (shr.stb + acc.b).inv) 
  tb0 = t12p3m !.> t12im (t123pm !.> x1Am c21p)
  tb = xA1p vshr2.tba ..> x1ApBp (c21p ..> aP ..> x1Ap tb0)
  us1 = xAB1mm (xA1Bmm (t12im2m ..> c21m)) ..> c21m
  us0 = t12im (x1Am vshr2.ts .!> x1Am vshr2.tba .!> t12p3m .!> t123pm ..> xABp t12im2m us1)
  ts = xABp vshr2.ts us0
  bs = xA1p us0 ..> aP !.> xA1p acc.bs
  in (shr2 :: (UserShr bs) ** Donated tb ts (\w => case w of
    FZ => us0
    FS w => vshr2.us w))

public export
record Deposit (shr : Shares n) (u : Fi n) (a : F) (shr2 : ty shr) where
  constructor Deposited
  {x : F}
  tba : shr2.tb == shr.tb + a
  xs : x == a * shr.ts * shr.stb.inv
  tsx : shr2.ts == shr.ts + x
  usx : shr2.us u == shr.us u + x
  us : (w : Fi n) -> (w = u -> Void) -> shr2.us w == shr.us w

export
(.deposit) : (shr : Shares n) -> (u : Fi n) -> (a : F) -> (shr2 ** shr2 <<< Deposit shr u a)
(.deposit) (shr :: acc) FZ a = let
  tba = sym aP
  us0 = t12im3m $ x1AmBm $ t12p3m ..> x1Ap (t12im2m ..> c21m) .!> t123pm
  usx = t12im $ t12p3m ..> xABp t12im2m us0 !!> t12p3m
  tsx = sym $ aP ..> (x1Ap $ sym usx)
  bs = t12p3m !.> t12im (t123pm !.> x1Am shr.tbts)
  in (shr :: UserShr bs ** Deposited tba refl tsx usx (\w, f => case w of
    FZ => void (f Refl)
    FS _ => refl))
(.deposit) (shr :: acc) (FS u) a = let
  (shr2 ** vshr2) = shr.deposit u a
  tba = xA1p vshr2.tba ..> c13p2p
  usx0 = t12im (t123pm .!> xA1m vshr2.xs ..> t123pm ..> xABp t12im2m (c21m ..> c213m4mm))
  usx = vshr2.usx .!> x1Ap usx0
  tsx0 = aM ..> x1Am (sym $ t12im $ vshr2.tsx ..> xABp t12im2m (c31m2m .!> vshr2.xs) !.> t123pm !!> x1Am vshr2.tba) .!> aM
  tsx = xA1p vshr2.tsx ..> x1ApBp (c21p .!> xABp tsx0 usx0)
  bs = xA1p tsx0 !.> acc.bs
  in (shr2 :: (UserShr bs) ** Deposited tba refl tsx usx (\w, f => case w of
    FZ => sym tsx0
    FS w => vshr2.us w (fiContra4 f)))

public export
record WithdrawPre (shr : Shares n) (u : Fi n) (a : F) where
  constructor Withdrawing
  {x : F}
  usa : x == shr.us u - a

public export
record Withdraw (shr : Shares n) (u : Fi n) (a : F) (shr2 : ty shr) where
  constructor Withdrawn
  p : WithdrawPre shr u a
  {y : F}
  ys : y == a * shr.tb * shr.sts.inv
  tby : shr2.tb == shr.tb - y
  tsx : shr2.ts == shr.ts - a
  usx : shr2.us u == p.x
  us : (w : Fi n) -> (w = u -> Void) -> shr2.us w == shr.us w

  usa : shr2.us u == shr.us u - a

export
(.withdraw) : (shr : Shares n) -> (u : Fi n) -> (a : F) -> WithdrawPre shr u a -> (shr2 ** shr2 <<< Withdraw shr u a)
(.withdraw) (shr :: acc) FZ a p = let
  usx = xA1m (t12im2m {sx1 = shr.sts}) ..> t12m2im
  tsx = c21p ..> aP ..> x1Ap (c21p ..> x1Ap usx ..> p.usa)
  bs = xA1p usx .!> t12im (x1Am shr.tbts !!> t112m3im3m {sx3 = shr.sts})
  tby1 = t12im3m $ x1AmBm $ sym t1232m1imm
  tby0 = t12im $ t12p3m ..> xABp tby1 t12im2m .!> t12p3m
  tby = c21p ..> aP ..> x1Ap (c21p ..> vA1sm shr.sts (vA1sm shr.stb.sinv (tby0 ..> p.usa)))
  in (shr :: UserShr bs ** Withdrawn p refl tby tsx usx (\w, f => case w of
    FZ => void (f Refl)
    FS w => refl) (x1Ap usx ..> p.usa))
(.withdraw) (shr :: acc) (FS u) a p = let
  (shr2 ** vshr2) = shr.withdraw u a (Withdrawing p.usa)
  usx = v1Ap $ vshr2.usa .!> p.usa
  ys = t12im3m $ vA1sm shr.sts.sinv (t12m1im ..> vshr2.ys)
  tsx0 = x1AmBm $ t12im $ v1Ap $ xA1p ys ..> vshr2.tsx ..> t12im2m !.> x1Am vshr2.tby !.> t123pm
  tsx = aP !.> xA1p vshr2.tsx ..> x1Ap tsx0
  tby = xA1p $ xA1p (t12im (t123pm ..> xABp t12im2m (c14m23mm ..> xABm t12m2im t12m2im) !!> t123pm) .!> vshr2.ys) ..> vshr2.tby
  bs = xA1p tsx0 ..> acc.bs
  in (shr2 :: (UserShr bs) ** Withdrawn p refl (aP !.> tby) tsx usx (\w, f => case w of
    FZ => tsx0
    FS w => vshr2.us w (fiContra4 f)) vshr2.usa)
