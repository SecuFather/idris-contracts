module LiquidToken

import Common
import Natural
import NaturalExt
import Token
import TokenExt
import Fractional
import FractionalExt
import Shares
import Balances

%default total

public export
record LiquidToken (n, m, b0 : N) (u0 : Fi n) where
  constructor LiqTok
  {tok : Token n m}
  {utok : Token n m}
  {shr : Shares n}
  {tr : N}
  vts : shr.ts == (tok.ubr u0 + S b0).fr
  vtb : shr.tb == (utok.ub u0).fr
  vus : (w : Fi n) -> (u0 = w -> Void) -> shr.us w == (tok.ub w).fr
  vtr : (tok.ubr u0 + S b0) + tr = utok.ub u0

namespace LiquidToken
  (.ts1) : {n, m, b0 : N} -> {u0 : Fi n} -> LiquidToken n m b0 u0 -> N
  (.ts1) liqTok = liqTok.tok.ubr u0 + b0

  (.ts) : {n, m, b0 : N} -> {u0 : Fi n} -> LiquidToken n m b0 u0 -> N
  (.ts) liqTok = S liqTok.ts1

  (.tb1) : {n, m, b0 : N} -> {u0 : Fi n} -> LiquidToken n m b0 u0 -> N
  (.tb1) liqTok = liqTok.ts1 + liqTok.tr

  (.tb) : {n, m, b0 : N} -> {u0 : Fi n} -> LiquidToken n m b0 u0 -> N
  (.tb) liqTok = S liqTok.tb1

public export
record DeployPre (n, m, b0 : N) (u, u0 : Fi n) (utok1, utok2 : Token n m) where
  constructor Deploying
  uu0 : u = u0 -> Void
  v1 : utok2 <<< Transfer utok1 u u0 (S b0)

public export
record Deploy (n, m, b0 : N) (u, u0 : Fi n) (utok : Token n m) (liqTok : LiquidToken n m b0 u0) where
  constructor Deployed
  p : DeployPre n m b0 u u0 utok liqTok.utok

  tr : liqTok.tr = utok.ub u0
  ts : liqTok.ts = S b0
  
export
deploy : (n, m, b0 : N) -> (u, u0 : Fi n) -> (utok1, utok2 : Token n m) -> 
  DeployPre n m b0 u u0 utok1 utok2 -> (liqTok ** liqTok <<< Deploy n m b0 u u0 utok1)
deploy n m b0 u u0 utok1 utok2 p = let
  (tok ** vtok) = TokenExt.deploy n m u0
  (shr ** vshr) = Shares.deploy n (S b0).fr (Deploying sfr)
  (shr2 ** vshr2) = shr.donate (utok1.ub u0).fr
  ts0 = xA1p vtok.ubr ..> tz1p
  vts = vshr2.ts ..> vshr.ts .!> xAf ts0
  tb0 = c21p .!> p.v1.ub2 p.uu0
  vtb = vshr2.tba ..> xA1p vshr.tb ..> t1f2fp ..> xAf tb0
  vus = \w, u0w => vshr2.us w ..> vshr.us w .!> xAf (vtok.ub0 w u0w)
  vtr = xA1p ts0 ..> tb0
  in (LiqTok vts vtb vus vtr ** Deployed p Refl (t12sp !.> ts0))

public export
record DepositPre (liqTok : LiquidToken n m b0 u0) (u : Fi n) (a : N) (utok2 : Token n m) where
  constructor Depositing
  uu0 : u = u0 -> Void
  v1 : utok2 <<< Transfer liqTok.utok u u0 a
  
public export
record Deposit (liqTok : LiquidToken n m b0 u0) (u : Fi n) (a : N) (liqTok2 : LiquidToken n m b0 u0) where
  constructor Deposited
  p : DepositPre liqTok u a liqTok2.utok

export
(.deposit) : {n, m, b0 : N} -> {u0 : Fi n} -> {utok : Token n m} ->
  (liqTok : LiquidToken n m b0 u0) -> (u : Fi n) -> (a : N) ->
  DepositPre liqTok u a utok -> (liqTok2 ** liqTok2 <<< Deposit liqTok u a)
(.deposit) liqTok u a p = let
  (shr ** vshr) = liqTok.shr.deposit u $ (a * liqTok.ts `div` liqTok.tb1).fr * liqTok.shr.tb * liqTok.shr.sts.inv
  (shr2 ** vshr2) = shr.donate $ (a * liqTok.ts `mod` liqTok.tb1).fr * liqTok.shr.sts.inv
  p1 = t12sm2d !.> xA1d (x1Am t1s2p !.> t123pm) ..> t12p3d
  p2 = p.v1.ubr2 p.uu0
  p3 = c13p2p ..> xABp p2 liqTok.vtr ..> c21p ..> mub .!> mub
  (bal ** vbal) = liqTok.tok.bal.burn u0 (a * liqTok.ts `div` liqTok.tb1) $ Burning $ 
    (aP !.> aP !.> xA1p p1 !.> vA1p (c143pp2p ..> aP !.> xA1p aP ..> p3)) ..> ub
  (tok ** vtok) = liqTok.tok.transfer u0 u (a * liqTok.ts `div` liqTok.tb1) (Transferring vbal)
  -- pa = t12p3m !.> t12im (xA1p (x1Am liqTok.vtb1 !.> t1f2fm) ..> t1f2fp ..> xAf tdiv !.> t1f2fm !.> x1Am liqTok.vts1)
  -- vtb = vshr2.tba ..> xA1p vshr.tba ..> aP ..> xABp liqTok.vtb pa ..> t1f2fp .!> xAf (p.v1.ub2 p.uu0)
  -- p2 = vshr.tsx
  -- p3 = vshr.xs
  -- p4 = vshr.xs ..> xA1m t12im2m ..> t12m2im
    -- c143pp2p ..> c13p2p ..> vAf (t1f2fp !!> xAf mub !.> t1f2fp !.> xA1p vtb !.> ?koloaaaa ..> xA1p vshr2.ts ..> xA1p (vshr.tsx ..> x1Ap p4) ..> c23p1p ..> xA1p t1f2fp ..> x1Ap liqTok.vts) .!> mub) ..> ub
  -- in (LiqTok {shr = shr2, tok} (vshr2.ts ..> vshr.tsx ..> xABp (liqTok.vts .!> t1f2fp) p4 ..> c13p2p ..> xA1p (t1f2fp ..> xAf ?sadsss) ..> t1f2fp) vtb ?ccc ?dddd ?asdasd ** Deposited p)
  in (LiqTok ?vsts2 ?vtb2 ?vus2 ?vtr2 ** Deposited p)

--(aP !.> vAf (t1f2fp !.> xA1p p2 !.> ?ooooos))