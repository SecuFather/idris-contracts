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
  v1 : liqTok2.tok <<< Transfer liqTok.tok u0 u (a * liqTok.ts `div` liqTok.tb1)

export
(.deposit) : {n, m, b0 : N} -> {u0 : Fi n} -> {utok : Token n m} ->
  (liqTok : LiquidToken n m b0 u0) -> (u : Fi n) -> (a : N) ->
  DepositPre liqTok u a utok -> (liqTok2 ** liqTok2 <<< Deposit liqTok u a)
(.deposit) liqTok u a p = (LiqTok vts vtb (\w, f => case fiEq w u of
  Yes Refl => shr2.snd.us w ..> shr.snd.usx ..> xABp (liqTok.vus w f) p5 ..> t1f2fp .!> xAf (tok.snd.ub2 f)
  No contra => shr2.snd.us w ..> shr.snd.us w contra ..> liqTok.vus w f .!> xAf (tok.snd.ub w f (c21v contra))) vtr ** Deposited p tok.snd) where
 shr = liqTok.shr.deposit u $ (a * liqTok.ts `div` liqTok.tb1).fr * liqTok.shr.tb * liqTok.shr.sts.inv
 shr2 = shr.fst.donate $ (a * liqTok.ts `mod` liqTok.tb1).fr * liqTok.shr.sts.inv
 p1 = t12sm2d !.> xA1d (x1Am t1s2p !.> t123pm) ..> t12p3d
 p2 = p.v1.ubr2 p.uu0
 p3 = c13p2p ..> xABp p2 liqTok.vtr ..> c21p ..> mub .!> mub
 bal = liqTok.tok.bal.burn u0 (a * liqTok.ts `div` liqTok.tb1) $ Burning $ 
   (aP !.> aP !.> xA1p p1 !.> vA1p (c143pp2p ..> aP !.> xA1p aP ..> p3)) ..> ub
 tok = liqTok.tok.transfer u0 u (a * liqTok.ts `div` liqTok.tb1) (Transferring bal.snd)
 pa = t12p3m !.> t12im (xA1p (x1Am (liqTok.vtb .!> xAf (t12sp3p !.> liqTok.vtr)) ..> t1f2fm) ..> c21p ..> t1f2fp ..> xAf t12d2sm ..> t1f2fm !!> x1Am (liqTok.vts ..> xAf t12sp))
 vtb = shr2.snd.tba ..> xA1p shr.snd.tba ..> aP ..> xABp liqTok.vtb pa ..> t1f2fp .!> xAf (p.v1.ub2 p.uu0)
 p4 = tok.snd.ubr1 p.uu0
 p5 = shr.snd.xs ..> xA1m t12im2m ..> t12m2im
 p6 = p.v1.ub2 p.uu0
 vtr = c32p1p ..> x1Ap p4 ..> xA1p c32p1p ..> c13p24pp ..> xABp (c31p2p ..> liqTok.vtr) (c21p ..> aP !!> p1) .!> p6
 vts = shr2.snd.ts ..> shr.snd.tsx ..> xA1p (liqTok.vts .!> t1f2fp) ..> c13p2p ..> xA1p (x1Ap p5 ..> t1f2fp .!> xAf p4) ..> t1f2fp
--all the proofs defined under where clause, because of performance issues


public export
record WithdrawPre (liqTok : LiquidToken n m b0 u0) (u : Fi n) (a : N) (tok2 : Token n m) where
  constructor Withdrawing
  uu0 : u = u0 -> Void
  v1 : tok2 <<< Transfer liqTok.tok u u0 a

public export
record Withdraw (liqTok : LiquidToken n m b0 u0) (u : Fi n) (a : N) (liqTok2 : LiquidToken n m b0 u0) where
  constructor Withdrawn
  p : WithdrawPre liqTok u a liqTok2.tok
  v1 : liqTok2.utok <<< Transfer liqTok.utok u0 u (a * liqTok.tb `div` liqTok.ts1)

export
(.withdraw) : {n, m, b0 : N} -> {u0 : Fi n} -> {tok : Token n m} ->
  (liqTok : LiquidToken n m b0 u0) -> (u : Fi n) -> (a : N) ->
  WithdrawPre liqTok u a tok -> (liqTok2 ** liqTok2 <<< Withdraw liqTok u a)
(.withdraw) liqTok u a p = ?sdsddds