module LiquidToken

import Common
import Natural
import NaturalExt
import Token
import TokenExt
import Fractional
import FractionalExt
import Shares

%default total

public export
record LiquidToken (n, m, b0 : N) (u0 : Fi n) (utok : Token n m) where
  constructor LiqTok
  {tok : Token n m}
  {shr : Shares n}
  vts : shr.ts == (tok.ubr u0 + S b0).fr
  vtb : shr.tb == (utok.ub u0).fr
  vus : (w : Fi n) -> (u0 = w -> Void) -> shr.us w == (tok.ub w).fr

public export
record DeployPre (n, m, b0 : N) (u, u0 : Fi n) (utok1, utok2 : Token n m) where
  constructor Deploying
  uu0 : u = u0 -> Void
  v1 : utok2 <<< Transfer utok1 u u0 (S b0)

public export
record Deploy (n, m, b0 : N) (u, u0 : Fi n) (utok1, utok2 : Token n m) (liqTok : LiquidToken n m b0 u0 utok2) where
  constructor Deployed
  p : DeployPre n m b0 u u0 utok1 utok2

export
deploy : (n, m, b0 : N) -> (u, u0 : Fi n) -> (utok1, utok2 : Token n m) -> 
  DeployPre n m b0 u u0 utok1 utok2 -> (liqTok ** liqTok <<< Deploy n m b0 u u0 utok1 utok2)
deploy n m b0 u u0 utok1 utok2 p = let
  (tok ** vtok) = TokenExt.deploy n m u0
  (shr ** vshr) = Shares.deploy n (S b0).fr (Deploying sfr)
  (shr2 ** vshr2) = shr.donate (utok1.ub u0).fr
  vts = vshr2.ts ..> vshr.ts .!> xAf (xA1p vtok.ubr ..> tz1p)
  vtb = vshr2.tba ..> xA1p vshr.tb ..> t1f2fp ..> xAf (c21p .!> p.v1.ub2 p.uu0)
  vus = \w, u0w => vshr2.us w ..> vshr.us w .!> xAf (vtok.ub0 w u0w)
  in (LiqTok vts vtb vus ** Deployed p)

public export
record DepositPre (liqTok : LiquidToken n m b0 u0 utok1) (u : Fi n) (a : N) (utok2 : Token n m) where
  constructor Depositing
  uu0 : u = u0 -> Void
  v1 : utok2 <<< Transfer utok1 u u0 a
  
public export
record Deposit (liqTok : LiquidToken n m b0 u0 utok1) (u : Fi n) (a : N) (utok2 : Token n m) (liqTok2 : LiquidToken n m b0 u0 utok2) where
  constructor Deposited
  p : DepositPre liqTok u a utok2
