module TokenExt

import Common
import Natural
import NaturalExt
import Balances
import Token

%default total

export
mub : {m : N} -> {tok : Token n m} -> {u : Fi n} -> tok.ubr u == m - tok.ub u
mub = xABp ub ubr ..> tok.bal.mub

public export
record Deploy (n, m : N) (u : Fi n) (tok : Token n m) where
  constructor Deployed
  {bal : Balances n m}
  v1 : bal <<< Deploy n m
  v2 : tok.bal <<< Mint bal u m

  ub : tok.ub u = m
  ubr : tok.ubr u = Z

  ub0 : (w : Fi n) -> (u = w -> Void) -> tok.ub w = Z

export
deploy : (n, m : N) -> (u : Fi n) -> (tok ** tok <<< Deploy n m u)
deploy n m u = let 
  (bal ** v1) = Balances.deploy n m
  (bal2 ** v2) = bal.mint u m (Minting $ t1zp .!> v1.rs)
  ub' = ub ..> v2.uba ..> xA1p (v1.ub u) ..> tz1p
  ubr' = ubr ..> v1Ap (v2.ubra ..> v1.ubr u .!> t1zp)
  in (Tok bal2 ** Deployed v1 v2 ub' ubr' (\w, uw => ub ..> v2.ub w uw ..> v1.ub w))

public export
record TransferPre (tok : Token n m) (u1, u2 : Fi n) (a : N) where
  constructor Transferring
  {bal : Balances n m}
  v1 : bal <<< Burn tok.bal u1 a

public export
record Transfer (tok : Token n m) (u1, u2 : Fi n) (a : N) (tok2 : ty tok) where
  constructor Transfered
  p : TransferPre tok u1 u2 a
  v2 : tok2.bal <<< Mint p.bal u2 a

  ub : (w : Fi n) -> (u1 = w -> Void) -> (u2 = w -> Void) -> tok2.ub w = tok.ub w
  ub1 : (u2 = u1 -> Void) -> tok2.ub u1 == tok.ub u1 - a
  ub2 : (u1 = u2 -> Void) -> tok2.ub u2 = tok.ub u2 + a

  ubr : (w : Fi n) -> (u1 = w -> Void) -> (u2 = w -> Void) -> tok2.ubr w = tok.ubr w
  ubr1 : (u2 = u1 -> Void) -> tok2.ubr u1 = tok.ubr u1 + a
  ubr2 : (u1 = u2 -> Void) -> tok2.ubr u2 == tok.ubr u2 - a

export
(.transfer) : {m : N} -> (tok : Token n m) -> (u1, u2 : Fi n) -> (a : N) -> (p : TransferPre tok u1 u2 a) -> (tok2 ** tok2 <<< Transfer tok u1 u2 a)
(.transfer) tok u1 u2 a p = let
  (bal2 ** v2) = p.bal.mint u2 a (Minting $ c21p .!> p.v1.rsa)
  ub' = \w, con1, con2 => ub ..> v2.ub w con2 ..> p.v1.ub w con1 .!> ub
  in (Tok bal2 ** Transfered p v2 ub' 
  (\u21 => x1Ap (ub ..> v2.ub _ u21) ..> p.v1.uba .!> ub)
  (\u12 => ub ..> v2.uba ..> xA1p (p.v1.ub _ u12 .!> ub))
  (\w, con1, con2 => 
    v1Ap (mub .!> xA1p (ub ..> v2.ub w con2 ..> p.v1.ub w con1 .!> ub) ..> mub)) (\con =>
    ubr ..> v2.ubr u1 con ..> p.v1.ubra .!> xA1p ubr) (\con => 
    x1Ap ubr ..> v2.ubra ..> p.v1.ubr u2 con .!> ubr))