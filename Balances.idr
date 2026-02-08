module Balances

import Common
import Natural
import NaturalExt

%default total

mutual
  export
  data Balances : (n, m : N) -> Type where
    Bal : Balances Z m
    (::) : (bal : Balances n m) -> (acc : UserBalance bal) -> Balances (S n) m

  export
  record UserBalance (t : Balances n m) where
    constructor UserBal
    {b, r : N}
    rsb : r == t.rs - b

  export
  (.rs) : {m : N} -> Balances n m -> N
  (.rs) Bal = m
  (.rs) (t :: acc) = acc.r

export
(.ub) : Balances n m -> Fi n -> N
(.ub) (t :: acc) FZ = acc.b
(.ub) (t :: acc) (FS u) = t.ub u

export
(.tb) : Balances n m -> N
(.tb) Bal = Z
(.tb) (bal :: acc) = bal.tb + acc.b

export
(.ubr) : Balances n m -> (u : Fi n) -> N
(.ubr) (bal :: acc) FZ = bal.tb + acc.r
(.ubr) (bal :: acc) (FS u) = bal.ubr u

export
(.mtb) : {m : N} -> (bal : Balances n m) -> bal.rs == m - bal.tb
(.mtb) {bal = Bal} = tz1p
(.mtb) {bal = bal :: acc} = aP ..> x1Ap acc.rsb ..> bal.mtb

export
(.mub) : {m : N} -> (bal : Balances n m) -> {u : Fi n} -> bal.ubr u == m - bal.ub u
(.mub) {bal = bal :: acc, u = FZ} = c213pp ..> x1Ap acc.rsb ..> bal.mtb
(.mub) {bal = bal :: acc, u = FS u} = bal.mub

public export
record Deploy (n, m : N) (bal : Balances n m) where
  constructor Deployed
  rs : bal.rs = m
  ub : (u : Fi n) -> bal.ub u = Z
  
  ubr : (u : Fi n) -> bal.ubr u = m

export
deploy : (n, m : N) -> (bal ** bal <<< Deploy n m)
deploy Z m = (Bal ** Deployed Refl (\w => fiVoid w) (\w => fiVoid w))
deploy (S n) m = let
  (bal ** vbal) = deploy n m
  in (bal :: UserBal tz1p ** Deployed vbal.rs (\w => case w of
    FZ => Refl
    FS w => vbal.ub w) (\w => case w of
    FZ => bal.mtb
    FS w => vbal.ubr w))

public export
record MintPre (bal : Balances n m) (u : Fi n) (a : N) where
  constructor Minting
  {x : N}
  rsa : x == (a <= bal.rs)

public export
record Mint (bal : Balances n m) (u : Fi n) (a : N) (bal2 : ty bal) where
  constructor Minted
  p : MintPre bal u a
  rsx : bal2.rs = p.x
  uba : bal2.ub u = bal.ub u + a
  ub : (w : Fi n) -> (u = w -> Void) -> bal2.ub w = bal.ub w

  ubra : bal2.ubr u == bal.ubr u - a
  ubr : (w : Fi n) -> (u = w -> Void) -> bal2.ubr w = bal.ubr w
  tba : bal2.tb = bal.tb + a

export
(.mint) : {m : N} -> (bal : Balances n m) -> (u : Fi n) -> (a : N) -> (p : MintPre bal u a) -> (bal2 ** bal2 <<< Mint bal u a)
(.mint) (bal :: acc) FZ a p = let
  rsb = aP ..> x1Ap p.rsa ..> acc.rsb
  in (bal :: UserBal rsb ** Minted p Refl Refl (\w, uw => case w of
    FZ => void $ uw Refl
    FS w => Refl) (c213pp ..> x1Ap p.rsa) (\w, uw => case w of
    FZ => void $ uw Refl
    FS w => Refl) (sym aP))
(.mint) (bal :: acc) (FS u) a p = let
  rsa = c213pp ..> x1Ap p.rsa ..> acc.rsb
  (bal2 ** vbal2) = bal.mint u a (Minting rsa)
  rsb = v1Ap (rsa .!> vbal2.p.rsa) .!> vbal2.rsx
  in (bal2 :: UserBal rsb ** Minted p Refl vbal2.uba (\w, uw => case w of
    FZ => Refl
    FS w => vbal2.ub w $ fiContra4 uw) vbal2.ubra (\w, uw => case w of
    FZ => xA1p vbal2.tba ..> aP ..> x1Ap p.rsa
    FS w => vbal2.ubr w $ fiContra4 uw) (xA1p vbal2.tba ..> c13p2p))

public export
record BurnPre (bal : Balances n m) (u : Fi n) (a : N) where
  constructor Burning
  {x : N}
  uba : x == (a <= bal.ub u)

public export
record Burn (bal : Balances n m) (u : Fi n) (a : N) (bal2 : ty bal) where
  constructor Burned
  p : BurnPre bal u a
  rsa : bal2.rs = bal.rs + a
  ubx : bal2.ub u = p.x
  ub : (w : Fi n) -> (u = w -> Void) -> bal2.ub w = bal.ub w

  uba : bal2.ub u == bal.ub u - a
  ubra : bal2.ubr u = bal.ubr u + a
  ubr : (w : Fi n) -> (u = w -> Void) -> bal2.ubr w = bal.ubr w
  tba : bal2.tb == bal.tb - a

export
(.burn) : {m : N} -> (bal : Balances n m) -> (u : Fi n) -> (a : N) -> (p : BurnPre bal u a) -> (bal2 ** bal2 <<< Burn bal u a)
(.burn) (bal :: acc) FZ a p = (bal :: UserBal (aP !.> c21p3p ..> xA1p p.uba ..> acc.rsb) ** Burned p c21p Refl (\w, uw => case w of
  FZ => void $ uw Refl
  FS w => Refl) p.uba (aP !.> c13p2p) (\w, uw => case w of
  FZ => void $ uw Refl
  FS w => Refl) (c213pp ..> x1Ap p.uba))
(.burn) (bal :: acc) (FS u) a p = let
  (bal2 ** vbal2) = bal.burn u a (Burning p.uba)
  ubx = vbal2.ubx ..> v1Ap (vbal2.p.uba .!> p.uba)
  in (bal2 :: UserBal (aP !.> xA1p acc.rsb .!> vbal2.rsa) ** Burned p Refl ubx (\w, uw => case w of
    FZ => Refl
    FS w => vbal2.ub w $ fiContra4 uw) (x1Ap ubx ..> p.uba) vbal2.ubra (\w, uw => case w of
    FZ => c231pp ..> x1Ap vbal2.tba ..> c21p
    FS w => vbal2.ubr w $ fiContra4 uw) (c312pp ..> x1Ap vbal2.tba ..> c21p))