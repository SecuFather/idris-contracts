module Token

import Common
import Natural
import NaturalExt
import Balances

%default total

public export
record Token (n, m : N) where
  constructor Tok
  bal : Balances n m

export
(.ub) : Token n m -> Fi n -> N
(.ub) tok u = tok.bal.ub u

export
(.ubr) : Token n m -> (u : Fi n) -> N
(.ubr) tok u = tok.bal.ubr u

export
ub : {tok : Token n m} -> {u : Fi n} -> tok.ub u = tok.bal.ub u
ub = Refl

export
ubr : {tok : Token n m} -> {u : Fi n} -> tok.ubr u = tok.bal.ubr u
ubr = Refl


