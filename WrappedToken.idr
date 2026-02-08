module WrappedToken

import Common
import Natural
import NaturalExt
import Token
import TokenExt

%default total

public export
record WrappedToken (n, m : N) (u0 : Fi n) (utok : Token n m) where
  constructor WrapTok
  {tok : Token n m}
  {d : N}
  don : d == utok.ub u0 - tok.ubr u0

export
(.ub) : WrappedToken n m u0 utok -> Fi n -> N
(.ub) wrapTok u = wrapTok.tok.ub u

export
ub : {wrapTok : WrappedToken n m u0 ttok} -> {u : Fi n} -> wrapTok.ub u = wrapTok.tok.ub u
ub = Refl