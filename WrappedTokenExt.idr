module WrappedTokenExt

import Common
import Natural
import NaturalExt
import Token
import TokenExt
import WrappedToken
import Balances

%default total

public export
record Deploy (n, m : N) (u0 : Fi n) (utok : Token n m) (wrapTok : WrappedToken n m u0 utok) where
  constructor Deployed
  vtok : wrapTok.tok <<< Deploy n m u0

export
deploy : (n, m : N) -> (u0 : Fi n) -> (utok : Token n m) -> (wrapTok ** wrapTok <<< Deploy n m u0 utok)
deploy n m u0 utok = let
  (tok ** vtok) = TokenExt.deploy n m u0
  in (WrapTok (xA1p vtok.ubr ..> tz1p) ** Deployed vtok)

export
record WrapPre (wrapTok : WrappedToken n m u0 utok1) (u : Fi n) (a : N) (utok2 : Token n m) where
  constructor Wrapping
  uu0 : u = u0 -> Void
  v1 : utok2 <<< Transfer utok1 u u0 a

public export
record Wrap (wrapTok : WrappedToken n m u0 utok1) (u : Fi n) (a : N) (utok2 : Token n m) (wrapTok2 : WrappedToken n m u0 utok2) where
  constructor Wrapped
  p : WrapPre wrapTok u a utok2
  v2 : wrapTok2.tok <<< Transfer wrapTok.tok u0 u a

export
(.wrap) : {m : N} -> {u0 : Fi n} -> {utok1, utok2 : Token n m} -> (wrapTok : WrappedToken n m u0 utok1) -> (u : Fi n) -> (a : N) -> 
  (p : WrapPre wrapTok u a utok2) -> (wrapTok2 ** wrapTok2 <<< Wrap wrapTok u a utok2)
(.wrap) wrapTok u a p = let
  don0 = xA1p wrapTok.don ..> (sym $ p.v1.ub2 p.uu0)
  uba = vA1p $ c143pp2p ..> c21p3p ..> xA1p don0 ..> mub .!> mub
  (bal ** vbal) = wrapTok.tok.bal.burn u0 a (Burning $ uba ..> ub {tok=wrapTok.tok})
  (tok ** vtok) = wrapTok.tok.transfer u0 u a (Transferring vbal)
  don = xA1p (vtok.ubr1 p.uu0) ..> c13p2p ..> don0
  in (WrapTok don ** Wrapped p vtok)

export
record TransferPre (wrapTok : WrappedToken n m u0 utok) (u1, u2 : Fi n) (a : N) where
  constructor Transfering
  {tok : Token n m}
  u10 : u1 = u0 -> Void
  v1 : tok <<< Transfer wrapTok.tok u1 u2 a

export
record Transfer (wrapTok : WrappedToken n m u0 utok) (u1, u2 : Fi n) (a : N) (wrapTok2 : ty wrapTok) where
  constructor Transfered
  p : TransferPre wrapTok u1 u2 a
  tok : wrapTok2.tok = p.tok

export
(.transfer) : {m : N} -> {u0 : Fi n} -> {utok : Token n m} -> (wrapTok : WrappedToken n m u0 utok) -> (u1, u2 : Fi n) -> (a : N) -> 
  (p : TransferPre wrapTok u1 u2 a) -> (wrapTok2 ** wrapTok2 <<< Transfer wrapTok u1 u2 a)
(.transfer) wrapTok u1 u2 a p with (fiEq u2 u0)
  (.transfer) wrapTok u1 u2 a p | Yes Refl with (fiEq u1 u2)
    (.transfer) wrapTok u1 u1 a p | Yes Refl | Yes Refl = void $ p.u10 Refl
    (.transfer) wrapTok u1 u2 a p | Yes Refl | No contra = (WrapTok (aP !.> xA1p (c21p ..> p.v1.ubr2 p.u10) ..> wrapTok.don) ** Transfered p Refl)
  (.transfer) wrapTok u1 u2 a p | No contra = (WrapTok (xA1p (p.v1.ubr u0 p.u10 contra) ..> wrapTok.don) ** Transfered p Refl)

export
record ExtTransferPre (wrapTok : WrappedToken n m u0 utok) (u1, u2 : Fi n) (a : N) (utok2 : Token n m) where
  constructor ExtTransfering
  u10 : u1 = u0 -> Void
  v1 : utok2 <<< Transfer utok u1 u2 a

export
record ExtTransfer (wrapTok : WrappedToken n m u0 utok) (u1, u2 : Fi n) (a : N) (utok2 : Token n m) (wrapTok2 : WrappedToken n m u0 utok2) where
  constructor ExtTransfered
  p : ExtTransferPre wrapTok u1 u2 a utok2

export
(.extTransfer) : {m : N} -> {u0 : Fi n} -> {utok, utok2 : Token n m} -> (wrapTok : WrappedToken n m u0 utok) -> (u1, u2 : Fi n) -> (a : N) -> 
  (p : ExtTransferPre wrapTok u1 u2 a utok2) -> (wrapTok2 ** wrapTok2 <<< ExtTransfer wrapTok u1 u2 a utok2)
(.extTransfer) wrapTok u1 u2 a p with (fiEq u2 u0)
  (.extTransfer) wrapTok u1 u2 a p | Yes Refl = (WrapTok (aP !.> xA1p wrapTok.don .!> p.v1.ub2 p.u10) ** ExtTransfered p)
  (.extTransfer) wrapTok u1 u2 a p | No contra = (WrapTok (wrapTok.don .!> p.v1.ub u0 p.u10 contra) ** ExtTransfered p)

export
record UnwrapPre (wrapTok : WrappedToken n m u0 utok1) (u : Fi n) (a : N) where
  constructor Unwrapping
  uu0 : u = u0 -> Void
  {tok : Token n m}
  v1 : tok <<< Transfer wrapTok.tok u u0 a

public export
record Unwrap (wrapTok : WrappedToken n m u0 utok1) (u : Fi n) (a : N) (utok2 : Token n m) (wrapTok2 : WrappedToken n m u0 utok2) where
  constructor Unwrapped
  p : UnwrapPre wrapTok u a
  v2 : utok2 <<< Transfer utok1 u0 u a

export
(.unwrap) : {m : N} -> {u0 : Fi n} -> {utok1, utok2 : Token n m} -> (wrapTok : WrappedToken n m u0 utok1) -> (u : Fi n) -> (a : N) -> 
  (p : UnwrapPre wrapTok u a) -> (utok2 ** wrapTok2 ** wrapTok2 <<< Unwrap wrapTok u a utok2)
(.unwrap) wrapTok u a p = let
  uba = aP !.> xA1p (p.v1.ubr2 p.uu0) ..> wrapTok.don ..> ub {tok = utok1}
  (bal ** vbal) = utok1.bal.burn u0 a (Burning uba)
  (utok2 ** vutok2) = utok1.transfer u0 u a (Transferring vbal)
  don = v1Ap $ aP !.> xA1p (p.v1.ubr2 p.uu0) ..> wrapTok.don .!> vutok2.ub1 p.uu0
  in (utok2 ** WrapTok don ** Unwrapped p vutok2)