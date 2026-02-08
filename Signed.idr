module Signed

import Common
import Natural

%default total

export
(.inc) : X -> N -> X
(.inc) (Xn x) Z = Xn x
(.inc) (Xn Z) (S y) = Xp y
(.inc) (Xn (S x)) (S y) = (Xn x).inc y
(.inc) (Xp x) n = Xp (x + n)

export
(.dec) : X -> N -> X
(.dec) (Xp x) Z = Xp x
(.dec) (Xp Z) (S y) = Xn y
(.dec) (Xp (S x)) (S y) = (Xp x).dec y
(.dec) (Xn x) n = Xn (x + n)

export
(+) : (x1, x2 : X) -> X
(+) (Xn x) x2 = x2.dec (S x)
(+) (Xp x) x2 = x2.inc x

export
(.x) : N -> X
(.x) x = Xp x

export
(.inv) : X -> X
(.inv) (Xn x) = Xp (S x)
(.inv) (Xp Z) = Xp Z
(.inv) (Xp (S x)) = Xn x

export
t1zp : {x1 : X} -> x1 + (Z).x = x1
t1zp {x1 = Xn x} = Refl
t1zp {x1 = Xp x} = cong Xp tz1p

export
t11ip : {x1 : X} -> x1 + x1.inv = (Z).x
t11ip {x1 = Xn x} = p x where
  p : (x2 : N) -> (Xp x2).dec x2 = Xp Z
  p Z = Refl
  p (S x2) = p x2
t11ip {x1 = Xp Z} = cong Xp t1zp
t11ip {x1 = Xp (S x)} = p x where
  p : (x2 : N) -> (Xn x2).inc (S x2) = Xp Z
  p Z = Refl
  p (S x2) = p x2

export
(..>) : {x1, x2, x3 : X} -> x1 = x2 -> x2 = x3 -> x1 = x3
(..>) Refl Refl = Refl