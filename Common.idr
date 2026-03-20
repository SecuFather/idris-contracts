module Common

%default total

export infixr 5 ..>, !.>, .!>, !!>, <<<
export infixl 8 |+|

public export
data N = Z | S N

public export
data Fi : N -> Type where
  FZ : Fi (S n)
  FS : Fi n -> Fi (S n)

public export
data F : Type where
  Fr : (x, y : N) -> {y0 : N} -> y = S y0 -> F

public export
data SF : F -> Type where
  SFr : {x0, y0 : N} -> (p : x = S x0) -> {q : y = S y0} -> SF (Fr x y q)

public export
data X = Xn N | Xp N

public export
(<<<) : {a : Type} -> a -> (a -> Type) -> Type
(<<<) x f = f x

public export
ty : {a : Type} -> (_ : a) -> Type
ty x = a

export
fiVoid : Fi Z -> a
fiVoid FZ impossible
fiVoid (FS _) impossible

export
fiContra1 : FZ = FS x -> Void
fiContra1 Refl impossible

export
fiContra2 : FS x = FZ -> Void
fiContra2 Refl impossible

export
fiContra3 : (x = y -> Void) -> FS x = FS y -> Void
fiContra3 f Refl = f Refl

export
fiContra4 : (FS x = FS y -> Void) -> x = y -> Void
fiContra4 f Refl = f Refl

export
fiEq : (f1, f2 : Fi n) -> Dec (f1 = f2)
fiEq FZ FZ = Yes Refl
fiEq FZ (FS x) = No fiContra1
fiEq (FS x) FZ = No fiContra2
fiEq (FS x) (FS y) = case fiEq x y of
  Yes prf => Yes (cong FS prf)
  No contra => No (fiContra3 contra)

export
c21v : (x1 = x2 -> Void) -> x2 = x1 -> Void
c21v f p = f $ sym p