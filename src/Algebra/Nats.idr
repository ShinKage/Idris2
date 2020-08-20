module Algebra.Nats

import Data.Nat

import Algebra.Semiring
import Algebra.Preorder

%default total

public export
data InfNat = N Nat | Infinity

public export
data LTEInfNat : InfNat -> InfNat -> Type where
  LTENat : Nat.LTE n m -> LTEInfNat (N n) (N m)
  LTEInf : LTEInfNat n Infinity

export
Uninhabited (LTEInfNat Infinity (N n)) where
  uninhabited (LTENat x) impossible
  uninhabited LTEInf impossible

public export
Preorder InfNat where
  LTE = LTEInfNat

  isLTE x Infinity = Yes LTEInf
  isLTE (N n) (N m) = case isLTE n m of
                           Yes prf => Yes (LTENat prf)
                           No contra => No (\(LTENat prf) => contra prf)
  isLTE Infinity (N n) = No uninhabited

  preorderRefl (N k) = LTENat lteRefl
  preorderRefl Infinity = LTEInf

  preorderTrans (LTENat x) (LTENat y) = LTENat (lteTransitive x y)
  preorderTrans (LTENat x) LTEInf = LTEInf
  preorderTrans LTEInf LTEInf = LTEInf

public export
Eq InfNat where
  (==) (N n) (N m) = n == m
  (==) Infinity Infinity = True
  (==) _ _ = False

public export
natInjective : N n = N m -> n = m
natInjective Refl = Refl

public export
DecEq InfNat where
  decEq (N n) (N m) = case decEq n m of
                           Yes prf => Yes (rewrite prf in Refl)
                           No contra => No (\prf => contra (natInjective prf))
  decEq (N n) Infinity = No (\case Refl impossible)
  decEq Infinity (N m) = No (\case Refl impossible)
  decEq Infinity Infinity = Yes Refl

export
Show InfNat where
  show (N n) = show n
  show Infinity = "∞"

export
rigPlus : InfNat -> InfNat -> InfNat
rigPlus (N n) (N m) = N (n + m)
rigPlus Infinity _ = Infinity
rigPlus _ Infinity = Infinity

export
rigMult : InfNat -> InfNat -> InfNat
rigMult (N 0) _ = N 0
rigMult _ (N 0) = N 0
rigMult (N n) (N m) = N (n * m)
rigMult Infinity _ = Infinity
rigMult _ Infinity = Infinity

public export
Semiring InfNat where
  (|+|) = rigPlus
  (|*|) = rigMult
  plusNeutral = N 0
  timesNeutral = N 1

||| The top value of a lattice
export
Top InfNat where
  top = Infinity

  topAbs x = LTEInf
