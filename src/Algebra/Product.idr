module Algebra.Product

import Algebra.Semiring
import Algebra.Preorder

%default total

data LTEProduct : (Preorder a, Preorder b) => (a, b) -> (a, b) -> Type where
  IsLTE : (Preorder a, Preorder b) => {0 a1, a2 : a} -> {0 b1, b2 : b} -> LTE a1 a2 -> LTE b1 b2 -> LTEProduct (a1, b1) (a2, b2)

public export
(Preorder a, Preorder b) => Preorder (a, b) where
  LTE = LTEProduct

  isLTE (x1, y1) (x2, y2) with (isLTE x1 x2, isLTE y1 y2)
    isLTE (x1, y1) (x2, y2) | (Yes prf1, Yes prf2) = Yes (IsLTE prf1 prf2)
    isLTE (x1, y1) (x2, y2) | (Yes prf1, No contra2) = No (\(IsLTE p1 p2) => contra2 p2)
    isLTE (x1, y1) (x2, y2) | (No contra1, Yes prf2) = No (\(IsLTE p1 p2) => contra1 p1)
    isLTE (x1, y1) (x2, y2) | (No contra1, No contra2) = No (\(IsLTE p1 p2) => contra1 p1)

  preorderRefl (x, y) = IsLTE (preorderRefl x) (preorderRefl y)

  preorderTrans (IsLTE x1 y1) (IsLTE x2 y2) = IsLTE (preorderTrans x1 x2) (preorderTrans y1 y2)

export
rigPlus : (Semiring a, Semiring b) => (a, b) -> (a, b) -> (a, b)
rigPlus (x1, y1) (x2, y2) = (x1 |+| x2, y1 |+| y2)

export
rigMult : (Semiring a, Semiring b) => (a, b) -> (a, b) -> (a, b)
rigMult (x1, y1) (x2, y2) = (x1 |*| x2, y1 |*| y2)

public export
(Semiring a, Semiring b) => Semiring (a, b) where
  (|+|) = rigPlus
  (|*|) = rigMult
  plusNeutral = (plusNeutral, plusNeutral)
  timesNeutral = (timesNeutral, timesNeutral)

||| The top value of a lattice
export
(Top a, Top b) => Top (a, b) where
  top = (top, top)

  topAbs (x, y) = IsLTE (topAbs x) (topAbs y)
