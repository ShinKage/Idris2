module Algebra.ZeroOneOmega

import Decidable.Equality

import Algebra.Semiring
import Algebra.Preorder

%default total

public export
data ZeroOneOmega = Rig0 | Rig1 | RigW

data LTEZeroOneOmega : ZeroOneOmega -> ZeroOneOmega -> Type where
  LTEZero : LTEZeroOneOmega Rig0 y
  LTEOneOne : LTEZeroOneOmega Rig1 Rig1
  LTEOneOmega : LTEZeroOneOmega Rig1 RigW
  LTEOmegaOmega : LTEZeroOneOmega RigW RigW

Uninhabited (LTEZeroOneOmega Rig1 Rig0) where
  uninhabited LTEZero impossible
  uninhabited LTEOneOne impossible
  uninhabited LTEOneOmega impossible
  uninhabited LTEOmegaOmega impossible

Uninhabited (LTEZeroOneOmega RigW Rig0) where
  uninhabited LTEZero impossible
  uninhabited LTEOneOne impossible
  uninhabited LTEOneOmega impossible
  uninhabited LTEOmegaOmega impossible

Uninhabited (LTEZeroOneOmega RigW Rig1) where
  uninhabited LTEZero impossible
  uninhabited LTEOneOne impossible
  uninhabited LTEOneOmega impossible
  uninhabited LTEOmegaOmega impossible

export
Preorder ZeroOneOmega where
  LTE = LTEZeroOneOmega

  isLTE Rig0 y = Yes LTEZero
  isLTE Rig1 Rig0 = No uninhabited
  isLTE Rig1 Rig1 = Yes LTEOneOne
  isLTE Rig1 RigW = Yes LTEOneOmega
  isLTE RigW Rig0 = No uninhabited
  isLTE RigW Rig1 = No uninhabited
  isLTE RigW RigW = Yes LTEOmegaOmega

  preorderRefl Rig0 = LTEZero
  preorderRefl Rig1 = LTEOneOne
  preorderRefl RigW = LTEOmegaOmega

  preorderTrans LTEZero y = LTEZero
  preorderTrans LTEOneOne LTEOneOne = LTEOneOne
  preorderTrans LTEOneOne LTEOneOmega = LTEOneOmega
  preorderTrans LTEOneOmega LTEOmegaOmega = LTEOneOmega
  preorderTrans LTEOmegaOmega LTEOmegaOmega = LTEOmegaOmega

public export
Eq ZeroOneOmega where
  (==) Rig0 Rig0 = True
  (==) Rig1 Rig1 = True
  (==) RigW RigW = True
  (==) _ _ = False

public export
DecEq ZeroOneOmega where
  decEq Rig0 Rig0 = Yes Refl
  decEq Rig0 Rig1 = No (\case Refl impossible)
  decEq Rig0 RigW = No (\case Refl impossible)
  decEq Rig1 Rig0 = No (\case Refl impossible)
  decEq Rig1 Rig1 = Yes Refl
  decEq Rig1 RigW = No (\case Refl impossible)
  decEq RigW Rig0 = No (\case Refl impossible)
  decEq RigW Rig1 = No (\case Refl impossible)
  decEq RigW RigW = Yes Refl

export
Show ZeroOneOmega where
  show Rig0 = "Rig0"
  show Rig1 = "Rig1"
  show RigW = "RigW"

export
rigPlus : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigPlus Rig0 a = a
rigPlus a Rig0 = a
rigPlus Rig1 a = RigW
rigPlus a Rig1 = RigW
rigPlus RigW RigW = RigW

export
rigMult : ZeroOneOmega -> ZeroOneOmega -> ZeroOneOmega
rigMult Rig0 _ = Rig0
rigMult _ Rig0 = Rig0
rigMult Rig1 a = a
rigMult a Rig1 = a
rigMult RigW RigW = RigW

public export
Semiring ZeroOneOmega where
  (|+|) = rigPlus
  (|*|) = rigMult
  plusNeutral = Rig0
  timesNeutral = Rig1

||| The top value of a lattice
export
Top ZeroOneOmega where
  top = RigW

  topAbs Rig0 = LTEZero
  topAbs Rig1 = LTEOneOmega
  topAbs RigW = LTEOmegaOmega
