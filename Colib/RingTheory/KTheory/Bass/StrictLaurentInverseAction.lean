/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.RingTheory.KTheory.Bass.StrictLaurentUnitQuotient
public import Colib.KTheory.Waldhausen.Iterated.ModelSelfTrackStableOperation

/-!
# The actual inverse Laurent Model action

Invert the specified identity automorphisms on the original Laurent Models, retaining their
coefficient-preservation equations. The original Model composition triangle proves that this
actual inverse action has the negative stable operation and the negative original quotient.
The inverse operation is constructed geometrically before its algebraic sign is identified.

Source: `Quillen/KTheory/Bass/StrictLaurentInverseAction.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.LaurentSeed
variable {R : CommRingCat.{u}} {C : Under R ⥤ WideSubcategory preservesZero.{w}} (A : ModelAction C)

/-- The inverse of the same specified Laurent unit, with its original coefficient functors. -/
def ModelAction.symm : ModelAction C where
  unit a := (A.unit a).symm
  naturality {a b} g x := map_inv_app_eq
    (C.map ((laurentUnderFunctor R).map g)).hom.toFunctor (A.unit a) (A.unit b) x
      (A.naturality g x)

/-- The actual inverse unit track induces the negative original degree-raising operation. -/
theorem ModelAction.symm_stableOperation (a : Under R) (d : ℤ) :
    (A.symm.track.homotopy a).stableOperation d =
      -(A.track.homotopy a).stableOperation d :=
  prespectrumIsoHomotopy_stableOperation_symm
    (C.map ((laurentUnderCoefficient R).app a))
    (onFunctor (C.map ((laurentUnderCoefficient R).app a)).hom.toFunctor (A.unit a)) d

/-- The whole original inverse-unit operation is the negative natural forward operation. -/
theorem ModelAction.symm_stableOperationNatTrans (d : ℤ) :
    A.symm.track.stableOperationNatTrans d = -A.track.stableOperationNatTrans d := by
  apply NatTrans.ext
  funext a
  exact A.symm_stableOperation a d

/-- The actual inverse unit uses the same original quotient and induces its negative. -/
theorem ModelAction.symm_stableUnitQuotient (d : ℤ) :
    A.symm.track.stableUnitQuotient d = -A.track.stableUnitQuotient d := by
  rw [Track.stableUnitQuotient, A.symm_stableOperationNatTrans, Preadditive.neg_comp]
  rfl

/-- Invertibility of the original forward quotient implies invertibility of the actual inverse
unit quotient, with no choice of a replacement operation. -/
theorem ModelAction.symm_stableUnitQuotient_isIso (d : ℤ)
    [IsIso (A.track.stableUnitQuotient d)] :
    IsIso (A.symm.track.stableUnitQuotient d) := by
  rw [A.symm_stableUnitQuotient]
  change IsIso (-(asIso (A.track.stableUnitQuotient d))).hom
  infer_instance

end KTheory.Bass.LaurentSeed
