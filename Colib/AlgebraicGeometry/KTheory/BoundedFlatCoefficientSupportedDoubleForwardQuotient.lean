/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedUnitQuotient
public import Colib.KTheory.Bass.TwoChartDoubleDescent

/-!
# Two original supported forward-unit quotients

The original supported stable forward-unit quotient followed by its contracted
successor is represented by the two unchanged supported Laurent-track operations
and the two original cokernel projections. Its nonnegative components are
isomorphisms when the ambient scheme is qcqs and the removed open is compact.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedDoubleForwardQuotient.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry CommRingCat.PolynomialLaurent
open KTheory.Bass.TwoChart Topology Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The two unchanged coefficient-supported stable Laurent operations before quotienting. -/
def boundedAboveFlatCoefficientSupportedDoubleForwardUnitMap (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).obj
        (prespectrum ((boundedAboveFlatCoefficientSupportedModelFunctor f).obj a)) ⟶
      (stableHomotopyFunctor ((d + 1) + 1)).obj
        (prespectrum ((boundedAboveFlatCoefficientSupportedModelFunctor f).obj
          ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)))) :=
  ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy a).stableOperation d ≫
    ((boundedAboveFlatCoefficientSupportedLaurentAction f).track.homotopy
      ((laurentUnderFunctor R).obj a)).stableOperation (d + 1)

/-- The original supported forward quotient followed by its contracted successor. -/
def boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient (d : ℤ) :=
  boundedAboveFlatCoefficientSupportedForwardUnitQuotient f d ≫
    (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).map
      (boundedAboveFlatCoefficientSupportedForwardUnitQuotient f (d + 1))

/-- Both original quotient projections retain the two actual supported track operations. -/
theorem boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient_representative
    (a : Under R) (d : ℤ) :
    (boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient f d).app a =
      boundedAboveFlatCoefficientSupportedDoubleForwardUnitMap f a d ≫
        doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
          ((boundedAboveFlatCoefficientSupportedModelFunctor f ⋙ prespectrumFunctor) ⋙
            stableHomotopyFunctor ((d + 1) + 1)) a := by
  simp only [boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient, NatTrans.comp_app,
    boundedAboveFlatCoefficientSupportedForwardUnitQuotient,
    KTheory.Bass.LaurentSeed.Track.stableUnitQuotient,
    KTheory.Bass.LaurentSeed.Track.stableOperationNatTrans,
    boundedAboveFlatCoefficientSupportedDoubleForwardUnitMap,
    contractionFunctor, doubleContractionπ, Category.assoc, contractionMap_π]

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The two actual supported positive Bass isomorphisms remain invertible after composition. -/
instance boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient_isIso (n : ℕ) :
    IsIso (boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient f (n : ℤ)) := by
  have : IsIso (boundedAboveFlatCoefficientSupportedForwardUnitQuotient f ((n : ℤ) + 1)) := by
    simpa only [Int.natCast_add, Int.natCast_one] using
      boundedAboveFlatCoefficientSupportedForwardUnitQuotient_isIso f (n + 1)
  unfold boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient
  infer_instance

/-- The supported double comparison is invertible on every actual coefficient fiber. -/
instance boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient_app_isIso
    (a : Under R) (n : ℕ) :
    IsIso ((boundedAboveFlatCoefficientSupportedDoubleForwardUnitQuotient f (n : ℤ)).app a) :=
  inferInstance

end AlgebraicGeometry.Scheme.Modules
