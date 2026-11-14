/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedMiddleIteration
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedKStableNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedSplitExact

/-!
# Exact original middle rows after iterated independent Bass contraction

The actual coefficient restriction and independent-variable comparisons identify iterated
contraction of the original positive K-row with the native middle row of the iterated group
functor. Exactness follows from the two proved natural split rows and additivity of each iterate.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedMiddleIteration.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent KTheory.Bass.TwoChart
universe u w
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]
local notation "Bs" => contractionFunctor
  (NatTrans.op Scheme.Bass.pairPlus)
  (NatTrans.op Scheme.Bass.pairMinus)
local notation "Bu" => contractionFunctor (underToLaurent R) (underToLaurentInvert R)
local notation "Is" => iteratedContractionFunctor
  (NatTrans.op Scheme.Bass.pairPlus)
  (NatTrans.op Scheme.Bass.pairMinus)
local notation "Iu" => iteratedContractionFunctor (underToLaurent R) (underToLaurentInvert R)

/-- The original supported K-row is exactly the restricted native K-row under actual charts.
-/
def boundedAboveFlatCoefficientSupportedKRestrictedMiddleIso (n : ℕ) :
    boundedAboveFlatCoefficientSupportedMiddleSequence f (n : ℤ) ≅
      boundedAboveFlatCoefficientSupportedRestrictedMiddle f
        (Bass.supportedKFunctor n) := by
  unfold boundedAboveFlatCoefficientSupportedRestrictedMiddle
  exact (middleIso (polynomialUnderCoefficient R) (underToLaurent R)
    (underToLaurentInvert R) (boundedAboveFlatCoefficientSupportedCommonCorner (R := R))
    (boundedAboveFlatCoefficientSupportedKStableNatIso f n).symm) ≪≫
      boundedAboveFlatCoefficientSupportedMiddleTransportIso f (Bass.supportedKFunctor n)

variable [CompactSpace P.left] [QuasiSeparatedSpace Q.left]

/-- Iterated native middle rows of positive K-groups are exact on the actual qcqs ambient and
compact-open family. -/
theorem boundedAboveFlatCoefficientSupportedRestrictedMiddle_iteratedK_exact (n i : ℕ) :
    (boundedAboveFlatCoefficientSupportedRestrictedMiddle f
      ((Is i).obj (Bass.supportedKFunctor (n + 1)))).Exact :=
  ShortComplex.exact_of_iso
    ((Iu i).mapShortComplex.mapIso
      (boundedAboveFlatCoefficientSupportedKRestrictedMiddleIso f (n + 1)) ≪≫
      boundedAboveFlatCoefficientSupportedRestrictedMiddleIteratedIso f
        (Bass.supportedKFunctor (n + 1)) i)
    (boundedAboveFlatCoefficientSupportedMiddleSequence_map_exact f n (Iu i))

end AlgebraicGeometry.Scheme.Modules
