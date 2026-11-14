/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedMiddleIterationExact

/-!
# Exact original supported negative middle rows

The original supported K-zero comparison and the actual inverse-unit quotient identify K-zero
with one contraction of the original supported K-one pair functor. Iterating the same original
pair contraction and its coefficient transport identifies every original supported Bass group
with the corresponding K-one iterate. The two constructed split rows and actual independent
pair-variable interchange then give middle exactness. The ambient scheme is qcqs and the
removed open is compact; no supported localization theorem is inferred from ambient groups.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedNegativeMiddleExactness.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent KTheory.Bass.TwoChart Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]
local notation "Ip" => iteratedContractionFunctor
  (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op Scheme.Bass.pairMinus)
local notation "Bu" => contractionFunctor (underToLaurent R) (underToLaurentInvert R)
local notation "K1" => Bass.supportedKFunctor 1

/-- Original supported K-zero is one actual contraction of original supported K-one. -/
def boundedAboveFlatCoefficientSupportedKZeroContractionIso :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKZeroFunctor ≅
      boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ (Ip 1).obj K1 := by
  let : IsIso (boundedAboveFlatCoefficientSupportedInverseUnitQuotient f 0) :=
    boundedAboveFlatCoefficientSupportedInverseUnitQuotient_isIso f 0
  exact boundedAboveFlatCoefficientSupportedBassBottomZeroNatIso f ≪≫
    asIso (boundedAboveFlatCoefficientSupportedInverseUnitQuotient f 0) ≪≫
      (Bu).mapIso (boundedAboveFlatCoefficientSupportedKStableNatIso f 1).symm ≪≫
        boundedAboveFlatCoefficientSupportedContractionTransportIso f K1

/-- Every original supported negative group retains its actual iterated K-one presentation. -/
def boundedAboveFlatCoefficientSupportedNegativeIteratedKOneIso :
    (i : ℕ) → boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙
        Bass.supportedNegativeKFunctor i ≅
      boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ (Ip (i + 1)).obj K1
  | 0 => boundedAboveFlatCoefficientSupportedKZeroContractionIso f
  | i + 1 =>
    (boundedAboveFlatCoefficientSupportedContractionTransportIso f
      (Bass.supportedNegativeKFunctor i)).symm ≪≫
      (Bu).mapIso (boundedAboveFlatCoefficientSupportedNegativeIteratedKOneIso i) ≪≫
        boundedAboveFlatCoefficientSupportedContractionTransportIso f ((Ip (i + 1)).obj K1)

/-- The original supported common-corner and signed difference row is exact in every negative
Bass degree on the actual coefficient pair family. -/
theorem boundedAboveFlatCoefficientSupportedNegativeMiddle_exact (i : ℕ) :
    (middleComplex (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedAboveFlatCoefficientSupportedCommonCorner (R := R))
      (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙
        Bass.supportedNegativeKFunctor i)).Exact :=
  ShortComplex.exact_of_iso
    ((middleIso (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedAboveFlatCoefficientSupportedCommonCorner (R := R))
      (boundedAboveFlatCoefficientSupportedNegativeIteratedKOneIso f i)) ≪≫
        boundedAboveFlatCoefficientSupportedMiddleTransportIso f ((Ip (i + 1)).obj K1)).symm
    (boundedAboveFlatCoefficientSupportedRestrictedMiddle_iteratedK_exact f 0 (i + 1))

end AlgebraicGeometry.Scheme.Modules
