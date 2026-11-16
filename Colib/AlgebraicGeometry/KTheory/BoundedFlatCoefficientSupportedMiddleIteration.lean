/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedMiddleTransport
public import Colib.KTheory.Bass.TwoChartIteration

/-!
# Exact original middle rows after iterated independent Bass contraction

The actual coefficient restriction and independent-variable comparisons identify iterated
contraction of the original positive K-row with the native middle row of the iterated group
functor. This provides the genuine iterated comparison used by the positive exact row.

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

/-- The original native pair middle row on the actual coefficient family. -/
def boundedAboveFlatCoefficientSupportedRestrictedMiddle
    (F : Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    ShortComplex (Under R ⥤ AddCommGrpCat.{w}) :=
  (Scheme.Bass.pairBassMiddleComplex F).map
    ((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
      AddCommGrpCat.{w}).obj (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f))

/-- Actual restriction and independent-variable transport commute on the whole middle row. -/
def boundedAboveFlatCoefficientSupportedRestrictedMiddleContractionIso
    (F : Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) :
    (boundedAboveFlatCoefficientSupportedRestrictedMiddle f F).map Bu ≅
      boundedAboveFlatCoefficientSupportedRestrictedMiddle f ((Bs).obj F) :=
  boundedAboveFlatCoefficientSupportedContractionShortComplexIso f
    (Scheme.Bass.pairBassMiddleComplex F) ≪≫
      (((Functor.whiskeringLeft (Under R) Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ
        AddCommGrpCat.{w}).obj
          (boundedAboveFlatCoefficientQuasiCompactOpenPairRow f)).mapShortComplex.mapIso
          (Scheme.Bass.pairContractionBassMiddleIso F))

attribute [local irreducible] boundedAboveFlatCoefficientSupportedRestrictedMiddle

/-- The same actual whole-row comparison iterates with the original contraction functors. -/
def boundedAboveFlatCoefficientSupportedRestrictedMiddleIteratedIso
    (F : Scheme.QuasiCompactOpenPairs.{u}ᵒᵖ ⥤ AddCommGrpCat.{w}) (i : ℕ) :
    (boundedAboveFlatCoefficientSupportedRestrictedMiddle f F).map (Iu i) ≅
      boundedAboveFlatCoefficientSupportedRestrictedMiddle f ((Is i).obj F) :=
  match i with
  | 0 => Iso.refl _
  | i + 1 => by
      change ((boundedAboveFlatCoefficientSupportedRestrictedMiddle f F).map (Iu i)).map Bu ≅
        boundedAboveFlatCoefficientSupportedRestrictedMiddle f ((Bs).obj ((Is i).obj F))
      exact (Bu).mapShortComplex.mapIso
        (boundedAboveFlatCoefficientSupportedRestrictedMiddleIteratedIso F i) ≪≫
          boundedAboveFlatCoefficientSupportedRestrictedMiddleContractionIso f ((Is i).obj F)

end AlgebraicGeometry.Scheme.Modules
