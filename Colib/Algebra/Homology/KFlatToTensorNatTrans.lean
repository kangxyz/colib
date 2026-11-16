/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Homology.KFlat.BifunctorToTotalComplex

/-! # The original derived-to-total morphism as a two-variable transformation

The components are exactly native `KFlatBifunctor.toTensor`, with no alteration
of resolutions, derived category model, or tensor object.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ),
    HomologicalComplex.HasMapBifunctor K L F (.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]
  (hres : ∀ G : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (f : P ⟶ G),
    KFlat F P ∧ QuasiIso f)

/-- The curried natural transformation with the original canonical morphism as component. -/
def nativeToTensorNatTrans :
    DerivedCategory.Q ⋙ derivedBifunctor F ⋙
      (Functor.whiskeringLeft _ _ _).obj DerivedCategory.Q ⟶
    F.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ) ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q where
  app K :=
    { app := fun L => toTensor F hres K L
      naturality := fun {L L'} g => by
        simpa using toTensor_naturality' F hres (𝟙 K) g }
  naturality {K K'} f := by
    ext L
    simpa using toTensor_naturality' F hres f (𝟙 L)

/-- This packaging preserves the exact native morphism by reflexivity. -/
theorem nativeToTensorNatTrans_app (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) :
    ((nativeToTensorNatTrans F hres).app K).app L = toTensor F hres K L := rfl

end CochainComplex.KFlatBifunctor
