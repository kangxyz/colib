/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.KFlatToTensorShift

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

/-- The source comparison moves the second shift first, using native derived
bifunctor and localization commutation isomorphisms. -/
def toTensorOrderedSourceShiftIso (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (n m : ℤ) :=
  ((DerivedCategory.Q ⋙ (derivedBifunctor F).obj
    (DerivedCategory.Q.obj (K⟦n⟧))).commShiftIso m).app L ≪≫
      (CategoryTheory.shiftFunctor (DerivedCategory D) m).mapIso
        (((DerivedCategory.Q ⋙ (derivedBifunctor F).flip.obj
          (DerivedCategory.Q.obj L)).commShiftIso n).app K)

/-- The target comparison moves the second shift first, using the original total
complex and localization shift isomorphisms. -/
def toTensorOrderedTargetShiftIso (K : CochainComplex A ℤ) (L : CochainComplex B ℤ)
    (n m : ℤ) :=
  (((totalBifunctor F).obj (K⟦n⟧) ⋙ DerivedCategory.Q).commShiftIso m).app L ≪≫
    (CategoryTheory.shiftFunctor (DerivedCategory D) m).mapIso
      ((((totalBifunctor F).flip.obj L ⋙ DerivedCategory.Q).commShiftIso n).app K)

/-- The native derived-to-total morphism commutes with the ordered pair of shifts,
for arbitrary input complexes. Both comparisons retain their actual native maps. -/
theorem toTensor_ordered_shift_square
    (resL : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      KFlatLeft F P ∧ QuasiIso f)
    (K : CochainComplex A ℤ) (L : CochainComplex B ℤ) (n m : ℤ) :
    (toTensorOrderedSourceShiftIso F K L n m).hom ≫
        (CategoryTheory.shiftFunctor (DerivedCategory D) m).map
          ((CategoryTheory.shiftFunctor (DerivedCategory D) n).map (toTensor F hres K L)) =
      toTensor F hres (K⟦n⟧) (L⟦m⟧) ≫
        (toTensorOrderedTargetShiftIso F K L n m).hom := by
  let := nativeToTensorFirst_commShift F hres resL L
  let := nativeToTensorSecond_commShift F hres resL (K⟦n⟧)
  have h₁ := NatTrans.shift_app_comm (nativeToTensorFirst F hres L) n K
  have h₂ := NatTrans.shift_app_comm (nativeToTensorSecond F hres (K⟦n⟧)) m L
  dsimp only [nativeToTensorFirst, nativeToTensorSecond] at h₁ h₂
  simp only [toTensorOrderedSourceShiftIso, toTensorOrderedTargetShiftIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  rw [← Functor.map_comp, h₁, Functor.map_comp, ← Category.assoc, h₂, Category.assoc]

end CochainComplex.KFlatBifunctor
