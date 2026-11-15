/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import StacksFrontier.Homology.KFlat.BifunctorComparisonOneVariable
public import StacksFrontier.Homology.KFlat.BifunctorOneSidedComparison
public import StacksFrontier.Homology.KFlat.BifunctorToTotalComplex
/-! # Native tensor comparison and shifts on the original K-flat models -/
@[expose] public noncomputable section
open CategoryTheory
namespace CochainComplex.KFlatBifunctor
variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K : HomologicalComplex A (ComplexShape.up ℤ))
    (L : HomologicalComplex B (ComplexShape.up ℤ)),
    K.HasMapBifunctor L F (ComplexShape.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]
  (hres : ∀ G : CochainComplex B ℤ,
    ∃ (P : CochainComplex B ℤ) (f : P ⟶ G), KFlat F P ∧ QuasiIso f)

/-- The native first-variable comparison is the original total-complex comparison. -/
theorem comparisonFirst_hom_app_eq_toTensor
    (L : CochainComplex B ℤ) (hL : KFlat F L)
    (K : (kFlatComplexesLeft F).FullSubcategory) :
    (comparisonFirst F L hL).hom.app K = toTensor F hres K.1 L := by
  rw [comparisonFirst_hom_app, toTensor_eq_comparisonRight F hres K.1 hL,
    comparisonRight_hom_eq_comparison_hom F K.1 L K.2 hL]

/-- The native second-variable comparison is the original total-complex comparison. -/
theorem comparisonSecond_hom_app_eq_toTensor
    (K : CochainComplex A ℤ) (hK : KFlatLeft F K)
    (L : (kFlatComplexes F).FullSubcategory) :
    (comparisonSecond F K hK).hom.app L = toTensor F hres K L.1 := by
  rw [comparisonSecond_hom_app, toTensor_eq_comparisonRight F hres K L.2,
    comparisonRight_hom_eq_comparison_hom F K L.1 hK L.2]

/-- First-variable shift compatibility, retaining the native composite shift data. -/
theorem toTensor_shift_first_model
    (K : (kFlatComplexesLeft F).FullSubcategory)
    (L : CochainComplex B ℤ) (hL : KFlat F L) (m : ℤ) :
    let S := kFlatComplexQLeft F ⋙
      (derivedBifunctor F).flip.obj (DerivedCategory.Q.obj L)
    let T := (kFlatComplexesLeft F).ι ⋙
      ((totalBifunctor F).flip.obj L ⋙ DerivedCategory.Q)
    (S.commShiftIso m).hom.app K ≫ (toTensor F hres K.1 L)⟦m⟧' =
      toTensor F hres (K⟦m⟧).1 L ≫ (T.commShiftIso m).hom.app K := by
  let _ := comparisonFirst_commShift F L hL
  have h := NatTrans.shift_app_comm (comparisonFirst F L hL).hom m K
  simpa only [comparisonFirst_hom_app_eq_toTensor F hres] using h

/-- Second-variable shift compatibility, retaining the native composite shift data. -/
theorem toTensor_shift_second_model
    (K : CochainComplex A ℤ) (hK : KFlatLeft F K)
    (L : (kFlatComplexes F).FullSubcategory) (n : ℤ) :
    let S := kFlatComplexQ F ⋙ (derivedBifunctor F).obj (DerivedCategory.Q.obj K)
    let T := (kFlatComplexes F).ι ⋙ ((totalBifunctor F).obj K ⋙ DerivedCategory.Q)
    (S.commShiftIso n).hom.app L ≫ (toTensor F hres K L.1)⟦n⟧' =
      toTensor F hres K (L⟦n⟧).1 ≫ (T.commShiftIso n).hom.app L := by
  let _ := comparisonSecond_commShift F K hK
  have h := NatTrans.shift_app_comm (comparisonSecond F K hK).hom n L
  simpa only [comparisonSecond_hom_app_eq_toTensor F hres] using h

end CochainComplex.KFlatBifunctor
