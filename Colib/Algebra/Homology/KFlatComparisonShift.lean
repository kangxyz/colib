/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.Homology.KFlat.BifunctorComparisonOneVariable

/-!
# Native shift squares for the two-sided K-flat comparison

New source extraction from the native one-variable comparison API. No tensor, derived
category model, shift convention, or comparison map is replaced. The source and target
shift isomorphisms are written with their full composite functors: these are precisely
those used by `comparisonFirst_commShift` and `comparisonSecond_commShift`.

The statements deliberately retain objects of the resolving full subcategories. This
keeps the native restriction shift datum visible, including its inclusion bridge. Their
underlying complexes are the original complexes; no additional flatness is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.KFlatBifunctor

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
      K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
  [(kFlatQLeft F).IsLocalization (kFlatQuasiIsoLeft F)]
  [(kFlatQ F).IsLocalization (kFlatQuasiIso F)]

/-- The original two-sided comparison square for a shift in its first variable,
with the native restricted source and target shift data explicit. -/
theorem comparison_shift_first_square
    (K : (kFlatComplexesLeft F).FullSubcategory)
    (L : (kFlatComplexes F).FullSubcategory) (n : ℤ) :
    ((kFlatComplexQLeft F ⋙
        (derivedBifunctor F).flip.obj (DerivedCategory.Q.obj L.1)).commShiftIso n).hom.app K ≫
        (CategoryTheory.shiftFunctor (DerivedCategory D) n).map (comparison F K.1 L.1 K.2 L.2).hom =
      (comparison F (K⟦n⟧).1 L.1 (K⟦n⟧).2 L.2).hom ≫
        (((kFlatComplexesLeft F).ι ⋙
          ((totalBifunctor F).flip.obj L.1 ⋙ DerivedCategory.Q)).commShiftIso n).hom.app K := by
  let := comparisonFirst_commShift F L.1 L.2
  simpa only [comparisonFirst_hom_app] using
    (NatTrans.shift_app_comm (comparisonFirst F L.1 L.2).hom n K)

/-- The original two-sided comparison square for a shift in its second variable,
with the native restricted source and target shift data explicit. -/
theorem comparison_shift_second_square
    (K : (kFlatComplexesLeft F).FullSubcategory)
    (L : (kFlatComplexes F).FullSubcategory) (n : ℤ) :
    ((kFlatComplexQ F ⋙
        (derivedBifunctor F).obj (DerivedCategory.Q.obj K.1)).commShiftIso n).hom.app L ≫
        (CategoryTheory.shiftFunctor (DerivedCategory D) n).map (comparison F K.1 L.1 K.2 L.2).hom =
      (comparison F K.1 (L⟦n⟧).1 K.2 (L⟦n⟧).2).hom ≫
        (((kFlatComplexes F).ι ⋙
          ((totalBifunctor F).obj K.1 ⋙ DerivedCategory.Q)).commShiftIso n).hom.app L := by
  let := comparisonSecond_commShift F K.1 K.2
  simpa only [comparisonSecond_hom_app] using
    (NatTrans.shift_app_comm (comparisonSecond F K.1 K.2).hom n L)

end CochainComplex.KFlatBifunctor

end
