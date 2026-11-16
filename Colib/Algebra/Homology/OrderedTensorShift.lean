/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift

/-! # Ordered shifts of the native total tensor

This comparison uses the native second-variable shift followed by the native
first-variable shift. Its component sign is `(-1)^(i*m)`, not a sign guessed
from the total shift. No derived tensor or alternative complex is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C₁ C₂ D : Type*} [Category* C₁] [Category* C₂] [Category* D]
  [Preadditive C₁] [Preadditive C₂] [Preadditive D]
  (F : C₁ ⥤ C₂ ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  (K : CochainComplex C₁ ℤ) (L : CochainComplex C₂ ℤ)
  [HasMapBifunctor K L F]

set_option backward.defeqAttrib.useBackward true in
/-- The ordered comparison, first moving the second shift out of the tensor. -/
def orderedMapBifunctorShiftIso (n m : ℤ) :
    mapBifunctor (K⟦n⟧) (L⟦m⟧) F ≅ ((mapBifunctor K L F)⟦n⟧)⟦m⟧ :=
  mapBifunctorShift₂Iso (K⟦n⟧) L F m ≪≫
    (CategoryTheory.shiftFunctor (CochainComplex D ℤ) m).mapIso (mapBifunctorShift₁Iso K L F n)

/-- The same ordered comparison with the sum shift, using native shift addition. -/
def orderedMapBifunctorSumShiftIso (n m : ℤ) :
    mapBifunctor (K⟦n⟧) (L⟦m⟧) F ≅ (mapBifunctor K L F)⟦n + m⟧ :=
  orderedMapBifunctorShiftIso F K L n m ≪≫
    ((shiftFunctorAdd (CochainComplex D ℤ) n m).app _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On the `(i,j)` summand the ordered comparison has precisely the sign `(-1)^(i*m)`. -/
theorem ι_orderedMapBifunctorShiftIso_hom_f (n m i j k : ℤ) (h : i + j = k) :
    ιMapBifunctor (K⟦n⟧) (L⟦m⟧) F i j k h ≫
        (orderedMapBifunctorShiftIso F K L n m).hom.f k =
      (i * m).negOnePow •
        ((F.map (K.shiftFunctorObjXIso n i (i + n) rfl).hom).app _ ≫
          (F.obj _).map (L.shiftFunctorObjXIso m j (j + m) rfl).hom ≫
          ιMapBifunctor K L F (i + n) (j + m) (k + m + n) (by omega)) := by
  change ιMapBifunctor (K⟦n⟧) (L⟦m⟧) F i j k h ≫
    (mapBifunctorShift₂Iso (K⟦n⟧) L F m).hom.f k ≫
    (mapBifunctorShift₁Iso K L F n).hom.f (k + m) = _
  rw [ι_mapBifunctorShift₂Iso_hom_f_assoc _ _ F m i j k h
    (j + m) (k + m) rfl rfl]
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    Category.id_comp, Category.assoc, Linear.units_smul_comp]
  rw [ι_mapBifunctorShift₁Iso_hom_f _ _ F n i (j + m) (k + m)
    (by omega) (i + n) (k + m + n) rfl rfl]
  simp [shiftFunctorObjXIso]

/-- Negative weight shifts retain the sign of the second weight on the first degree. -/
theorem ordered_weight_sign (i : ℤ) (q : ℕ) :
    (i * (-(q : ℤ))).negOnePow = (i * (q : ℤ)).negOnePow := by
  rw [mul_neg, Int.negOnePow_neg]

set_option backward.defeqAttrib.useBackward true in
/-- Reversing the order of the two weight shifts gives exactly `(-1)^(p*q)`. -/
theorem mapBifunctor_weightShift_order (p q : ℕ) :
    mapBifunctorShift₁Iso K (L⟦-(q : ℤ)⟧) F (-(p : ℤ)) ≪≫
      (CategoryTheory.shiftFunctor _ (-(p : ℤ))).mapIso
        (mapBifunctorShift₂Iso K L F (-(q : ℤ))) =
      ((p : ℤ) * (q : ℤ)).negOnePow •
        (orderedMapBifunctorShiftIso F K L (-(p : ℤ)) (-(q : ℤ)) ≪≫
          (shiftFunctorComm (CochainComplex D ℤ) (-(p : ℤ)) (-(q : ℤ))).app _) := by
  simpa only [orderedMapBifunctorShiftIso, neg_mul_neg, Iso.trans_assoc] using
    mapBifunctorShift₁Iso_trans_mapBifunctorShift₂Iso K L F (-(p : ℤ)) (-(q : ℤ))

end CochainComplex
