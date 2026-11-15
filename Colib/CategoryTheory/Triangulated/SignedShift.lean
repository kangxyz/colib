/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor

/-!
# Exact shifts of a pretriangulated category

The commutation of the shift by `n` with the shift by `a` includes the
sign `(-1)^(n*a)`. With that comparison, the image of a distinguished
triangle is isomorphic to Mathlib's signed shift of the triangle.
-/

@[expose] public noncomputable section

open CategoryTheory.Pretriangulated CategoryTheory.Preadditive CategoryTheory.Limits

universe u v

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] [Preadditive C] [HasShift C ℤ]

/-- The comparison of two shifts with the cohomological sign. -/
def signedShiftComm (n a : ℤ) :
    shiftFunctor C a ⋙ shiftFunctor C n ≅ shiftFunctor C n ⋙ shiftFunctor C a :=
  NatIso.ofComponents (fun X => (n * a).negOnePow • (shiftFunctorComm C a n).app X)
    (fun f => by
      simp only [smul_iso_hom, Linear.comp_units_smul, Linear.units_smul_comp]
      exact congrArg ((n * a).negOnePow • ·) ((shiftFunctorComm C a n).hom.naturality f))

omit [Preadditive C] in
private theorem shiftFunctorComm_add_hom (n a b : ℤ) (X : C) :
    (shiftFunctorComm C (a + b) n).hom.app X =
      ((shiftFunctorAdd C a b).hom.app X)⟦n⟧' ≫
        (shiftFunctorComm C b n).hom.app (X⟦a⟧) ≫
        ((shiftFunctorComm C a n).hom.app X)⟦b⟧' ≫
        (shiftFunctorAdd C a b).inv.app (X⟦n⟧) := by
  apply (cancel_epi ((shiftFunctorComm C n (a + b)).hom.app X)).mp
  have h := shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app n a b X
  have he (c : ℤ) (Y : C) : (shiftFunctorComm C c n).hom.app Y =
      (shiftFunctorComm C n c).inv.app Y := by
    rw [← shiftFunctorComm_symm C n c]
    rfl
  rw [he, Iso.hom_inv_id_app, ← Category.assoc, h, he b, he a]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app]
  change 𝟙 _ = (shiftFunctorAdd C a b).hom.app (X⟦n⟧) ≫
    (shiftFunctor C b).map (𝟙 (X⟦n⟧⟦a⟧)) ≫ (shiftFunctorAdd C a b).inv.app (X⟦n⟧)
  simp

variable [∀ a : ℤ, (shiftFunctor C a).Additive]

/-- The shift functor has its sign-correct commutation with the shifts. -/
instance shiftFunctorSignedCommShift (n : ℤ) : (shiftFunctor C n).CommShift ℤ where
  commShiftIso := signedShiftComm C n
  commShiftIso_zero := by
    ext X
    simp only [signedShiftComm, NatIso.ofComponents_hom_app, smul_iso_hom, mul_zero,
      Int.negOnePow_zero, one_smul, Functor.CommShift.isoZero_hom_app]
    have h := shiftFunctorZero_inv_app_shift (X := X) n
    have h' : (shiftFunctorComm C 0 n).hom.app X =
        (shiftFunctorComm C n 0).inv.app X :=
      congrArg (fun e => e.hom.app X) (shiftFunctorComm_symm C n 0).symm
    change (shiftFunctorComm C 0 n).hom.app X = _
    rw [h', ← cancel_epi ((shiftFunctor C n).map ((shiftFunctorZero C ℤ).inv.app X)), ← h]
    change _ = (shiftFunctor C n).map ((shiftFunctorZero C ℤ).inv.app X) ≫
      (shiftFunctor C n).map ((shiftFunctorZero C ℤ).hom.app X) ≫
      (shiftFunctorZero C ℤ).inv.app (X⟦n⟧)
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  commShiftIso_add a b := by
    ext X
    simp only [Functor.CommShift.isoAdd_hom_app, signedShiftComm,
      NatIso.ofComponents_hom_app, smul_iso_hom, Functor.map_units_smul,
      Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, mul_add, Int.negOnePow_add]
    exact congrArg (((n * a).negOnePow * (n * b).negOnePow) • ·)
      (shiftFunctorComm_add_hom C n a b X)

variable [HasZeroObject C] [Pretriangulated C]

/-- Cohomological shift is an exact functor with the signed commutation. -/
instance shiftFunctorIsTriangulated (n : ℤ) : (shiftFunctor C n).IsTriangulated where
  map_distinguished T hT := by
    refine isomorphic_distinguished _ (T.shift_distinguished hT n) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (Iso.refl _) ?_ ?_ ?_
    · simp [Functor.mapTriangle, Triangle.shiftFunctor, Linear.comp_units_smul]
    · simp [Functor.mapTriangle, Triangle.shiftFunctor, Linear.units_smul_comp,
        Linear.comp_units_smul, smul_smul, Int.units_mul_self]
    · suffices T.mor₃⟦n⟧' ≫ ((shiftFunctor C n).commShiftIso (1 : ℤ)).hom.app T.obj₁ =
          n.negOnePow • (T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁) by
        simpa [Functor.mapTriangle, Triangle.shiftFunctor] using this
      change T.mor₃⟦n⟧' ≫ (signedShiftComm C n 1).hom.app T.obj₁ = _
      simp [signedShiftComm, Linear.comp_units_smul]

section Functor

variable {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
  [∀ a : ℤ, (shiftFunctor D a).Additive]
  (F : C ⥤ D) [F.CommShift ℤ] [F.Additive]

omit [HasZeroObject C] [Pretriangulated C] in
/-- An additive shift-compatible functor preserves the signed commutation of shifts. -/
theorem commShiftIso_signedShift (n : ℤ) :
    NatTrans.CommShift (F.commShiftIso n).hom ℤ := by
  refine ⟨fun a => NatTrans.ext (funext fun X => ?_)⟩
  change _ ≫ ((F.commShiftIso n).hom.app X)⟦a⟧' = _
  simp only [Functor.commShiftIso_comp_hom_app, NatTrans.comp_app, Functor.whiskerLeft_app,
    Category.assoc]
  change F.map ((signedShiftComm C n a).hom.app X) ≫
      (F.commShiftIso a).hom.app (X⟦n⟧) ≫ ((F.commShiftIso n).hom.app X)⟦a⟧' =
    (F.commShiftIso n).hom.app (X⟦a⟧) ≫
      ((F.commShiftIso a).hom.app X)⟦n⟧' ≫ (signedShiftComm D n a).hom.app (F.obj X)
  simp only [signedShiftComm, NatIso.ofComponents_hom_app, smul_iso_hom,
    Functor.map_units_smul, Linear.units_smul_comp, Linear.comp_units_smul, Iso.app_hom]
  exact congrArg ((n * a).negOnePow • ·) (by
    rw [F.map_shiftFunctorComm_hom_app]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    have h : (shiftFunctor D a).map (𝟙 ((F ⋙ shiftFunctor D n).obj X)) =
        𝟙 (((F.obj X)⟦n⟧)⟦a⟧) :=
      (shiftFunctor D a).map_id ((F ⋙ shiftFunctor D n).obj X)
    rw [h]
    let f := (F.commShiftIso n).hom.app (X⟦a⟧)
    let g := ((F.commShiftIso a).hom.app X)⟦n⟧'
    let j := (shiftFunctorComm D a n).hom.app (F.obj X)
    exact congrArg (fun x => f ≫ g ≫ x) (Category.comp_id j))

end Functor

end CategoryTheory
