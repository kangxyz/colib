/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleRightComplex

/-! # Shift of the varied variable in tensor with a degree-zero single -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u₁ u₂ v₁ v₂ u' v'

namespace CochainComplex

variable {A : Type u₁} {B : Type u₂} {C : Type u'} [Category.{v₁} A] [Category.{v₂} B]
  [Category.{v'} C] [Preadditive A] [Preadditive B] [Preadditive C] [HasZeroObject B]
  (F : A ⥤ B ⥤ C) [F.Additive] [∀ X : A, (F.obj X).Additive]
  [∀ (K : CochainComplex A ℤ) (L : CochainComplex B ℤ), CochainComplex.HasMapBifunctor K L F]
  (P : B) [(F.flip.obj P).Additive]

local notation "c" => ComplexShape.up ℤ
set_option quotPrecheck false in
local notation "S" => (CochainComplex.singleFunctor B 0).obj P

/-- The original right single comparison preserves the first-variable shift on every term. -/
theorem mapBifunctorSingleRightIso_commShift₁ (K : CochainComplex A ℤ) (n : ℤ) :
    (CochainComplex.mapBifunctorShift₁Iso K S F n).hom ≫
        (mapBifunctorSingleRightIso F K P).hom⟦n⟧' =
      (mapBifunctorSingleRightIso F (K⟦n⟧) P).hom ≫
        (((F.flip.obj P).mapHomologicalComplex c).commShiftIso n).hom.app K := by
  apply HomologicalComplex.hom_ext
  intro i
  let S₀ := S
  let j := singleRightι F (K⟦n⟧) P i
  let p := singleRightπ F (K⟦n⟧) P i
  have h₀ : p ≫ j = 𝟙 _ := singleRightπ_ι F (K⟦n⟧) P i
  let h (T : CochainComplex A ℤ) (i : ℤ) :
      singleRightι F T P i ≫ (mapBifunctorSingleRightIso F T P).hom.f i =
        (F.obj (T.X i)).map (singleObjXSelf c 0 P).hom := by
    let e := mapBifunctorSingleRightXIso F T P i
    have he := e.inv_hom_id
    change ((F.obj (T.X i)).map (singleObjXSelf c 0 P).inv ≫ singleRightι F T P i) ≫
      (mapBifunctorSingleRightIso F T P).hom.f i = 𝟙 _ at he
    rw [Category.assoc] at he
    rw [← cancel_epi ((F.obj (T.X i)).map (singleObjXSelf c 0 P).inv), he,
      ← Functor.map_comp, Iso.inv_hom_id]
    exact ((F.obj (T.X i)).map_id P).symm
  suffices he :
      j ≫ ((CochainComplex.mapBifunctorShift₁Iso K S F n).hom ≫
          (mapBifunctorSingleRightIso F K P).hom⟦n⟧').f i =
        j ≫ ((mapBifunctorSingleRightIso F (K⟦n⟧) P).hom ≫
          (((F.flip.obj P).mapHomologicalComplex c).commShiftIso n).hom.app K).f i by
    simpa only [← Category.assoc, h₀, Category.id_comp] using congrArg (p ≫ ·) he
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  have hi := CochainComplex.ι_mapBifunctorShift₁Iso_hom_f K S₀ F n
    i 0 i (by simp) (i + n) (i + n) rfl rfl
  change j ≫ (CochainComplex.mapBifunctorShift₁Iso K S₀ F n).hom.f i = _ at hi
  rw [← Category.assoc j, hi]
  have hshift : ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).map
      (mapBifunctorSingleRightIso F K P).hom).f i =
      (mapBifunctorSingleRightIso F K P).hom.f (i + n) := rfl
  rw [hshift]
  simp only [CochainComplex.shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv,
    Category.comp_id]
  let I := singleRightι F K P (i + n)
  let j' := (mapBifunctorSingleRightIso F (K⟦n⟧) P).hom.f i
  let f := (mapBifunctorSingleRightIso F K P).hom.f (i + n)
  have hf : (F.map (𝟙 (K.X (i + n)))).app (S₀.X 0) =
      𝟙 ((F.obj (K.X (i + n))).obj (S₀.X 0)) :=
    NatTrans.congr_app (F.map_id (K.X (i + n))) (S₀.X 0)
  change ((F.map (𝟙 (K.X (i + n)))).app (S₀.X 0) ≫ I) ≫ f = j ≫ j' ≫ 𝟙 _
  calc
    _ = I ≫ f := congrArg (· ≫ f) ((congrArg (· ≫ I) hf).trans (Category.id_comp I))
    _ = j ≫ j' := (h K (i + n)).trans (h (K⟦n⟧) i).symm
    _ = _ := (congrArg (j ≫ ·) (Category.comp_id j')).symm

end CochainComplex
