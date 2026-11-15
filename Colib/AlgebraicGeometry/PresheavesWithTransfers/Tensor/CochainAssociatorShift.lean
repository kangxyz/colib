/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.Algebra.Homology.Linear

/-!
# Shifting the middle variable of a signed cochain associator

On each tridegree, associating before or after the middle shift uses the
same associator on coefficients. Each route picks up the sign from the
degree of the first factor times the middle shift.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomologicalComplex
open scoped ZeroObject

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Preadditive C]
  [MonoidalPreadditive C] [HasZeroObject C]
  [∀ K L : GradedObject ℤ C, GradedObject.HasTensor K L]
  [∀ X : C, PreservesColimit (Functor.empty.{0} C) (tensorLeft X)]
  [∀ X : C, PreservesColimit (Functor.empty.{0} C) (tensorRight X)]
  [∀ K L M : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor K L M]
  [∀ K L M : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ K L M]

local notation "Ch" => CochainComplex C ℤ
local notation "c" => ComplexShape.up ℤ
local notation "F" => curriedTensor C
local notation "ι₂(" K "," L "," p "," q "," d ")" => ιTensorObj K L p q d (by omega)
local notation "ι₁₂(" K "," L "," M "," p "," q "," r "," d ")" =>
  HomologicalComplex.mapBifunctor₁₂.ι F F K L M c c p q r d (by change p + q + r = d; omega)
local notation "ι₂₃(" K "," L "," M "," p "," q "," r "," d ")" =>
  HomologicalComplex.mapBifunctor₂₃.ι F F K L M c c c p q r d (by change p + q + r = d; omega)
local notation "s(" K "," L "," m ")" => CochainComplex.mapBifunctorShift₂Iso K L F m
local notation "t(" K "," L "," m ")" => CochainComplex.mapBifunctorShift₁Iso K L F m

@[reassoc]
private theorem assoc_ι (K L M : Ch) (p q r d : ℤ) (h : p + q + r = d) :
    ι₁₂(K,L,M,p,q,r,d) ≫ (α_ K L M).hom.f d =
      (α_ (K.X p) (L.X q) (M.X r)).hom ≫ ι₂₃(K,L,M,p,q,r,d) := by
  have hα : (α_ K L M).hom.f d =
      (HomologicalComplex.mapBifunctorAssociatorX (curriedAssociatorNatIso C) K L M c c c d).hom :=
    rfl
  rw [hα, HomologicalComplex.ι_mapBifunctorAssociatorX_hom]
  simp only [curriedAssociatorNatIso_hom_app_app_app]

/-- The signed cochain associator is compatible with a shift in its middle variable. -/
theorem associator_hom_middleShift (K L M : Ch) (m : ℤ) :
    (α_ K (L⟦m⟧) M).hom ≫ K ◁ (t(L,M,m)).hom ≫ (s(K,L ⊗ M,m)).hom =
      (s(K,L,m)).hom ▷ M ≫ (t(K ⊗ L,M,m)).hom ≫ (α_ K L M).hom⟦m⟧' := by
  apply HomologicalComplex.hom_ext
  intro d
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have hd : p + q + r = d := h
  let D := d + m
  let v := q + r
  let w := p + q
  let Ls := (CategoryTheory.shiftFunctor Ch m).obj L
  simp only [HomologicalComplex.comp_f]
  rw [assoc_ι_assoc K Ls M p q r d hd]
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq F F K Ls M c c c p q r v d rfl (by dsimp [v]; omega)]
  rw [HomologicalComplex.mapBifunctor₁₂.ι_eq F F K Ls M c c p q r w d rfl hd]
  change _ ≫ (K.X p ◁ ι₂(Ls,M,q,r,v) ≫ ι₂(K,Ls ⊗ M,p,v,d)) ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 K) (t(L,M,m)).hom F c).f d ≫ _ =
    ((ι₂(K,Ls,p,q,w) ▷ M.X r) ≫ ι₂(K ⊗ Ls,M,w,r,d)) ≫
      (HomologicalComplex.mapBifunctorMap (s(K,L,m)).hom (𝟙 M) F c).f d ≫ _ ≫ _
  simp only [Category.assoc]
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap_assoc]
  simp only [HomologicalComplex.id_f, curriedTensor_obj_map, curriedTensor_map_app, id_whiskerRight,
    whiskerLeft_id]
  have h₁ : (𝟙 (K.X p ⊗ (Ls ⊗ M).X v)) ≫ (K.X p ◁ (t(L,M,m)).hom.f v) =
      K.X p ◁ (t(L,M,m)).hom.f v := Category.id_comp _
  let L₀ := (CategoryTheory.shiftFunctor Ch m).obj (CochainComplex.mapBifunctor K L F)
  let G₀ := (CategoryTheory.shiftFunctor Ch m).obj (CochainComplex.mapBifunctor L M F)
  let j := HomologicalComplex.ιMapBifunctor L₀ M F c w r d hd
  let j' := HomologicalComplex.ιMapBifunctor K G₀ F c p v d (by dsimp [v]; omega)
  have h₂ : 𝟙 (L₀.X w ⊗ M.X r) ≫ j = j := Category.id_comp _
  rw [← Category.assoc (𝟙 (K.X p ⊗ (Ls ⊗ M).X v)), h₁]
  change _ ≫ K.X p ◁ ι₂(Ls,M,q,r,v) ≫ K.X p ◁ (t(L,M,m)).hom.f v ≫ j' ≫ _ =
    ι₂(K,Ls,p,q,w) ▷ M.X r ≫ (s(K,L,m)).hom.f w ▷ M.X r ≫
      𝟙 (L₀.X w ⊗ M.X r) ≫ j ≫ _ ≫ _
  rw [← Category.assoc (𝟙 (L₀.X w ⊗ M.X r)), h₂]
  rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight_assoc]
  rw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f L M F m q r v rfl
    (q + m) (v + m) rfl rfl]
  rw [CochainComplex.ι_mapBifunctorShift₂Iso_hom_f K L F m p q w rfl
    (q + m) (w + m) rfl rfl]
  have hL := CochainComplex.ι_mapBifunctorShift₂Iso_hom_f K (CochainComplex.mapBifunctor L M F)
    F m p v d (by dsimp [v]; omega) (v + m) D rfl rfl
  have hR := CochainComplex.ι_mapBifunctorShift₁Iso_hom_f (CochainComplex.mapBifunctor K L F)
    M F m w r d hd (w + m) D rfl rfl
  change j' ≫ (s(K,L ⊗ M,m)).hom.f d = _ at hL
  change j ≫ (t(K ⊗ L,M,m)).hom.f d = _ at hR
  rw [hL, ← Category.assoc j, hR]
  simp only [CochainComplex.shiftFunctorObjXIso, XIsoOfEq_rfl, Iso.refl_hom,
    Iso.refl_inv, curriedTensor_obj_map, curriedTensor_map_app, Category.comp_id]
  have hleft : 𝟙 (L.X (q + m)) ▷ M.X r ≫ L.ιMapBifunctor M F (q + m) r (v + m)
      (by dsimp [v]; omega) = L.ιMapBifunctor M F (q + m) r (v + m) (by dsimp [v]; omega) :=
    (congrArg (· ≫ _) (id_whiskerRight _ _)).trans (Category.id_comp _)
  rw [hleft]
  let I := ι₂(K,L,p,q + m,w + m)
  let J := ι₂(L,M,q + m,r,v + m)
  let U := ι₂(K,L ⊗ M,p,v + m,D)
  let V := ι₂(K ⊗ L,M,w + m,r,D)
  have hshift : ((CategoryTheory.shiftFunctor Ch m).map (α_ K L M).hom).f d =
      (α_ K L M).hom.f D := rfl
  rw [hshift]
  let a := (α_ (K.X p) (L.X (q + m)) (M.X r)).hom
  let z := (p * m).negOnePow
  have hI : K.X p ◁ 𝟙 (L.X (q + m)) ≫ I = I :=
    (congrArg (· ≫ _) (whiskerLeft_id _ _)).trans (Category.id_comp _)
  have hU : K.X p ◁ 𝟙 ((L ⊗ M).X (v + m)) ≫ U = U :=
    (congrArg (· ≫ _) (whiskerLeft_id _ _)).trans (Category.id_comp _)
  have hV : 𝟙 ((K ⊗ L).X (w + m)) ▷ M.X r ≫ V = V :=
    (congrArg (· ≫ _) (id_whiskerRight _ _)).trans (Category.id_comp _)
  let Ld := 𝟙 ((K ⊗ (L ⊗ M)).X D)
  let Rd := 𝟙 (((K ⊗ L) ⊗ M).X D)
  change a ≫ K.X p ◁ J ≫ (z • (K.X p ◁ 𝟙 ((L ⊗ M).X (v + m)) ≫ U ≫ Ld)) =
    (z • (K.X p ◁ 𝟙 (L.X (q + m)) ≫ I)) ▷ M.X r ≫
      (𝟙 ((K ⊗ L).X (w + m)) ▷ M.X r ≫ V ≫ Rd) ≫ (α_ K L M).hom.f D
  have hR₀ : V ≫ Rd = V := Category.comp_id _
  have hL₀ : U ≫ Ld = U := Category.comp_id _
  rw [hR₀, hL₀, hI, hU, hV]
  change a ≫ K.X p ◁ J ≫ (z • U) =
    (tensorRight (M.X r)).map (z • I) ≫ V ≫ (α_ K L M).hom.f D
  rw [Functor.map_units_smul, Linear.units_smul_comp,
    Linear.comp_units_smul, Linear.comp_units_smul]
  apply congrArg (z • ·)
  have hleft₀ : ι₂₃(K,L,M,p,q + m,r,D) = (K.X p ◁ J) ≫ U :=
    HomologicalComplex.mapBifunctor₂₃.ι_eq _ _ K L M c c c p (q + m) r (v + m) D
      (by change (q + m) + r = v + m; dsimp [v]; omega)
      (by change p + (v + m) = D; dsimp [v, D]; omega)
  have hright₀ : ι₁₂(K,L,M,p,q + m,r,D) = (I ▷ M.X r) ≫ V :=
    HomologicalComplex.mapBifunctor₁₂.ι_eq _ _ K L M c c p (q + m) r (w + m) D
      (by change p + (q + m) = w + m; dsimp [w]; omega)
      (by change w + m + r = D; dsimp [w, D]; omega)
  change a ≫ K.X p ◁ J ≫ U = I ▷ M.X r ≫ V ≫ (α_ K L M).hom.f D
  calc
    a ≫ K.X p ◁ J ≫ U = a ≫ ι₂₃(K,L,M,p,q + m,r,D) :=
      congrArg (a ≫ ·) hleft₀.symm
    _ = ι₁₂(K,L,M,p,q + m,r,D) ≫ (α_ K L M).hom.f D :=
      (assoc_ι K L M p (q + m) r D (by dsimp [D]; omega)).symm
    _ = I ▷ M.X r ≫ V ≫ (α_ K L M).hom.f D :=
      (congrArg (· ≫ (α_ K L M).hom.f D) hright₀).trans (Category.assoc _ _ _)

end CochainComplex
