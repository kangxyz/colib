/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Util.References
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact

/-!
# Canonical rotated cone comparison for short exact complexes
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CochainComplex.mappingCone

universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical double-cone comparison attached to a short complex. -/
def shortComplexConeMap (S : ShortComplex (CochainComplex C ℤ)) :
    mappingCone (inr S.f) ⟶ mappingCone S.g :=
  map (inr S.f) S.g (𝟙 S.X₂) (descShortComplex S) (by simp)

/-- The canonical rotated comparison, not a choice of a triangle completion. -/
def fromShortComplexShift (S : ShortComplex (CochainComplex C ℤ)) :
    S.X₁⟦(1 : ℤ)⟧ ⟶ mappingCone S.g :=
  (rotateHomotopyEquiv S.f).hom ≫ shortComplexConeMap S

lemma quasiIso_shortComplexConeMap {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) : QuasiIso (shortComplexConeMap S) := by
  let := HasDerivedCategory.standard C
  have := quasiIso_descShortComplex hS
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
  let t := DerivedCategory.Q.mapTriangle.map
    (triangleMap (inr S.f) S.g (𝟙 S.X₂) (descShortComplex S) (by simp))
  have h₁ : IsIso t.hom₁ := by
    change IsIso (DerivedCategory.Q.map (𝟙 S.X₂))
    infer_instance
  have h₂ : IsIso t.hom₂ := by
    change IsIso (DerivedCategory.Q.map (descShortComplex S))
    infer_instance
  exact isIso₃_of_isIso₁₂ t (DerivedCategory.mappingCone_triangle_distinguished _)
    (DerivedCategory.mappingCone_triangle_distinguished _) h₁ h₂

lemma quasiIso_fromShortComplexShift {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) : QuasiIso (fromShortComplexShift S) := by
  have := quasiIso_shortComplexConeMap hS
  dsimp [fromShortComplexShift]
  infer_instance

/-- The native signed shift comparison from the first term to the shifted cone. -/
def fromShortComplex (S : ShortComplex (CochainComplex C ℤ)) :
    S.X₁ ⟶ mappingCone (S.g⟦(-1 : ℤ)⟧') :=
  (shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).inv.app S.X₁ ≫
    (fromShortComplexShift S)⟦(-1 : ℤ)⟧' ≫ (shiftIso S.g (-1)).hom

lemma quasiIso_fromShortComplex {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) : QuasiIso (fromShortComplex S) := by
  have := quasiIso_fromShortComplexShift hS
  dsimp [fromShortComplex]
  infer_instance

/-- The derived inverse of the canonical shifted SES comparison. -/
def shiftedConeIso {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) [HasDerivedCategory C] :
    DerivedCategory.Q.obj (mappingCone (S.g⟦(-1 : ℤ)⟧')) ≅
      DerivedCategory.Q.obj S.X₁ := by
  have := quasiIso_fromShortComplex hS
  exact (asIso (DerivedCategory.Q.map (fromShortComplex S))).symm

end CochainComplex.mappingCone

namespace CochainComplex.mappingCone
open HomComplex
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

@[reassoc]
lemma fromShortComplexShift_fst (S : ShortComplex (CochainComplex C ℤ)) (i : ℤ) :
    (fromShortComplexShift S).f i ≫ (fst S.g).1.v i (i + 1) rfl =
      S.f.f (i + 1) := by
  simp [fromShortComplexShift, shortComplexConeMap, rotateHomotopyEquiv,
    map, lift_f _ _ _ _ i (i + 1) rfl, Cochain.leftShift_v]

@[reassoc]
lemma fromShortComplexShift_fst' (S : ShortComplex (CochainComplex C ℤ))
    (i j : ℤ) (h : i + 1 = j) :
    (fromShortComplexShift S).f i ≫ (fst S.g).1.v i j h =
      (S.X₁.shiftFunctorObjXIso 1 i j h.symm).hom ≫ S.f.f j := by
  subst j
  simpa [shiftFunctorObjXIso] using fromShortComplexShift_fst S i

@[reassoc]
lemma fromShortComplexShift_snd (S : ShortComplex (CochainComplex C ℤ)) (i : ℤ) :
    (fromShortComplexShift S).f i ≫ (snd S.g).v i i (add_zero i) = 0 := by
  simp [fromShortComplexShift, shortComplexConeMap, rotateHomotopyEquiv,
    map, lift_f _ _ _ _ i (i + 1) rfl, descShortComplex,
    Cochain.leftShift_v (n := -1) _ 1 0 _ i i _ (i + 1) (by omega)]

@[colib_tag "COL-1234",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/Algebra/Homology/HomotopyCategory/Pretriangulated.lean:50-56,280-308"
    "ingredient" "The original negative-first-projection connecting map and native signed shift"]
lemma fromShortComplex_bockstein (S : ShortComplex (CochainComplex C ℤ)) :
    fromShortComplex S ≫ (triangle (S.g⟦(-1 : ℤ)⟧')).mor₃ ≫
      (shiftFunctorCompIsoId _ (-1 : ℤ) 1 (by omega)).hom.app S.X₂ = S.f := by
  ext i
  simp only [Functor.id_obj, Int.reduceNeg, fromShortComplex, Functor.comp_obj,
    shiftFunctorCompIsoId,
    Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, shiftIso, Int.negOnePow_neg, Int.negOnePow_one,
    Units.neg_smul, one_smul, Category.assoc, triangle, Triangle.mk_obj₁, Triangle.mk_mor₃,
    Iso.trans_hom, Iso.symm_hom, HomologicalComplex.comp_f, shiftFunctor_obj_X',
    shiftFunctorZero_inv_app_f, shiftFunctorAdd'_hom_app_f', shiftFunctor_map_f', Cocycle.homOf_f,
    Cocycle.rightShift_coe, Cocycle.coe_neg, Cochain.rightShift_neg, Cochain.neg_v,
    Cochain.rightShift_v (n := 1) _ 1 0 _ i i _ (i + 1) rfl,
    shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id, shiftFunctorAdd'_inv_app_f',
    shiftFunctorZero_hom_app_f, HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
    Preadditive.neg_comp, Preadditive.comp_neg, lift_f_fst_v_assoc, Cocycle.shift_coe,
    Cochain.shift_v', neg_neg, HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom_assoc]
  erw [fromShortComplexShift_fst'_assoc]
  simp [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]

@[reassoc]
lemma map_f_fst {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (g₁ : K₁ ⟶ L₁) (g₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : g₁ ≫ b = a ≫ g₂) (i : ℤ) :
    (map g₁ g₂ a b h).f i ≫ (fst g₂).1.v i (i + 1) rfl =
      (fst g₁).1.v i (i + 1) rfl ≫ a.f (i + 1) := by
  apply (ext_from_iff g₁ (i + 1) i rfl _ _).mpr
  constructor <;> simp [map]

@[reassoc]
lemma map_f_snd {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (g₁ : K₁ ⟶ L₁) (g₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : g₁ ≫ b = a ≫ g₂) (i : ℤ) :
    (map g₁ g₂ a b h).f i ≫ (snd g₂).v i i (add_zero i) =
      (snd g₁).v i i (add_zero i) ≫ b.f i := by
  apply (ext_from_iff g₁ (i + 1) i rfl _ _).mpr
  constructor <;> simp [map]

lemma fromShortComplexShift_naturality
    {S T : ShortComplex (CochainComplex C ℤ)} (f : S ⟶ T) :
    fromShortComplexShift S ≫ map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm =
      f.τ₁⟦(1 : ℤ)⟧' ≫ fromShortComplexShift T := by
  ext i
  apply (ext_to_iff T.g i (i + 1) rfl _ _).mpr
  constructor
  · simp only [HomologicalComplex.comp_f, Category.assoc]
    erw [map_f_fst, fromShortComplexShift_fst, fromShortComplexShift_fst_assoc]
    simpa using congrArg (fun f => f.f (i + 1)) f.comm₁₂.symm
  · simp only [HomologicalComplex.comp_f, Category.assoc]
    erw [map_f_snd, fromShortComplexShift_snd, fromShortComplexShift_snd_assoc]
    simp

end CochainComplex.mappingCone

namespace CochainComplex.mappingCone
open HomComplex
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

@[reassoc]
lemma map_f_fst' {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (g₁ : K₁ ⟶ L₁) (g₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : g₁ ≫ b = a ≫ g₂) (i j : ℤ) (hij : i + 1 = j) :
    (map g₁ g₂ a b h).f i ≫ (fst g₂).1.v i j hij =
      (fst g₁).1.v i j hij ≫ a.f j := by
  subst j
  exact map_f_fst g₁ g₂ a b h i

lemma shiftIso_map {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    (g₁ : K₁ ⟶ L₁) (g₂ : K₂ ⟶ L₂) (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂)
    (h : g₁ ≫ b = a ≫ g₂) (n : ℤ) :
    (map g₁ g₂ a b h)⟦n⟧' ≫ (shiftIso g₂ n).hom =
      (shiftIso g₁ n).hom ≫ map (g₁⟦n⟧') (g₂⟦n⟧') (a⟦n⟧') (b⟦n⟧')
        (by simpa only [Functor.map_comp] using
          (congrArg (fun f => (CategoryTheory.shiftFunctor (CochainComplex C ℤ) n).map f) h)) := by
  ext i
  apply (ext_to_iff (g₂⟦n⟧') i (i + 1) rfl _ _).mpr
  constructor <;>
    simp [shiftIso, map_f_fst', map_f_snd, Cochain.shift_v']

lemma fromShortComplex_naturality
    {S T : ShortComplex (CochainComplex C ℤ)} (f : S ⟶ T) :
    fromShortComplex S ≫
      map (S.g⟦(-1 : ℤ)⟧') (T.g⟦(-1 : ℤ)⟧')
        (f.τ₂⟦(-1 : ℤ)⟧') (f.τ₃⟦(-1 : ℤ)⟧')
        (by simpa only [Functor.map_comp] using
          (congrArg (fun g => (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1)).map g)
            f.comm₂₃.symm)) = f.τ₁ ≫ fromShortComplex T := by
  dsimp only [fromShortComplex]
  rw [Category.assoc, Category.assoc, ← shiftIso_map S.g T.g f.τ₂ f.τ₃ f.comm₂₃.symm (-1),
    ← Functor.map_comp_assoc, fromShortComplexShift_naturality, Functor.map_comp]
  simp only [Category.assoc]
  have hn := (shiftFunctorCompIsoId (CochainComplex C ℤ)
    (1 : ℤ) (-1) (by omega)).inv.naturality f.τ₁
  change f.τ₁ ≫ _ = _ ≫
    (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map
      ((CategoryTheory.shiftFunctor (CochainComplex C ℤ) (1 : ℤ)).map f.τ₁) at hn
  rw [← reassoc_of% hn]

lemma shiftedConeIso_naturality [HasDerivedCategory C]
    {S T : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T) :
    DerivedCategory.Q.map
      (map (S.g⟦(-1 : ℤ)⟧') (T.g⟦(-1 : ℤ)⟧')
        (f.τ₂⟦(-1 : ℤ)⟧') (f.τ₃⟦(-1 : ℤ)⟧')
        (by simpa only [Functor.map_comp] using
          (congrArg (fun g => (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1)).map g)
            f.comm₂₃.symm))) ≫ (shiftedConeIso hT).hom =
      (shiftedConeIso hS).hom ≫ DerivedCategory.Q.map f.τ₁ := by
  have := quasiIso_fromShortComplex hS
  have := quasiIso_fromShortComplex hT
  apply (cancel_epi (DerivedCategory.Q.map (fromShortComplex S))).mp
  rw [← DerivedCategory.Q.map_comp_assoc, fromShortComplex_naturality,
    DerivedCategory.Q.map_comp]
  simp [shiftedConeIso]

end CochainComplex.mappingCone

namespace CochainComplex.mappingCone
universe v u
variable {C : Type u} [Category.{v} C] [Abelian C]
lemma map_arrow_eq {K₁ L₁ K₂ L₂ : CochainComplex C ℤ}
    {g₁ g₁' : K₁ ⟶ L₁} {g₂ g₂' : K₂ ⟶ L₂}
    (a : K₁ ⟶ K₂) (b : L₁ ⟶ L₂) (h₁ : g₁ = g₁') (h₂ : g₂ = g₂')
    (h : g₁ ≫ b = a ≫ g₂) (h' : g₁' ≫ b = a ≫ g₂') :
    map g₁ g₂ a b h ≫
      (eqToIso (congrArg (fun g : K₂ ⟶ L₂ => mappingCone g) h₂)).hom =
    (eqToIso (congrArg (fun g : K₁ ⟶ L₁ => mappingCone g) h₁)).hom ≫
      map g₁' g₂' a b h' := by
  subst g₁'
  subst g₂'
  simp
end CochainComplex.mappingCone
