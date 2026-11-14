/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.EulerBoundedSequence
public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.GeometricCoefficientFunctors
public import Colib.KTheory.Waldhausen.Additivity.GroupFormula

/-! # The middle Euler coefficient is the sum of two negative coefficients

The native Euler middle term is the biproduct of two copies of the negative line.
Its literal inclusions and projections remain a biproduct after degreewise tensor,
Godement totalization, and direct image. Thus the middle coefficient is the actual
coproduct functor of two copies of the resolved negative coefficient.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.Waldhausen
open AlgebraicGeometry.RingedSpace AlgebraicGeometry.Scheme.Modules
open Stacks.SheafOfModules.Tensor
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

variable (X : Scheme.{u})

local notation "P" => (projectiveSpaceOver 1 X)
local notation "π" => (P ↘ X)
local notation "L" => (twistOver 1 X (-1))
local notation "M" => (ShortComplex.X₂ (projectiveLineEulerSequence X))
local notation "V" => (BoundedBelowPerfect.waldhausen P)
local notation "W" => (perfectComplexesWaldhausen
  (LocallyRingedSpace.toRingedSpace (Scheme.toLocallyRingedSpace X)))
local notation "D" => (total P ⋙ projectiveLineG₀ X)
local notation "TL" => (BoundedBelowPerfect.tensorVectorBundleRight L)
local notation "TM" => (BoundedBelowPerfect.tensorVectorBundleRight M)

attribute [local instance] Abelian.hasFiniteBiproducts

local instance : HasBinaryCoproducts (ObjectProperty.FullSubcategory
    (IsPerfectComplex (X := X.toRingedSpace))) := Additivity.hasBinaryCoproducts W

local instance : IsProper π := isProper_projectiveSpaceOver 1 X

local instance : SheafOfModules.IsFiniteLocallyFree (R := (P).ringCatSheaf) L :=
  let : SheafOfModules.IsFiniteLocallyFreeOfRank (R := (P).ringCatSheaf) L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme P _
  SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1

local instance eulerMiddleTensorMonoidal : MonoidalCategory (P).Modules :=
  SheafOfModules.monoidalCategorySheafTensor (P).sheaf

local instance eulerMiddleTensorAdditive : MonoidalPreadditive (P).Modules :=
  SheafOfModules.monoidalPreadditiveSheafTensor (P).sheaf

/-- The two equal summands use the original inclusions into the Euler middle bundle. -/
def eulerMiddleInl : TL ⋙ D ⟶ TM ⋙ D :=
  Functor.whiskerRight (BoundedBelowPerfect.tensorVectorBundleRightMap
    (biprod.inl ≫ (projectiveLineEulerMiddleBiprodIso X).inv)) D

/-- The other inclusion is the second biproduct inclusion of the Euler middle bundle. -/
def eulerMiddleInr : TL ⋙ D ⟶ TM ⋙ D :=
  Functor.whiskerRight (BoundedBelowPerfect.tensorVectorBundleRightMap
    (biprod.inr ≫ (projectiveLineEulerMiddleBiprodIso X).inv)) D

/-- The first projection of the actual Euler middle coefficient. -/
def eulerMiddleFst : TM ⋙ D ⟶ TL ⋙ D :=
  Functor.whiskerRight (BoundedBelowPerfect.tensorVectorBundleRightMap
    ((projectiveLineEulerMiddleBiprodIso X).hom ≫ biprod.fst)) D

/-- The second projection of the actual Euler middle coefficient. -/
def eulerMiddleSnd : TM ⋙ D ⟶ TL ⋙ D :=
  Functor.whiskerRight (BoundedBelowPerfect.tensorVectorBundleRightMap
    ((projectiveLineEulerMiddleBiprodIso X).hom ≫ biprod.snd)) D

set_option maxHeartbeats 1000000 in
-- The comparisons unfold the actual tensor, resolution, and direct-image functors.
/-- The projected Euler middle arrows satisfy the five biproduct identities. -/
theorem eulerMiddle_relations (K : BoundedBelowPerfect.Obj P) :
    (eulerMiddleInl X).app K ≫ (eulerMiddleFst X).app K = 𝟙 _ ∧
    (eulerMiddleInl X).app K ≫ (eulerMiddleSnd X).app K = 0 ∧
    (eulerMiddleInr X).app K ≫ (eulerMiddleFst X).app K = 0 ∧
    (eulerMiddleInr X).app K ≫ (eulerMiddleSnd X).app K = 𝟙 _ ∧
    (eulerMiddleFst X).app K ≫ (eulerMiddleInl X).app K +
      (eulerMiddleSnd X).app K ≫ (eulerMiddleInr X).app K = 𝟙 _ := by
  let e := projectiveLineEulerMiddleBiprodIso X
  let a : L ⟶ M := biprod.inl ≫ e.inv
  let b : L ⟶ M := biprod.inr ≫ e.inv
  let p : M ⟶ L := e.hom ≫ biprod.fst
  let q : M ⟶ L := e.hom ≫ biprod.snd
  have ha : a ≫ p = 𝟙 _ := by simp [a, p]
  have hb : a ≫ q = 0 := by simp [a, q]
  have hc : b ≫ p = 0 := by simp [b, p]
  have hd : b ≫ q = 𝟙 _ := by simp [b, q]
  have he : p ≫ a + q ≫ b = 𝟙 _ := by
    dsimp only [p, a, q, b]
    simp only [Category.assoc, ← Preadditive.comp_add]
    rw [← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
      ← Preadditive.add_comp, biprod.total, Category.id_comp, Iso.hom_inv_id]
  let t₁ := BoundedBelowPerfect.tensorVectorBundleRightMap a
  let t₂ := BoundedBelowPerfect.tensorVectorBundleRightMap b
  let t₃ := BoundedBelowPerfect.tensorVectorBundleRightMap p
  let t₄ := BoundedBelowPerfect.tensorVectorBundleRightMap q
  have h₁ : t₁.app K ≫ t₃.app K = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.hom_ext
    intro n
    change ((tensorLeft (K.obj.X n)).map a) ≫ ((tensorLeft (K.obj.X n)).map p) = 𝟙 _
    rw [← Functor.map_comp, ha]
    exact (tensorLeft (K.obj.X n)).map_id _
  have h₂ : t₁.app K ≫ t₄.app K = 0 := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.hom_ext
    intro n
    change ((tensorLeft (K.obj.X n)).map a) ≫ ((tensorLeft (K.obj.X n)).map q) = 0
    rw [← Functor.map_comp, hb, Functor.map_zero]
  have h₃ : t₂.app K ≫ t₃.app K = 0 := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.hom_ext
    intro n
    change ((tensorLeft (K.obj.X n)).map b) ≫ ((tensorLeft (K.obj.X n)).map p) = 0
    rw [← Functor.map_comp, hc, Functor.map_zero]
  have h₄ : t₂.app K ≫ t₄.app K = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.hom_ext
    intro n
    change ((tensorLeft (K.obj.X n)).map b) ≫ ((tensorLeft (K.obj.X n)).map q) = 𝟙 _
    rw [← Functor.map_comp, hd]
    exact (tensorLeft (K.obj.X n)).map_id _
  have h₅ : t₃.app K ≫ t₁.app K + t₄.app K ≫ t₂.app K = 𝟙 _ := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.hom_ext
    intro n
    let F := tensorLeft (K.obj.X n)
    change F.map p ≫ F.map a + F.map q ≫ F.map b = 𝟙 _
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, he]
    exact F.map_id _
  let E := D
  let : E.Additive := by
    dsimp only [E]
    change (total P ⋙ perfectPushforward π).Additive
    infer_instance
  have j₁ := congrArg E.map h₁
  have j₂ := congrArg E.map h₂
  have j₃ := congrArg E.map h₃
  have j₄ := congrArg E.map h₄
  have j₅ := congrArg E.map h₅
  rw [E.map_comp, E.map_id] at j₁ j₄
  rw [E.map_comp, E.map_zero] at j₂ j₃
  rw [E.map_add, E.map_comp, E.map_comp, E.map_id] at j₅
  exact ⟨j₁, j₂, j₃, j₄, j₅⟩

/-- The projected Euler middle is the actual pointwise sum of two projected negative lines. -/
def projectiveLineEulerMiddleSumIso :
    CategoryTheory.sumFunctor (TL ⋙ D) (TL ⋙ D) ≅ TM ⋙ D := by
  let i := eulerMiddleInl X
  let j := eulerMiddleInr X
  let p := eulerMiddleFst X
  let q := eulerMiddleSnd X
  refine NatIso.ofComponents (fun K => ?_) (fun {_ _} g => ?_)
  · obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := eulerMiddle_relations X K
    refine { hom := coprod.desc (i.app K) (j.app K)
             inv := p.app K ≫ coprod.inl + q.app K ≫ coprod.inr
             hom_inv_id := ?_
             inv_hom_id := ?_ }
    · apply coprod.hom_ext
      · rw [coprod.inl_desc_assoc, Preadditive.comp_add,
          ← Category.assoc, ← Category.assoc, h₁, h₂]
        simp only [Category.id_comp, zero_comp, add_zero]
        exact (Category.comp_id _).symm
      · rw [coprod.inr_desc_assoc, Preadditive.comp_add,
          ← Category.assoc, ← Category.assoc, h₃, h₄]
        simp only [Category.id_comp, zero_comp, zero_add]
        exact (Category.comp_id _).symm
    · rw [Preadditive.add_comp, Category.assoc, Category.assoc,
        coprod.inl_desc, coprod.inr_desc]
      exact h₅
  · apply coprod.hom_ext
    · simp only [CategoryTheory.sumFunctor, coprod.inl_map_assoc,
        coprod.inl_desc_assoc, coprod.inl_desc]
      exact i.naturality g
    · simp only [CategoryTheory.sumFunctor, coprod.inr_map_assoc,
        coprod.inr_desc_assoc, coprod.inr_desc]
      exact j.naturality g

/-- The Euler middle coefficient is the square of the single negative-line K-map. -/
theorem projectiveLineEulerMiddle_KMap (n : ℕ) (x : (V).K n) :
    KMap ((BoundedBelowPerfect.tensorVectorBundleRight_exact M).comp
      ((total_exact P).comp (projectiveLineG₀_exact X))) n x =
      (KMap ((BoundedBelowPerfect.tensorVectorBundleRight_exact L).comp
        ((total_exact P).comp (projectiveLineG₀_exact X))) n x) ^ 2 := by
  let d := (total_exact P).comp (projectiveLineG₀_exact X)
  let f := (BoundedBelowPerfect.tensorVectorBundleRight_exact L).comp d
  let g := (BoundedBelowPerfect.tensorVectorBundleRight_exact M).comp d
  have h := KMap_eq_of_iso (Additivity.sumFunctor_isExact V W f f) g
    (projectiveLineEulerMiddleSumIso X) n
  exact (DFunLike.congr_fun h.symm x).trans
    ((Additivity.KMap_sum_apply V W f f n x).trans (pow_two _).symm)

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect
