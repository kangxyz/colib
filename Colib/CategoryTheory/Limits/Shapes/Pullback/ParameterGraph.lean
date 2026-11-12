/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Assoc
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Pullback against a graph parameter

If a free parameter in one factor is identified with a parameter map from
the other factor, the parameter quotient is the original product. After
also matching the common middle factor, the full pullback is the original
pullback over that middle factor.
-/

@[expose] public noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {Q P X S T : C}

section Incidence

variable (p : Q ⟶ X) (f : X ⟶ S) (t : T ⟶ S)

/-- Extend the middle map by a free parameter. -/
def pullbackParameterExtensionMap : pullback (p ≫ f) t ⟶ pullback f t :=
  pullback.map _ _ _ _ p (𝟙 T) (𝟙 S) (by simp) (by simp)

@[reassoc (attr := simp)]
theorem pullbackParameterExtensionMap_fst :
    pullbackParameterExtensionMap p f t ≫ pullback.fst f t = pullback.fst (p ≫ f) t ≫ p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackParameterExtensionMap_snd :
    pullbackParameterExtensionMap p f t ≫ pullback.snd f t = pullback.snd (p ≫ f) t := by
  exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- The extended map is the actual pullback over the original middle factor. -/
theorem pullbackParameterExtension_isPullback :
    IsPullback (pullbackParameterExtensionMap p f t) (pullback.fst (p ≫ f) t)
      (pullback.fst f t) p := by
  have h : IsPullback (pullbackParameterExtensionMap p f t ≫ pullback.snd f t)
      (pullback.fst (p ≫ f) t) t (p ≫ f) := by
    rw [pullbackParameterExtensionMap_snd]
    exact (IsPullback.of_hasPullback (p ≫ f) t).flip
  exact h.of_right (pullbackParameterExtensionMap_fst p f t)
    (IsPullback.of_hasPullback f t).flip

/-- After taking a graph parameter on the right, the full incidence is
Cartesian over the original middle object. -/
theorem pullbackParameterIncidence_isPullback (r : P ⟶ X) (l : P ⟶ T)
    (hl : r ≫ f = l ≫ t) :
    IsPullback
      (pullback.fst (pullbackParameterExtensionMap p f t) (pullback.lift r l hl) ≫
        pullback.fst (p ≫ f) t)
      (pullback.snd (pullbackParameterExtensionMap p f t) (pullback.lift r l hl)) p r := by
  have h := (IsPullback.of_hasPullback
    (pullbackParameterExtensionMap p f t) (pullback.lift r l hl)).paste_horiz
    (pullbackParameterExtension_isPullback p f t).flip
  simpa only [pullback.lift_fst] using h

end Incidence

section Product

variable (q : Q ⟶ S) (r : P ⟶ S) (t : T ⟶ S)

/-- Move the free parameter after the original product of coefficients. -/
def pullbackParameterProductIso :
    pullback (pullback.fst q t ≫ q) r ≅ pullback (pullback.fst q r ≫ q) t := by
  let e := pullback.map (pullback.snd r q ≫ q) t (pullback.fst q r ≫ q) t
    (pullbackSymmetry r q).hom (𝟙 _) (𝟙 _) (by simp) (by simp)
  let : IsIso e := by dsimp only [e]; infer_instance
  exact pullbackSymmetry (pullback.fst q t ≫ q) r ≪≫
    (pullbackAssoc r q q t).symm ≪≫ asIso e

@[reassoc (attr := simp)]
theorem pullbackParameterProductIso_hom_first :
    (pullbackParameterProductIso q r t).hom ≫ pullback.fst (pullback.fst q r ≫ q) t ≫
      pullback.fst q r = pullback.fst (pullback.fst q t ≫ q) r ≫ pullback.fst q t := by
  simp [pullbackParameterProductIso, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem pullbackParameterProductIso_hom_second :
    (pullbackParameterProductIso q r t).hom ≫ pullback.fst (pullback.fst q r ≫ q) t ≫
      pullback.snd q r = pullback.snd (pullback.fst q t ≫ q) r := by
  simp [pullbackParameterProductIso, pullback.map, Category.assoc]

@[reassoc (attr := simp)]
theorem pullbackParameterProductIso_hom_parameter :
    (pullbackParameterProductIso q r t).hom ≫ pullback.snd (pullback.fst q r ≫ q) t =
      pullback.fst (pullback.fst q t ≫ q) r ≫ pullback.snd q t := by
  simp [pullbackParameterProductIso, pullback.map, Category.assoc]

end Product

section Quotient

variable (q : Q ⟶ S) (r : P ⟶ S) (t : T ⟶ S) (l : P ⟶ T) (hl : l ≫ t = r)

local notation "QT" => pullback q t
local notation "A" => pullback (pullback.fst q t ≫ q) r
local notation "D" => pullback q r

/-- The two parameters in the uncut product, with the free parameter first. -/
def pullbackParameterPair : A ⟶ pullback t t :=
  pullback.lift (pullback.fst _ r ≫ pullback.snd q t) (pullback.snd _ r ≫ l) (by
    calc
      _ = pullback.fst (pullback.fst q t ≫ q) r ≫ (pullback.snd q t ≫ t) :=
        Category.assoc _ _ _
      _ = pullback.fst (pullback.fst q t ≫ q) r ≫ (pullback.fst q t ≫ q) :=
        congrArg (pullback.fst (pullback.fst q t ≫ q) r ≫ ·) pullback.condition.symm
      _ = pullback.snd (pullback.fst q t ≫ q) r ≫ r := pullback.condition
      _ = _ := by rw [Category.assoc, hl])

@[reassoc (attr := simp)]
theorem pullbackParameterPair_fst :
    pullbackParameterPair q r t l hl ≫ pullback.fst t t =
      pullback.fst _ r ≫ pullback.snd q t :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pullbackParameterPair_snd :
    pullbackParameterPair q r t l hl ≫ pullback.snd t t = pullback.snd _ r ≫ l :=
  pullback.lift_snd _ _ _

/-- Insert the right-hand graph parameter in the uncut product. -/
def pullbackParameterGraphInclusion : D ⟶ A :=
  pullback.lift
    (pullback.lift (pullback.fst q r) (pullback.snd q r ≫ l)
      (by rw [Category.assoc, hl, pullback.condition]))
    (pullback.snd q r) (by
      rw [← Category.assoc, pullback.lift_fst]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem pullbackParameterGraphInclusion_first :
    pullbackParameterGraphInclusion q r t l hl ≫ pullback.fst _ r ≫ pullback.fst q t =
      pullback.fst q r := by
  simp [pullbackParameterGraphInclusion]

@[reassoc (attr := simp)]
theorem pullbackParameterGraphInclusion_parameter :
    pullbackParameterGraphInclusion q r t l hl ≫ pullback.fst _ r ≫ pullback.snd q t =
      pullback.snd q r ≫ l := by
  simp [pullbackParameterGraphInclusion]

@[reassoc (attr := simp)]
theorem pullbackParameterGraphInclusion_second :
    pullbackParameterGraphInclusion q r t l hl ≫ pullback.snd _ r = pullback.snd q r :=
  pullback.lift_snd _ _ _

/-- Matching the two parameters cuts out the actual graph over the original
product, retaining its scheme structure. -/
theorem pullbackParameterGraph_isPullback :
    IsPullback (pullbackParameterGraphInclusion q r t l hl) (pullback.snd q r ≫ l)
      (pullbackParameterPair q r t l hl) (pullback.diagonal t) where
  w := by
    apply pullback.hom_ext <;> simp [Category.assoc]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun c => by
    have h₁ : c.fst ≫ pullback.fst _ r ≫ pullback.snd q t = c.snd := by
      simpa [Category.assoc] using
        congrArg (fun m => m ≫ pullback.fst t t) c.condition
    have h₂ : c.fst ≫ pullback.snd _ r ≫ l = c.snd := by
      simpa [Category.assoc] using
        congrArg (fun m => m ≫ pullback.snd t t) c.condition
    let m : c.pt ⟶ D := pullback.lift (c.fst ≫ pullback.fst _ r ≫ pullback.fst q t)
      (c.fst ≫ pullback.snd _ r) (by simp only [Category.assoc, ← pullback.condition])
    refine ⟨m, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [m, Category.assoc]
        · simpa [m, Category.assoc] using h₂.trans h₁.symm
      · simp [m, Category.assoc]
    · simpa [m, Category.assoc] using h₂
    · intro n hn _
      change n ≫ pullbackParameterGraphInclusion q r t l hl = c.fst at hn
      apply pullback.hom_ext (f := q) (g := r)
      · simpa [m, Category.assoc] using
          congrArg (fun a => a ≫ pullback.fst _ r ≫ pullback.fst q t) hn
      · simpa [m, Category.assoc] using congrArg (fun a => a ≫ pullback.snd _ r) hn)⟩

end Quotient

end CategoryTheory.Limits
