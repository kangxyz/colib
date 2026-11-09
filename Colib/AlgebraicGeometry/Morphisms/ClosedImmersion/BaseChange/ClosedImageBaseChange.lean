/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base-changing a closed support inside a relative product

The literal base change of a support over its source maps into the base-changed
ambient product by a Cartesian square. Closed immersions are consequently
preserved, with no flatness or reducedness assumption on the base change.
The support is the entire scheme fibre product, including its nilpotents.
Finiteness of the support projection is preserved by arbitrary base change.

Adapted from `kangxyz/motivic` revision
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Morphisms/ClosedImmersion/BaseChange/ClosedImageBaseChange.lean`
(blob `f8d155783c2d1e82b44c535b39620a70aa1cc1f3`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ClosedImageBaseChange

variable {S X Y U C : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (u : U ⟶ S)
  (g : U ⟶ X) (hg : g ≫ x = u) (j : C ⟶ pullback x y)

/-- The actual map between the two ambient products. -/
def ambientMap : pullback u y ⟶ pullback x y :=
  pullback.map u y x y g (𝟙 Y) (𝟙 S) (by simpa using hg.symm) (by simp)

@[reassoc (attr := simp)]
theorem ambientMap_fst : ambientMap x y u g hg ≫ pullback.fst x y =
    pullback.fst u y ≫ g := by simp only [ambientMap, pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem ambientMap_snd : ambientMap x y u g hg ≫ pullback.snd x y =
    pullback.snd u y := by simp only [ambientMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The actual inclusion of the whole source-base-changed support. -/
def inclusion : pullback (j ≫ pullback.fst x y) g ⟶ pullback u y :=
  pullback.lift (pullback.snd (j ≫ pullback.fst x y) g)
    (pullback.fst (j ≫ pullback.fst x y) g ≫ j ≫ pullback.snd x y) (by
      calc
        _ = pullback.snd (j ≫ pullback.fst x y) g ≫ g ≫ x := by rw [hg]
        _ = pullback.fst (j ≫ pullback.fst x y) g ≫ j ≫
            pullback.fst x y ≫ x := by
          simpa only [Category.assoc] using
            (pullback.condition_assoc (f := j ≫ pullback.fst x y) (g := g) x).symm
        _ = _ := by simp only [pullback.condition, Category.assoc])

@[reassoc (attr := simp)]
theorem inclusion_fst : inclusion x y u g hg j ≫ pullback.fst u y =
    pullback.snd (j ≫ pullback.fst x y) g := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem inclusion_snd : inclusion x y u g hg j ≫ pullback.snd u y =
    pullback.fst (j ≫ pullback.fst x y) g ≫ j ≫ pullback.snd x y :=
  pullback.lift_snd _ _ _

/-- The literal support inclusion is the actual base change of the old inclusion. -/
theorem inclusion_isPullback :
    IsPullback (pullback.fst (j ≫ pullback.fst x y) g)
      (inclusion x y u g hg j) j (ambientMap x y u g hg) := by
  have hw : pullback.fst (j ≫ pullback.fst x y) g ≫ j =
      inclusion x y u g hg j ≫ ambientMap x y u g hg := by
    apply pullback.hom_ext
    · simp only [Category.assoc, ambientMap_fst, inclusion_fst_assoc]
      exact pullback.condition
    · simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk _ (fun c ↦
    pullback.lift c.fst (c.snd ≫ pullback.fst u y) (by
      have h := congrArg (fun f ↦ f ≫ pullback.fst x y) c.condition
      simpa only [Category.assoc, ambientMap_fst] using h)) ?_ ?_ ?_)
  · intro c
    exact pullback.lift_fst _ _ _
  · intro c
    apply pullback.hom_ext
    · simp only [Category.assoc, inclusion_fst, pullback.lift_snd]
    · have h := congrArg (fun f ↦ f ≫ pullback.snd x y) c.condition
      simpa only [Category.assoc, inclusion_snd, pullback.lift_fst_assoc,
        ambientMap_snd] using h
  · intro c m h₁ h₂
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using h₁
    · have h := congrArg (fun f ↦ f ≫ pullback.fst u y) h₂
      simpa only [Category.assoc, inclusion_fst, pullback.lift_snd] using h

/-- Closed supports remain closed in the actual new ambient product. -/
instance inclusion_isClosedImmersion [IsClosedImmersion j] :
    IsClosedImmersion (inclusion x y u g hg j) :=
  MorphismProperty.of_isPullback (inclusion_isPullback x y u g hg j) inferInstance

/-- The inclusion and ambient base-change map recover the original closed support map. -/
@[reassoc]
theorem inclusion_ambientMap :
    inclusion x y u g hg j ≫ ambientMap x y u g hg =
      pullback.fst (j ≫ pullback.fst x y) g ≫ j :=
  (inclusion_isPullback x y u g hg j).w.symm

/-- An arbitrary base change retains finiteness of the entire support over its source. -/
instance inclusion_finite_projection [IsFinite (j ≫ pullback.fst x y)] :
    IsFinite (inclusion x y u g hg j ≫ pullback.fst u y) := by
  rw [inclusion_fst]
  infer_instance

end AlgebraicGeometry.ClosedImageBaseChange
