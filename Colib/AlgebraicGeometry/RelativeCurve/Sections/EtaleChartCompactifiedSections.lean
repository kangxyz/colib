/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.EtaleChart

/-!
# Original chart sections inside the pulled-back compactification

This is an unverified narrow wiring candidate. No normality, integrality, or
compactification-existence assertion is made here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleChart
variable {A Y Z U N : Scheme.{u}}
  (q : A ⟶ Z) (p : Z ⟶ Y) (s : Y ⟶ Z)
  (i : A ⟶ U) (f : U ⟶ Y) (hi : i ≫ f = q ≫ p)
  (j : U ⟶ N) (fN : N ⟶ Y) (hj : j ≫ fN = f)

/-- The actual compactification after the original chart refinement. -/
abbrev compactifiedCurve := pullback (original q p s ≫ (q ≫ p)) fN

/-- The unchanged retained curve maps into the actual compactification. -/
def retainedToCompactification : curve q p s f ⟶ compactifiedCurve q p s fN :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ j) (by
    rw [Category.assoc, hj]
    exact pullback.condition)

@[reassoc (attr := simp)] theorem retainedToCompactification_fst :
    retainedToCompactification q p s f j fN hj ≫ pullback.fst _ _ =
      pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem retainedToCompactification_snd :
    retainedToCompactification q p s f j fN hj ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ j := pullback.lift_snd _ _ _

/-- The original section, not a replacement graph, in the compactification. -/
def compactifiedOriginalSection : refinement q p s ⟶ compactifiedCurve q p s fN :=
  originalSection q p s i f hi ≫ retainedToCompactification q p s f j fN hj

/-- The original retraction section in the same compactification. -/
def compactifiedRetractSection (hs : s ≫ p = 𝟙 Y) :
    refinement q p s ⟶ compactifiedCurve q p s fN :=
  retractSection q p s i f hi hs ≫ retainedToCompactification q p s f j fN hj

@[reassoc (attr := simp)] theorem compactifiedOriginalSection_projection :
    compactifiedOriginalSection q p s i f hi j fN hj ≫ pullback.fst _ _ = 𝟙 _ := by
  simp [compactifiedOriginalSection, originalSection_projection]

@[reassoc (attr := simp)] theorem compactifiedRetractSection_projection
    (hs : s ≫ p = 𝟙 Y) :
    compactifiedRetractSection q p s i f hi j fN hj hs ≫ pullback.fst _ _ = 𝟙 _ := by
  simp [compactifiedRetractSection, retractSection_projection]

/-- The two unchanged original sections have the same field-valued mark. -/
theorem compactifiedSections_same_marking
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ A) (η : Spec (.of Ω) ⟶ Y)
    (hξ : ξ ≫ q = η ≫ s) (hs : s ≫ p = 𝟙 Y) :
    refinementMark q p s ξ η hξ hs ≫
        compactifiedOriginalSection q p s i f hi j fN hj =
      refinementMark q p s ξ η hξ hs ≫
        compactifiedRetractSection q p s i f hi j fN hj hs := by
  dsimp only [compactifiedOriginalSection, compactifiedRetractSection]
  rw [← Category.assoc, ← Category.assoc,
    sections_same_marking q p s ξ η hξ i f hi hs]

/-- The retained source still recovers the original chart target morphisms. -/
theorem retainedOriginal_target {T : Scheme.{u}} (t : U ⟶ T) :
    originalSection q p s i f hi ≫ (pullback.snd _ _ ≫ t) =
      original q p s ≫ (i ≫ t) := by
  rw [← Category.assoc, originalSection_target, Category.assoc]

/-- The retained source recovers the same original retract target morphism. -/
theorem retainedRetract_target {T : Scheme.{u}} (t : U ⟶ T)
    (hs : s ≫ p = 𝟙 Y) :
    retractSection q p s i f hi hs ≫ (pullback.snd _ _ ≫ t) =
      retract q p s ≫ (i ≫ t) := by
  rw [← Category.assoc, retractSection_target, Category.assoc]
end AlgebraicGeometry.Scheme.EtaleChart
