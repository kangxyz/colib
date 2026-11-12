/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.StrictLocalBaseChange.Normal
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.RetainedGeometry
public import Colib.AlgebraicGeometry.Sites.Etale.StrictHenselizationRegular

/-!
# Actual integral components of strict-local compactifications

Start with a normal proper compactification over the original locally Noetherian base. Its
pullback along the canonical strict-henselization map is normal and locally Noetherian, without
being assumed integral or smooth over the original field. Two sections of its retained smooth
open with the same specialization land in one actual integral clopen component. The retained
open and full finite boundary are their actual successive pullbacks; every original section
map is preserved.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Finite type over the actual Noetherian strict henselization gives local Noetherianity. -/
theorem isLocallyNoetherian_pullback_strictHenselizationToBase
    (B : BigEtaleSite.{u}) {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (hS : B.Contains S) (s : GeometricPoint S) (p : X ⟶ S) [LocallyOfFiniteType p] :
    IsLocallyNoetherian (pullback p (strictHenselizationToBase B S hS s)) := by
  have := isNoetherian_strictHenselization B S hS s
  exact LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p
    (strictHenselizationToBase B S hS s))

namespace Scheme

/-- Restrict the retained open after an arbitrary base change, preserving smooth dimension. -/
theorem smoothOfRelativeDimension_pullback_retainedOpen
    {X Y S T : Scheme.{u}} (p : X ⟶ S) (j : Y ⟶ X) (g : T ⟶ S)
    (n : ℕ) [SmoothOfRelativeDimension n (j ≫ p)] :
    SmoothOfRelativeDimension n
      (pullback.fst (pullback.fst p g) j ≫ pullback.snd p g) := by
  have h := (IsPullback.of_hasPullback (pullback.fst p g) j).flip.paste_vert
    (IsPullback.of_hasPullback p g)
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n) h inferInstance

/-- The full boundary remains finite after an arbitrary base change, with its original scheme
structure transported by the actual pullback. -/
theorem isFinite_pullback_retainedBoundary
    {X D S T : Scheme.{u}} (p : X ⟶ S) (b : D ⟶ X) (g : T ⟶ S)
    [IsFinite (b ≫ p)] :
    IsFinite (pullback.fst (pullback.fst p g) b ≫ pullback.snd p g) := by
  have h := (IsPullback.of_hasPullback (pullback.fst p g) b).flip.paste_vert
    (IsPullback.of_hasPullback p g)
  exact MorphismProperty.of_isPullback (P := @IsFinite) h inferInstance

/-- Construct an actual integral proper component after the native strict-local base change.
Both sections of the unchanged base-changed retained open, its smooth curve structure and its
full finite boundary are retained. Projectivity, when present, also restricts to this same
component. No component provider or integrality of the whole base change is assumed. -/
theorem exists_integral_component_strictLocal_retaining_sections
    (B : BigEtaleSite.{u}) {S X Y D : Scheme.{u}} [IsLocallyNoetherian S] [IsNormal X]
    (hS : B.Contains S) (s : GeometricPoint S) (p : X ⟶ S) [IsProper p]
    (j : Y ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ p)]
    (b : D ⟶ X) [IsClosedImmersion b] [IsFinite (b ≫ p)]
    (hb : Set.range b = (Set.range j)ᶜ)
    (s₀ s₁ : strictHenselization B S hS s ⟶
      pullback (pullback.fst p (strictHenselizationToBase B S hS s)) j)
    (h₀ : s₀ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B S hS s)) j ≫
      pullback.snd p (strictHenselizationToBase B S hS s) = 𝟙 _)
    (h₁ : s₁ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B S hS s)) j ≫
      pullback.snd p (strictHenselizationToBase B S hS s) = 𝟙 _)
    (hs : (s₀ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B S hS s)) j)
        (IsLocalRing.closedPoint ↥(etaleLocalRing B S hS s)) =
      (s₁ ≫ pullback.fst (pullback.fst p (strictHenselizationToBase B S hS s)) j)
        (IsLocalRing.closedPoint ↥(etaleLocalRing B S hS s))) :
    let g := strictHenselizationToBase B S hS s
    let j' := pullback.fst (pullback.fst p g) j
    let b' := pullback.fst (pullback.fst p g) b
    let p' := pullback.snd p g
    ∃ (U : (pullback p g : Scheme.{u}).Opens)
      (t₀ t₁ : strictHenselization B S hS s ⟶ pullback U.ι j'),
      (U : Set (pullback p g : Scheme.{u})) = _root_.irreducibleComponent
        ((s₀ ≫ j') (IsLocalRing.closedPoint ↥(etaleLocalRing B S hS s))) ∧
      IsIntegral U.toScheme ∧ IsNormal U.toScheme ∧ IsLocallyNoetherian U.toScheme ∧
      IsClosedImmersion U.ι ∧ IsProper (U.ι ≫ p') ∧
      (IsProjectiveMorphism p → IsProjectiveMorphism (U.ι ≫ p')) ∧
      IsIntegral (pullback U.ι j') ∧ IsOpenImmersion (pullback.fst U.ι j') ∧
      SmoothOfRelativeDimension 1 (pullback.fst U.ι j' ≫ U.ι ≫ p') ∧
      IsClosedImmersion (pullback.fst U.ι b') ∧
      IsFinite (pullback.fst U.ι b' ≫ U.ι ≫ p') ∧
      Set.range (pullback.fst U.ι b') = (Set.range (pullback.fst U.ι j'))ᶜ ∧
      t₀ ≫ pullback.snd U.ι j' = s₀ ∧ t₁ ≫ pullback.snd U.ι j' = s₁ ∧
      t₀ ≫ pullback.fst U.ι j' ≫ U.ι = s₀ ≫ j' ∧
      t₁ ≫ pullback.fst U.ι j' ≫ U.ι = s₁ ≫ j' ∧
      t₀ ≫ pullback.fst U.ι j' ≫ U.ι ≫ p' = 𝟙 _ ∧
      t₁ ≫ pullback.fst U.ι j' ≫ U.ι ≫ p' = 𝟙 _ := by
  intro g j' b' p'
  have := isNormal_pullback_strictHenselizationToBase B hS s p
  have := isLocallyNoetherian_pullback_strictHenselizationToBase B hS s p
  have : SmoothOfRelativeDimension 1 (j' ≫ p') :=
    smoothOfRelativeDimension_pullback_retainedOpen p j g 1
  have : IsFinite (b' ≫ p') := isFinite_pullback_retainedBoundary p b g
  have hb' : Set.range b' = (Set.range j')ᶜ := by
    dsimp [b', j']
    rw [Pullback.range_fst, Pullback.range_fst, hb]
    rfl
  obtain ⟨U, t₀, t₁, hcomp, hint, hn, hln, hc, hp, hrest⟩ :=
    exists_integral_component_retaining_sections p' j' b' hb' s₀ s₁ h₀ h₁ hs
  refine ⟨U, t₀, t₁, hcomp, hint, hn, hln, hc, hp, ?_, hrest⟩
  intro hproj
  obtain ⟨n, i, hi, heq⟩ := hproj.baseChange g
  have := hc
  have := hi
  exact ⟨n, U.ι ≫ i, inferInstance, by rw [Category.assoc, heq]⟩

end Scheme

end AlgebraicGeometry
