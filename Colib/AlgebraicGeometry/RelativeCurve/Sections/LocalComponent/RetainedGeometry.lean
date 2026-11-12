/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective

/-!
# Retain sections, the smooth open and the full boundary on a normal component

Restriction to the actual clopen component preserves properness and projectivity. The retained
smooth open and its entire finite boundary are their native pullbacks along the component
inclusion. In particular, the boundary's scheme structure is pulled back, rather than replaced
by the reduced closed support. Sections in the original open lift to its actual pullback, with
both projection identities retained.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

variable {X S Y D : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]

/-- The proper structure morphism restricts to the actual component. -/
instance isProper_normalComponentOpen (p : X ⟶ S) [IsProper p] (x : X) :
    IsProper ((normalComponentOpen x).ι ≫ p) := inferInstance

/-- The actual closed embedding in projective space restricts to the component. -/
theorem isProjectiveMorphism_normalComponentOpen (p : X ⟶ S)
    (hp : IsProjectiveMorphism p) (x : X) :
    IsProjectiveMorphism ((normalComponentOpen x).ι ≫ p) := by
  obtain ⟨n, i, hi, hcomp⟩ := hp
  have := hi
  exact ⟨n, (normalComponentOpen x).ι ≫ i, inferInstance, by rw [Category.assoc, hcomp]⟩

/-- The actual boundary pullback stays finite over the unchanged base. -/
instance isFinite_normalComponentBoundary (p : X ⟶ S) (b : D ⟶ X)
    [IsFinite (b ≫ p)] (x : X) :
    IsFinite (pullback.fst (normalComponentOpen x).ι b ≫ (normalComponentOpen x).ι ≫ p) := by
  rw [← Category.assoc, pullback.condition, Category.assoc]
  infer_instance

/-- The smooth relative dimension is unchanged on the retained open of the component. -/
theorem smoothOfRelativeDimension_normalComponentOpen (p : X ⟶ S) (j : Y ⟶ X)
    (n : ℕ) [SmoothOfRelativeDimension n (j ≫ p)] (x : X) :
    SmoothOfRelativeDimension n
      (pullback.fst (normalComponentOpen x).ι j ≫ (normalComponentOpen x).ι ≫ p) := by
  rw [← Category.assoc, pullback.condition, Category.assoc]
  have h : SmoothOfRelativeDimension (0 + n)
      (pullback.snd (normalComponentOpen x).ι j ≫ (j ≫ p)) :=
    smoothOfRelativeDimension_comp 0 n _ _
  rwa [Nat.zero_add] at h

/-- Pullback retains the whole boundary, with its original scheme structure. -/
theorem range_normalComponentBoundary (j : Y ⟶ X) (b : D ⟶ X)
    (hb : Set.range b = (Set.range j)ᶜ) (x : X) :
    Set.range (pullback.fst (normalComponentOpen x).ι b) =
      (Set.range (pullback.fst (normalComponentOpen x).ι j))ᶜ := by
  rw [Pullback.range_fst, Pullback.range_fst, hb]
  rfl

/-- Two original sections of a retained smooth open, agreeing after specialization, are
preserved on one actual integral proper component and its smooth open. The entire original
finite boundary is restricted by the actual pullback, including its scheme structure. -/
theorem exists_integral_component_retaining_sections
    {R : CommRingCat.{u}} [IsLocalRing R] (p : X ⟶ Spec R) [IsProper p]
    (j : Y ⟶ X) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ p)]
    (b : D ⟶ X) [IsClosedImmersion b] [IsFinite (b ≫ p)]
    (hb : Set.range b = (Set.range j)ᶜ)
    (s₀ s₁ : Spec R ⟶ Y) (h₀ : s₀ ≫ j ≫ p = 𝟙 _) (h₁ : s₁ ≫ j ≫ p = 𝟙 _)
    (hs : (s₀ ≫ j) (IsLocalRing.closedPoint R) =
      (s₁ ≫ j) (IsLocalRing.closedPoint R)) :
    ∃ (U : X.Opens) (t₀ t₁ : Spec R ⟶ pullback U.ι j),
      (U : Set X) = irreducibleComponent
        ((s₀ ≫ j) (IsLocalRing.closedPoint R)) ∧
      IsIntegral U.toScheme ∧ IsNormal U.toScheme ∧ IsLocallyNoetherian U.toScheme ∧
      IsClosedImmersion U.ι ∧ IsProper (U.ι ≫ p) ∧
      IsIntegral (pullback U.ι j) ∧ IsOpenImmersion (pullback.fst U.ι j) ∧
      SmoothOfRelativeDimension 1 (pullback.fst U.ι j ≫ U.ι ≫ p) ∧
      IsClosedImmersion (pullback.fst U.ι b) ∧
      IsFinite (pullback.fst U.ι b ≫ U.ι ≫ p) ∧
      Set.range (pullback.fst U.ι b) = (Set.range (pullback.fst U.ι j))ᶜ ∧
      t₀ ≫ pullback.snd U.ι j = s₀ ∧ t₁ ≫ pullback.snd U.ι j = s₁ ∧
      t₀ ≫ pullback.fst U.ι j ≫ U.ι = s₀ ≫ j ∧
      t₁ ≫ pullback.fst U.ι j ≫ U.ι = s₁ ≫ j ∧
      t₀ ≫ pullback.fst U.ι j ≫ U.ι ≫ p = 𝟙 _ ∧
      t₁ ≫ pullback.fst U.ι j ≫ U.ι ≫ p = 𝟙 _ := by
  let x := (s₀ ≫ j) (IsLocalRing.closedPoint R)
  let U := normalComponentOpen x
  have hmem₀ : (s₀ ≫ j) (IsLocalRing.closedPoint R) ∈ U := mem_normalComponentOpen x
  have hmem₁ : (s₁ ≫ j) (IsLocalRing.closedPoint R) ∈ U := hs ▸ hmem₀
  let a₀ := liftToNormalComponent (s₀ ≫ j) x hmem₀
  let a₁ := liftToNormalComponent (s₁ ≫ j) x hmem₁
  have ha₀ : a₀ ≫ U.ι = s₀ ≫ j := liftToNormalComponent_ι _ _ _
  have ha₁ : a₁ ≫ U.ι = s₁ ≫ j := liftToNormalComponent_ι _ _ _
  let t₀ := pullback.lift a₀ s₀ ha₀
  let t₁ := pullback.lift a₁ s₁ ha₁
  have : Nonempty (pullback U.ι j : Scheme.{u}) := ⟨t₀ (IsLocalRing.closedPoint R)⟩
  have : IsIntegral (pullback U.ι j) := isIntegral_of_isOpenImmersion (pullback.fst U.ι j)
  refine ⟨U, t₀, t₁, rfl, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance,
    smoothOfRelativeDimension_normalComponentOpen p j 1 x,
    inferInstance, inferInstance, range_normalComponentBoundary j b hb x,
    pullback.lift_snd _ _ _, pullback.lift_snd _ _ _, ?_, ?_, ?_, ?_⟩
  · simp only [t₀, pullback.lift_fst_assoc, ha₀]
  · simp only [t₁, pullback.lift_fst_assoc, ha₁]
  · rw [show t₀ ≫ pullback.fst U.ι j ≫ U.ι ≫ p = (a₀ ≫ U.ι) ≫ p by
      simp only [t₀, pullback.lift_fst_assoc, Category.assoc], ha₀, Category.assoc, h₀]
  · rw [show t₁ ≫ pullback.fst U.ι j ≫ U.ι ≫ p = (a₁ ≫ U.ι) ≫ p by
      simp only [t₁, pullback.lift_fst_assoc, Category.assoc], ha₁, Category.assoc, h₁]

end AlgebraicGeometry.Scheme
