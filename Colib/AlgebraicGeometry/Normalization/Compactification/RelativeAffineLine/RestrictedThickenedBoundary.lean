/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.RestrictMarkedSquare
public import Colib.AlgebraicGeometry.Normalization.Compactification.Boundary.ThickenedBoundary
public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.Basic

/-!
# The full thickened boundary after one coefficient restriction

The relative normalization, source and mark restrict along the same
coefficient open. The resulting boundary contains the whole residual
marked fiber and the inverse image of target infinity, through their
literal maps into the restricted compactification.

Adapted from Motivic at a6805c4a87cdfd7717dd7a94039246a167f15380,
`Normalization/Compactification/RelativeAffineLine/RestrictedThickenedBoundary.lean`
under `Motivic/Aglib/AlgebraicGeometry`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.RelativeCurve

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R)))
  [Etale p] [QuasiCompact p] [IsSeparated p]
  (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y)

local notation "π" => (projectiveSpaceOverRing 1 (CommRingCat.of R) ↘ Spec (CommRingCat.of R))

omit [IsSeparated p] in
/-- The original marked square remains Cartesian in the native projective chart. -/
theorem marked_projective_isPullback (H : IsPullback s (𝟙 Z) p z) :
    IsPullback s (𝟙 Z) (inclusion R p ≫ toProjectiveLine R p)
      (z ≫ NativeProjectiveLine.chart R) := by
  rw [inclusion_toProjectiveLine]
  have h : IsPullback z (𝟙 Z) (NativeProjectiveLine.chart R) (z ≫ NativeProjectiveLine.chart R) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa only [Category.id_comp] using H.paste_vert h

omit [IsNoetherianRing R] in
/-- A finite mark in the original affine chart is closed in the whole projective line. -/
theorem markedProjective_closed [IsClosedImmersion z]
    [IsFinite (z ≫ polynomialProjection (.of R))] :
    IsClosedImmersion (z ≫ NativeProjectiveLine.chart R) := by
  have : IsProper ((z ≫ NativeProjectiveLine.chart R) ≫ π) := by
    rw [Category.assoc, NativeProjectiveLine.chart_projection, ← polynomialProjection]
    infer_instance
  have : IsProper (z ≫ NativeProjectiveLine.chart R) := IsProper.of_comp _ π
  exact IsClosedImmersion.of_isPreimmersion _
    (z ≫ NativeProjectiveLine.chart R).isClosedMap.isClosed_range

attribute [local instance] markedProjective_closed

variable (H : IsPullback s (𝟙 Z) p z) (O : (Spec (.of R)).Opens)

/-- The actual preimage of the coefficient open in the projective line. -/
abbrev projectiveCoefficientOpen : (projectiveSpaceOverRing 1 (.of R)).Opens :=
  π ⁻¹ᵁ O

/-- The actual preimage of the coefficient open in the source normalization. -/
abbrev compactificationCoefficientOpen : (compactification R p).Opens :=
  toProjectiveLine R p ⁻¹ᵁ projectiveCoefficientOpen R O

local notation "V" => (projectiveCoefficientOpen R O)
local notation "C₀" => (compactificationCoefficientOpen R p O)
local notation "F₀" => (toProjectiveLine R p ∣_ V)
local notation "j₀" => (inclusion R p ∣_ C₀)
local notation "z₀" => ((z ≫ NativeProjectiveLine.chart R) ∣_ V)
local notation "s₀" => restrictMarkedSection (marked_projective_isPullback R p z s H) V
local notation "q₀" => (projection R p ∣_ O)
local notation "d₀" => (infinityInclusion R p ∣_ C₀)
local notation "i₀" => (NativeProjectiveLine.infinity R ∣_ V)

omit [IsSeparated p] in
/-- The restricted marking retains its full original Cartesian square. -/
theorem restrictedMarkedSection_isPullback : IsPullback s₀ (𝟙 _) (j₀ ≫ F₀) z₀ := by
  simpa only [morphismRestrict_comp] using
    restrictMarkedSection_isPullback (marked_projective_isPullback R p z s H) V

omit [IsSeparated p] in
/-- The marked map identifies its image on the actual restricted projective line. -/
theorem restrictedMarkedSection_projective : (s₀ ≫ j₀) ≫ F₀ = z₀ := by
  simpa only [Category.assoc, Category.id_comp] using
    (restrictedMarkedSection_isPullback R p z s H O).w

local notation "h₀" => restrictedMarkedSection_projective R p z s H O

/-- The closed boundary on the actual coefficient open retains both additional
schemes through their original maps. -/
theorem exists_restricted_thickened_boundary [IsFinite (toProjectiveLine R p)]
    [IsClosedImmersion z] [IsFinite (z ≫ polynomialProjection (.of R))]
    (hfinite : IsFinite ((infinityInclusion R p ≫ projection R p) ∣_ O)) :
    ∃ (D : Scheme.{u}) (d : D ⟶ (C₀).toScheme),
      IsClosedImmersion d ∧ Set.range d = (Set.range j₀)ᶜ ∧
      Disjoint (Set.range j₀) (Set.range d) ∧
      Disjoint (Set.range (s₀ ≫ j₀)) (Set.range d) ∧ IsFinite (d ≫ q₀) ∧
      ∃ (a : (infinityInclusion R p ⁻¹ᵁ C₀).toScheme ⟶ D)
        (b : (residualMarkedFiberOpen F₀ j₀ z₀ s₀ h₀).toScheme ⟶ D)
        (c : pullback F₀ i₀ ⟶ D),
        a ≫ d = d₀ ∧ b ≫ d = residualMarkedFiberMap F₀ j₀ z₀ s₀ h₀ ∧
          c ≫ d = pullback.fst F₀ i₀ := by
  let : IsProper (projection R p) := by
    unfold projection
    infer_instance
  let : IsFinite (d₀ ≫ q₀) := by
    change IsFinite ((infinityInclusion R p ∣_ projection R p ⁻¹ᵁ O) ≫ q₀)
    rw [← morphismRestrict_comp]
    exact hfinite
  have hd : Set.range d₀ = (Set.range j₀)ᶜ :=
    range_morphismRestrict_complement (inclusion R p) (infinityInclusion R p) C₀
      (range_infinityInclusion R p)
  have he : inclusion R p ⁻¹ᵁ C₀ = p ⁻¹ᵁ NativeProjectiveLine.chart R ⁻¹ᵁ V := by
    calc
      _ = (inclusion R p ≫ toProjectiveLine R p) ⁻¹ᵁ V :=
        (Scheme.Hom.comp_preimage _ _ _).symm
      _ = (p ≫ NativeProjectiveLine.chart R) ⁻¹ᵁ V :=
        congrArg (fun f : Y ⟶ projectiveSpaceOverRing 1 (.of R) ↦ f ⁻¹ᵁ V)
          (inclusion_toProjectiveLine R p)
      _ = _ := Scheme.Hom.comp_preimage _ _ _
  let e := Y.isoOfEq he
  have heι : e.hom ≫ (p ⁻¹ᵁ NativeProjectiveLine.chart R ⁻¹ᵁ V).ι =
      (inclusion R p ⁻¹ᵁ C₀).ι := Scheme.isoOfEq_hom_ι Y he
  let a := NativeProjectiveLine.chart R ∣_ V
  let p₀ := e.hom ≫ (p ∣_ NativeProjectiveLine.chart R ⁻¹ᵁ V)
  have hp₀ : p₀ ≫ a = j₀ ≫ F₀ := by
    apply (cancel_mono (V).ι).mp
    simp only [p₀, a, Category.assoc, morphismRestrict_ι,
      morphismRestrict_ι_assoc, inclusion_toProjectiveLine]
    rw [← Category.assoc e.hom, heι]
  have hi : Disjoint (Set.range a) (Set.range i₀) := by
    rw [range_morphismRestrict_complement _ _ V (NativeProjectiveLine.range_infinity R)]
    exact disjoint_compl_right
  exact exists_thickened_compactification_boundary F₀ q₀ j₀ d₀ hd z₀ s₀ h₀
    (restrictedMarkedSection_isPullback R p z s H O) i₀ p₀ a hp₀ hi

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
