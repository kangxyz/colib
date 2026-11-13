/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.RestrictedThickenedBoundary
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.PairedNormRefinement

/-!
# The whole boundary in the original paired coefficient diagram

The compactification and the marked square use the literal parameter
pullbacks of the paired section construction. The same thickening retains
both the full inverse infinity and the whole residual marked scheme.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification

open PolynomialLaurent RelativeCurve.NativeProjectiveLine RelativeCurvePencil.RelativeBase

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
  {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of R[X]))
  [Etale p] [QuasiCompact p] [IsSeparated p] [IsFinite (toProjectiveLine R p)]
  (z : Z ⟶ Spec (.of R[X])) [IsClosedImmersion z]
  [IsFinite (z ≫ polynomialProjection (.of R))]
  (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 Z) p z)
  (O : (Spec (.of R)).Opens)

local notation "q" => (polynomialProjection (.of R))
local notation "π" => (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))
local notation "f" => (toProjectiveLine R p)
local notation "j" => (inclusion R p)
local notation "jA" => (chart R)
local notation "hA" => ((chart_projection R).trans (Category.id_comp q).symm)
local notation "hB" => (inclusion_projection R p)
local notation "F₁" => (sourceBaseMap π O f)
local notation "π₁" => (compactificationProjection π O)
local notation "πB₁" => (compactificationProjection (f ≫ π) O)
local notation "jB₁" => (firstInclusion q ⊤ O (f ≫ π) j p hB)
local notation "jA₁" => (targetInclusion q O π jA hA)
local notation "p₁" => (firstMap q ⊤ O p)
local notation "z₁" => (markToParameter q ⊤ O z (fun _ _ ↦ trivial))
local notation "s₁" => (closedLift q ⊤ O z (fun _ _ ↦ trivial) p s hs)
local notation "H₁" => (closedLift_isPullback q ⊤ O z (fun _ _ ↦ trivial) p s hs H)
local notation "hRet₁" => (firstInclusion_comp_coefficientMap q O π jA hA f j p
  (inclusion_toProjectiveLine R p) hB)
local notation "m₁" => (z₁ ≫ jA₁)
local notation "Hmark" => (pairedMark_isPullback F₁ jB₁ jA₁ p₁ hRet₁ z₁ s₁ H₁)
local notation "hmark" => (markedSection_original_equation F₁ jB₁ m₁ s₁ Hmark)
local notation "d₀" => (sourceBaseMap (f ≫ π) O (infinityInclusion R p))
local notation "d∞" => (sourceBaseMap π O (RelativeCurve.NativeProjectiveLine.infinity R))

/-- The actual whole source boundary for the paired choice on the first
coefficient open and the original whole first-source pullback. -/
theorem exists_pairedBoundary_on_coefficientOpen
    (hfinite : IsFinite ((infinityInclusion R p ≫ projection R p) ∣_ O)) :
    ∃ (D : Scheme.{u}) (d : D ⟶ (compactificationOpen (f ≫ π) O).toScheme),
      IsClosedImmersion d ∧ Set.range d = (Set.range jB₁)ᶜ ∧
      Disjoint (Set.range jB₁) (Set.range d) ∧
      IsClosedImmersion (s₁ ≫ jB₁) ∧ IsClosedImmersion m₁ ∧
      IsFinite (d ≫ πB₁) ∧
      ∃ (bI : pullback F₁ d∞ ⟶ D)
        (bE : (residualMarkedFiberOpen F₁ jB₁ m₁ s₁ hmark).toScheme ⟶ D),
        bI ≫ d = pullback.fst F₁ d∞ ∧
        bE ≫ d = residualMarkedFiberMap F₁ jB₁ m₁ s₁ hmark := by
  have hd : Set.range d₀ = (Set.range jB₁)ᶜ := by
    rw [sourceBaseMap_range_preimage, firstInclusion_range_preimage_top,
      range_infinityInclusion]
    rfl
  let : IsFinite (d₀ ≫ πB₁) := by
    rw [sourceBaseMap_projection]
    exact hfinite
  let : IsClosedImmersion (z ≫ jA) := markedProjective_closed R z
  let : IsClosedImmersion (s ≫ j) := by
    have : IsClosedImmersion ((s ≫ j) ≫ f) := by
      rw [markedSection_original_equation f j (z ≫ jA) s
        (pairedMark_isPullback f j jA p (inclusion_toProjectiveLine R p) z s H)]
      infer_instance
    exact IsClosedImmersion.of_comp _ f
  let : IsClosedImmersion m₁ := by
    rw [targetInclusion_mark]
    infer_instance
  have hi : Disjoint (Set.range jA₁) (Set.range d∞) :=
    targetInclusion_disjoint q O π jA hA (RelativeCurve.NativeProjectiveLine.infinity R) (by
      rw [range_infinity]
      exact disjoint_compl_right)
  obtain ⟨D, d, hclosed, hrange, hdisj, -, hfin, _, bE, bI, -, hbE, hbI⟩ :=
    exists_thickened_compactification_boundary F₁ πB₁ jB₁ d₀ hd m₁ s₁ hmark Hmark
      d∞ p₁ jA₁ (hRet₁).symm hi
  exact ⟨D, d, hclosed, hrange, hdisj, inferInstance, inferInstance, hfin, bI, bE, hbI, hbE⟩

end AlgebraicGeometry.Scheme.RelativeAffineLineEtaleCompactification
