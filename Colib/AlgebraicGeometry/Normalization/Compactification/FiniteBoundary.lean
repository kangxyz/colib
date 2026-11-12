/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.Compactification.NormalFiniteChart
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper normal compactifications with their entire finite boundary

Pull back a fixed finite boundary of the compact target along the actual finite normalization
cover. The resulting closed subscheme is finite over the unchanged base and its support is
exactly the complement of the original source. Its scheme structure is the actual pullback,
not a chosen finite subset of the complement. Properness comes from the original target.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- Normalize a proper Nagata target in a normal integral source finite over its open chart.
The pullback of the target's finite boundary is the full finite boundary of the constructed
proper normal compactification. All source and base maps are retained. -/
@[colib_tag "COL-1064"]
theorem exists_normal_proper_compactification_of_finite_chart
    {X Y Z S E : Scheme.{u}} [IsIntegral X] [IsNormal X] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) [IsFinite f] (j : Y ⟶ Z) [IsOpenImmersion j] [QuasiCompact j]
    (hZ : IsNagataScheme Z) (q : Z ⟶ S) [IsProper q]
    (d : E ⟶ Z) [IsClosedImmersion d] [IsFinite (d ≫ q)]
    (hd : Set.range d = (Set.range j)ᶜ) :
    ∃ (N D : Scheme.{u}) (i : X ⟶ N) (π : N ⟶ Z) (b : D ⟶ N) (e : D ⟶ E),
      IsIntegral N ∧ IsLocallyNoetherian N ∧ IsNormal N ∧
      IsOpenImmersion i ∧ IsFinite π ∧ IsProper (π ≫ q) ∧ IsClosedImmersion b ∧
      IsFinite (b ≫ π ≫ q) ∧ IsPullback b e π d ∧ Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = f ≫ j ∧ i ≫ π ≫ q = f ≫ j ≫ q := by
  obtain ⟨N, i, π, hN, hn, hnormal, hi, hπ, hfac, hrange⟩ :=
    exists_normal_finite_cover_of_nagata_finite_chart f j hZ
  have := hπ
  have : IsFinite (pullback.fst π d ≫ π ≫ q) := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
    infer_instance
  refine ⟨N, pullback π d, i, π, pullback.fst π d, pullback.snd π d, hN, hn, hnormal, hi, hπ,
    inferInstance, inferInstance, inferInstance, IsPullback.of_hasPullback π d, ?_, hfac, ?_⟩
  · rw [AlgebraicGeometry.Scheme.Pullback.range_fst, hd, hrange]
    rfl
  · rw [← Category.assoc, hfac, Category.assoc]

end AlgebraicGeometry.Scheme
