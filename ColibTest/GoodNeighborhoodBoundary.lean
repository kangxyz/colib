/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Normalization.Compactification.NonemptyBoundary
import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.NonemptyBoundary
import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.Integral

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.RelativeCurve PrincipalFamilyUnitOpen

universe u

noncomputable section

/-- The actual infinity square and full boundary support from the same-tuple producer imply
nonemptiness of the actual retained-boundary preimage over every marked base neighborhood. -/
example (R : Type u) [CommRing R]
    {X N D : Scheme.{u}} (i : X ⟶ N) [IsOpenImmersion i]
    (π : N ⟶ projectiveLine R) [Surjective π]
    (b : D ⟶ N) (e : D ⟶ Spec (.of R))
    (hpb : IsPullback b e π (projectiveLineInfinitySection R))
    (hboundary : Set.range b = (Set.range i)ᶜ)
    (W : X.Opens) (T : (Spec (.of R)).Opens) (s : Spec (.of R)) (hs : s ∈ T) :
    Nonempty (((retainedBoundaryInclusion (i ''ᵁ W) ≫ π ≫
      (projectiveLine R ↘ Spec (.of R))) ⁻¹ᵁ T).toScheme) := by
  have : Surjective e := Scheme.surjective_infinity_pullback R π b e hpb
  have hbase : b ≫ π ≫ (projectiveLine R ↘ Spec (.of R)) = e := by
    rw [← Category.assoc, hpb.w, Category.assoc,
      projectiveLineInfinitySection_comp_structureMorphism, Category.comp_id]
  have : Surjective (b ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) := by
    rw [hbase]
    infer_instance
  have : Surjective (retainedBoundaryInclusion (i ''ᵁ W) ≫ π ≫
      (projectiveLine R ↘ Spec (.of R))) := by
    apply surjective_retainedBoundary _ b
    intro x hx hxW
    rw [hboundary] at hx
    obtain ⟨y, _, hy⟩ := hxW
    exact hx ⟨y, hy⟩
  exact nonempty_retainedBoundary_preimage _ _ T s hs

/-- A point retained in the original affine open proves integrality after the base shrink. -/
example {X N S : Scheme.{u}} [IsIntegral N] (i : X ⟶ N) [IsOpenImmersion i]
    (q : N ⟶ S) (W : X.Opens) (T : S.Opens) (x : X) (hx : x ∈ W)
    (hT : q (i x) ∈ T) : IsIntegral ((((i ''ᵁ W).ι ≫ q) ⁻¹ᵁ T).toScheme) := by
  have : Nonempty (i ''ᵁ W).toScheme := ⟨⟨i x, ⟨x, hx, rfl⟩⟩⟩
  have : IsIntegral (i ''ᵁ W).toScheme := isIntegral_of_isOpenImmersion (i ''ᵁ W).ι
  exact Scheme.isIntegral_preimage_of_mem ((i ''ᵁ W).ι ≫ q) T ⟨i x, ⟨x, hx, rfl⟩⟩ hT

/-- A section-unit open containing the actual nonempty boundary is integral. -/
example {N W B : Scheme.{u}} [IsIntegral N] (w : W ⟶ N) [IsOpenImmersion w]
    (b : B ⟶ W) [Nonempty B] : IsIntegral W := by
  have : Nonempty W := ⟨b (Classical.choice inferInstance)⟩
  exact isIntegral_of_isOpenImmersion w

/-- The principal action's original ambient cylinder receives both required properties. -/
example {k : Type u} [Field k] {N : Scheme.{u}} [IsIntegral N] [IsNoetherian N]
    (p : N ⟶ Spec (.of k)) :
    IsIntegral (parameterSpace p) ∧ IsNoetherian (parameterSpace p) :=
  ⟨isIntegral_parameterSpace p, isNoetherian_parameterSpace p⟩

/-- Restriction of the actual proper compactification is Noetherian; its integrality uses
an actual retained point rather than an inferred nonempty-open premise. -/
example {N S : Scheme.{u}} [IsIntegral N] [IsLocallyNoetherian N] [CompactSpace S]
    (q : N ⟶ S) [IsProper q] (T : S.Opens) (x : N) (hx : q x ∈ T) :
    IsIntegral ((q ⁻¹ᵁ T).toScheme) ∧ IsNoetherian ((q ⁻¹ᵁ T).toScheme) := by
  have : CompactSpace N := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian N := {}
  have : CompactSpace ((q ⁻¹ᵁ T).toScheme) :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact (q ⁻¹ᵁ T : Set N))
  exact ⟨Scheme.isIntegral_preimage_of_mem q T x hx, AlgebraicGeometry.IsNoetherian.mk⟩

#print axioms Scheme.surjective_projectiveLine_cover_of_etale_away
#print axioms surjective_retainedBoundary
#print axioms isIntegral_parameterSpace
#print axioms isNoetherian_parameterSpace

end
