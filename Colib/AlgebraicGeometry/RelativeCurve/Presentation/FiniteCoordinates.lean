/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.Compactification.FiniteCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Compactification.Retained.CompactNeighborhood

/-!
# Good relative-curve geometry from the original finite coordinates

Construct the normal finite projective-line cover, transport the original affine smooth open,
and produce a principal base shrink on which its full enlarged boundary is finite. The given
finite prescribed scheme is retained over the same shrink. The scheme maps are the original
coordinate maps, not newly selected projections.

This is the geometric consumer of the finite-coordinate and whole-fibre conclusions of a
parameter-selection theorem. Finiteness of the original polynomial map and whole-fibre
containment remain explicit inputs; the finite normal compactification and the finite enlarged
boundary are actual conclusions. The simultaneous parameter-selection theorem is not assumed
as an unspecified certificate or claimed proved by this file.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- A finite polynomial coordinate map and an affine smooth open containing the whole marked
fibre give a normal proper finite projective-line cover and a principal neighborhood where the
full enlarged boundary is finite and the full prescribed finite scheme stays in that open. -/
@[colib_tag "COL-1069", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/NagataNormalization/Basic.lean:208-222"
  "ingredient" "Nagata finiteness of relative normalization in the compactification \
    ingredient; retained geometry is assembled here."]
theorem exists_good_neighborhood_of_finite_polynomial_coordinates
    (k R B : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    (f : Polynomial R →+* B) (hf : f.Finite)
    (W : (Spec (.of B)).Opens) [IsAffine W.toScheme]
    [SmoothOfRelativeDimension 1
      (W.ι ≫ Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)))]
    (s : Spec (.of R))
    (hW : ∀ x : Spec (.of B), Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) x = s → x ∈ W)
    {Z : Scheme.{u}} (z : Z ⟶ Spec (.of B))
    [IsFinite (z ≫ Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)))] :
    ∃ (N D : Scheme.{u}) (i : Spec (.of B) ⟶ N) (π : N ⟶ projectiveLine R)
      (b : D ⟶ N) (e : D ⟶ Spec (.of R)) (t : R) (hi : IsOpenImmersion i),
      letI := hi;
      IsIntegral N ∧ IsLocallyNoetherian N ∧ IsNormal N ∧
      IsFinite π ∧ IsProper (π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsClosedImmersion b ∧ IsFinite (b ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsPullback b e π (projectiveLineInfinitySection R) ∧
      Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = Spec.map (CommRingCat.ofHom f) ≫ projectiveLineXChart R ∧
      i ≫ π ≫ (projectiveLine R ↘ Spec (.of R)) =
        Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) ∧
      s ∈ PrimeSpectrum.basicOpen t ∧ IsAffine (i ''ᵁ W).toScheme ∧
      SmoothOfRelativeDimension 1 ((i ''ᵁ W).ι ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsFinite ((retainedBoundaryInclusion (i ''ᵁ W) ≫ π ≫
        (projectiveLine R ↘ Spec (.of R))) ∣_ PrimeSpectrum.basicOpen t) ∧
      IsAffine ((((i ''ᵁ W).ι ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ⁻¹ᵁ
        PrimeSpectrum.basicOpen t).toScheme) ∧
      ∀ x : Z, (z ≫ Spec.map (CommRingCat.ofHom (f.comp Polynomial.C))) x ∈
        PrimeSpectrum.basicOpen t → (z ≫ i) x ∈ i ''ᵁ W := by
  obtain ⟨N, D, i, π, b, e, hN, hn, hnormal, hi, hπ, hp, hb, hfinite, hpb, hr, hfac, hbase⟩ :=
    Scheme.exists_normal_projectiveLine_cover_of_finite_polynomial_map k R B f hf
  have := hi
  have := hp
  have := hfinite
  obtain ⟨t, ht, ha, hsm, hnew, ha', hz⟩ := exists_compact_retained_principal_neighborhood R
    i (π ≫ (projectiveLine R ↘ Spec (.of R)))
    (Spec.map (CommRingCat.ofHom (f.comp Polynomial.C))) hbase b hr W s hW z
  exact ⟨N, D, i, π, b, e, t, hi, hN, hn, hnormal, hπ, hp, hb, hfinite, hpb, hr,
    hfac, hbase, ht, ha, hsm, hnew, ha', hz⟩

end AlgebraicGeometry.Scheme.RelativeCurve
