/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Open.RelativeCurveOverlapShrinking

/-! # Relative overlap shrinking through the original open immersion -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/RelativeCurve/Open/RelativeOpenImmersionOverlapShrinking.lean`,
blob `b5a1326a796ca1ad7bba8ae653439102ef16d0cd`.
Only the actual generic fiber receives a curve-dimension bound. The original
total space, overlap and full finite boundary are retained. Ordinary cohomology
uses the native free-Yoneda Ext source.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry.Scheme

/-- The canonical-pullback version retains the original open immersion, its
original smaller open, and every point of the unchanged finite prescribed scheme. -/
theorem exists_base_principal_openImmersion_overlap_shrinking
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y W Z : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p]
    (i : W ⟶ Y) [IsOpenImmersion i] (O : W.Opens)
    (hO : genericPoints W ⊆ (O : Set W)) (z : Z ⟶ Y)
    [IsFinite (z ≫ p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))]
    (hz : Disjoint (Set.range z) (Set.range i)) :
    ∃ (r : R), r ≠ 0 ∧ ∃ T : Y.Opens,
      (∀ a : Z,
        (z ≫ p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) a ∈
          PrimeSpectrum.basicOpen r → z a ∈ T) ∧ i ⁻¹ᵁ T ≤ O := by
  let U := i.opensRange
  let O' := i.isoOpensRange.inv ⁻¹ᵁ O
  have hO' : genericPoints U.toScheme ⊆ (O' : Set U.toScheme) := by
    intro x hx
    exact hO (Hom.mem_genericPoints_of_generalizing i.isoOpensRange.inv
      (Flat.generalizingMap _) x hx)
  have hz' : Disjoint (Set.range z) (U : Set Y) := by
    exact hz
  obtain ⟨r, hr, hretain, hsmall⟩ :=
    exists_base_principal_overlapClosureComplement R p U O' hO' z hz'
  refine ⟨r, hr, overlapClosureComplement U O', hretain, ?_⟩
  intro x hx
  have hi : U.ι (i.isoOpensRange.hom x) = i x :=
    congrArg (fun f : W ⟶ Y => f x) i.isoOpensRange_hom_ι
  have hm : i.isoOpensRange.hom x ∈ U.ι ⁻¹ᵁ overlapClosureComplement U O' := by
    change U.ι (i.isoOpensRange.hom x) ∈ overlapClosureComplement U O'
    rw [hi]
    exact hx
  have ht := hsmall hm
  change i.isoOpensRange.inv (i.isoOpensRange.hom x) ∈ O at ht
  have he : i.isoOpensRange.inv (i.isoOpensRange.hom x) = x :=
    congrArg (fun f : W ⟶ W => f x) i.isoOpensRange.hom_inv_id
  simpa only [he] using ht

end AlgebraicGeometry.Scheme
