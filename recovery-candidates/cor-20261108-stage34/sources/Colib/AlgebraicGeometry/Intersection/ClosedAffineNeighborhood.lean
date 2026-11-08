/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Constructed quotient charts on closed-support neighborhoods

Recovery reconstruction, 2026-11-08. The three geometric endpoints below are
adapted from the exact upstream source at motivic@a6805c4, not copied from the lost
Colib candidate. They have not been compiled. The historical fourth Tor-length
endpoint is not reconstructed here: its accepted affine comparison interface
is not yet available. No missing result is replaced by an assumption.

Source: Motivic/Aglib/AlgebraicGeometry/Intersection/ClosedAffineNeighborhood.lean.
The construction uses native IsClosedImmersion.Spec_iff and Pullback.range_snd.

An arbitrary closed support restricted to an actual affine open neighborhood
has a quotient chart with the exact inclusion square and exact point range.
The restricted support need not be a finite-correspondence generator. Its
quotient presentation and point lifts are constructed, rather than assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {P T : Scheme.{u}} (R : Type u) [CommRing R]
  (i : T ⟶ P) [IsClosedImmersion i]
  (uP : Spec (CommRingCat.of R) ⟶ P) [IsOpenImmersion uP]

/-- Restriction of any closed support to an affine open has an actual quotient
chart. Its range is exactly the support points lying in the ambient open. -/
theorem exists_closedAffineNeighborhood :
    ∃ I : Ideal R, ∃ v : Spec (CommRingCat.of (R ⧸ I)) ⟶ T,
      IsOpenImmersion v ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP ∧
      Set.range v = i ⁻¹' Set.range uP := by
  obtain ⟨I, e, he⟩ := (IsClosedImmersion.Spec_iff (f := pullback.fst uP i)).mp inferInstance
  let v : Spec (CommRingCat.of (R ⧸ I)) ⟶ T := e.inv ≫ pullback.snd uP i
  have hs : v ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP := by
    dsimp [v]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, he]
    simp only [Iso.inv_hom_id_assoc]
  refine ⟨I, v, inferInstance, hs, ?_⟩
  ext t
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) q,
      (congrArg (fun m ↦ m q) hs).symm⟩
  · intro ht
    have ht' : t ∈ Set.range (pullback.snd uP i) := by
      rw [Scheme.Pullback.range_snd]
      exact ht
    obtain ⟨w, hw⟩ := ht'
    refine ⟨e.hom w, ?_⟩
    change pullback.snd uP i (e.inv (e.hom w)) = t
    rw [Scheme.hom_inv_apply, hw]

/-- Every given support point in the ambient affine neighborhood has a point
in the constructed quotient chart; no finite-source assertion is required. -/
theorem exists_pointedClosedAffineNeighborhood (t : T) (ht : i t ∈ Set.range uP) :
    ∃ I : Ideal R, ∃ v : Spec (CommRingCat.of (R ⧸ I)) ⟶ T,
      IsOpenImmersion v ∧
      v ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP ∧
      ∃ q : PrimeSpectrum (R ⧸ I), v q = t := by
  obtain ⟨I, v, hv, hs, hr⟩ := exists_closedAffineNeighborhood R i uP
  refine ⟨I, v, hv, hs, ?_⟩
  change t ∈ Set.range v
  rw [hr]
  exact ht

variable {D : Scheme.{u}} (j : D ⟶ P) [IsClosedImmersion j]

/-- Two actual closed supports have simultaneous quotient neighborhoods over the
same ambient affine chart. Their coordinate primes agree over the ambient ring. -/
theorem exists_closedAffineIntersectionCharts (d : T) (t : D) (hp : i d = j t)
    (hd : i d ∈ Set.range uP) :
    ∃ I J : Ideal R,
    ∃ vI : Spec (CommRingCat.of (R ⧸ I)) ⟶ T,
    ∃ vJ : Spec (CommRingCat.of (R ⧸ J)) ⟶ D,
      IsOpenImmersion vI ∧ IsOpenImmersion vJ ∧
      vI ≫ i = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP ∧
      vJ ≫ j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ uP ∧
      ∃ q : PrimeSpectrum (R ⧸ I), ∃ r : PrimeSpectrum (R ⧸ J),
        vI q = d ∧ vJ r = t ∧
        q.comap (Ideal.Quotient.mk I) = r.comap (Ideal.Quotient.mk J) := by
  obtain ⟨I, vI, hvI, hsI, q, hq⟩ := exists_pointedClosedAffineNeighborhood R i uP d hd
  obtain ⟨J, vJ, hvJ, hsJ, r, hr⟩ := exists_pointedClosedAffineNeighborhood R j uP t
    (hp ▸ hd)
  refine ⟨I, J, vI, vJ, hvI, hvJ, hsI, hsJ, q, r, hq, hr, ?_⟩
  apply uP.isOpenEmbedding.injective
  change (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ uP) q =
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ uP) r
  rw [← hsI, ← hsJ]
  change i (vI q) = j (vJ r)
  rw [hq, hr, hp]

end AlgebraicGeometry.Scheme
