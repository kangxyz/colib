/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Normalization.Compactification.FiniteBoundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.ProjectiveLineCompactification
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Normal projective-line compactification of the original finite coordinates

The target is the pinned native two-chart projective line. Its actual infinity section gives
the full boundary via a scheme-theoretic pullback. The source and its original polynomial
coordinate map are unchanged. Nagata normalization avoids any generic separability assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- A finite coordinate map from a normal integral scheme produces a normal finite cover of
the native projective line, proper over the original base, with the actual infinity pullback. -/
@[colib_tag "COL-1069"]
theorem exists_normal_projectiveLine_cover_of_finite_coordinate
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (hR : IsNagataScheme (Spec (.of R)))
    {X : Scheme.{u}} [IsIntegral X] [IsNormal X]
    (f : X ⟶ Spec (.of (Polynomial R))) [IsFinite f] :
    ∃ (N D : Scheme.{u}) (i : X ⟶ N) (π : N ⟶ projectiveLine R)
      (b : D ⟶ N) (e : D ⟶ Spec (.of R)),
      IsIntegral N ∧ IsLocallyNoetherian N ∧ IsNormal N ∧
      IsOpenImmersion i ∧ IsFinite π ∧ IsProper (π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsClosedImmersion b ∧ IsFinite (b ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsPullback b e π (projectiveLineInfinitySection R) ∧
      Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = f ≫ projectiveLineXChart R ∧
      i ≫ π ≫ (projectiveLine R ↘ Spec (.of R)) =
        f ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  have : IsLocallyNoetherian (projectiveLine R) :=
    LocallyOfFiniteType.isLocallyNoetherian (projectiveLine R ↘ Spec (.of R))
  have hP : IsNagataScheme (projectiveLine R) :=
    isNagataScheme_of_locallyOfFiniteType (projectiveLine R ↘ Spec (.of R)) hR
  have : IsFinite (projectiveLineInfinitySection R ≫
      (projectiveLine R ↘ Spec (.of R))) := by
    rw [projectiveLineInfinitySection_comp_structureMorphism]
    infer_instance
  obtain ⟨N, D, i, π, b, e, hN, hn, hnormal, hi, hπ, hp, hb, hf, hpb, hr, hfac, hbase⟩ :=
    exists_normal_proper_compactification_of_finite_chart f (projectiveLineXChart R) hP
      (projectiveLine R ↘ Spec (.of R)) (projectiveLineInfinitySection R)
      (range_projectiveLineInfinitySection R)
  refine ⟨N, D, i, π, b, e, hN, hn, hnormal, hi, hπ, hp, hb, hf, hpb, hr, hfac, ?_⟩
  simpa only [projectiveLineXChart_comp_structureMorphism,
    projectiveLineAffineStructureMorphism] using hbase

/-- Smooth integral algebras over a field supply the normal source and finite-type algebras
supply the Nagata coordinate base. No local étale coordinate hypothesis is needed. -/
@[colib_tag "COL-1069"]
theorem exists_normal_projectiveLine_cover_of_finite_polynomial_map
    (k R B : Type u) [Field k] [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    (f : Polynomial R →+* B) (hf : f.Finite) :
    ∃ (N D : Scheme.{u}) (i : Spec (.of B) ⟶ N) (π : N ⟶ projectiveLine R)
      (b : D ⟶ N) (e : D ⟶ Spec (.of R)),
      IsIntegral N ∧ IsLocallyNoetherian N ∧ IsNormal N ∧
      IsOpenImmersion i ∧ IsFinite π ∧ IsProper (π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsClosedImmersion b ∧ IsFinite (b ≫ π ≫ (projectiveLine R ↘ Spec (.of R))) ∧
      IsPullback b e π (projectiveLineInfinitySection R) ∧
      Set.range b = (Set.range i)ᶜ ∧
      i ≫ π = Spec.map (CommRingCat.ofHom f) ≫ projectiveLineXChart R ∧
      i ≫ π ≫ (projectiveLine R ↘ Spec (.of R)) =
        Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) := by
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : IsNormal (Spec (.of B)) :=
    isNormal_of_isRegular _ (isRegular_of_smooth_over_field
      (Spec.map (CommRingCat.ofHom (algebraMap k B))))
  have : IsFinite (Spec.map (CommRingCat.ofHom f)) := (IsFinite.SpecMap_iff _).mpr hf
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  have hR := isNagataScheme_of_locallyOfFiniteType_over_field k
    (Spec.map (CommRingCat.ofHom (algebraMap k R)))
  obtain ⟨N, D, i, π, b, e, hN, hn, hnormal, hi, hπ, hp, hb, hfinite, hpb, hr, hfac, hbase⟩ :=
    exists_normal_projectiveLine_cover_of_finite_coordinate R hR
      (Spec.map (CommRingCat.ofHom f))
  refine ⟨N, D, i, π, b, e, hN, hn, hnormal, hi, hπ, hp, hb, hfinite, hpb, hr, hfac, ?_⟩
  simpa only [← Spec.map_comp, ← CommRingCat.ofHom_comp] using hbase

end AlgebraicGeometry.Scheme
