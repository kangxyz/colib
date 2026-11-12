/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import StacksFrontier.AlgebraicGeometry.Limits.ProjectiveSpace
import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SimultaneousGoodNeighborhood
import Colib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.OpenGraphFinite
import Colib.AlgebraicGeometry.ProjectiveSpace.SchematicImage.Quadratic.Charts.RelativeCoordinates
import Colib.AlgebraicGeometry.Morphisms.Finite.MinimalComponentQuotient

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.MvPolynomial
open QuadraticIncidence QuadraticIncidence.InfinityChart Scheme.RelativeCurve
universe u

/-- The native base-change projective space remains available alongside the raw Proj charts. -/
example (n : ℕ) (S : Scheme.{u}) : Scheme.{u} := AlgebraicGeometry.ProjectiveSpace n S

/-- Finiteness is produced for the original map, without a reduction or new tuple. -/
example {U X Y S : Scheme.{u}} (j : U ⟶ X) (f : X ⟶ S) (g : Y ⟶ S)
    (h : U ⟶ Y) (w : j ≫ f = h ≫ g)
    [IsOpenImmersion j] [QuasiCompact j] [IsSeparated g] [IsProper f] [IsAffineHom h]
    (hno : ∀ x : (pullback.lift j h w).image,
      ((pullback.lift j h w).imageι ≫ pullback.fst f g) x ∈ Set.range j) : IsFinite h :=
  Scheme.isFinite_of_graph_image_range j f g h w hno

/-- Literal auxiliary-row separation keeps the base functions. -/
example (k B : Type u) [Field k] [CommRing B] [Algebra k B]
    {σ : Type u} [Fintype σ] (g : σ → B) (d : ℕ)
    (a : QuadraticIncidence.Exponent σ → k)
    (c : Fin d × QuadraticIncidence.Exponent σ → k) :
    (QuadraticIncidence.InfinityChart.quadraticRelativeCoordinateHom k B g d a c).comp
      Polynomial.C = QuadraticIncidence.InfinityChart.quadraticCoordinateHom k B g d c :=
  QuadraticIncidence.InfinityChart.quadraticRelativeCoordinateHom_comp_C k B g d a c

#print axioms AlgebraicGeometry.Scheme.graph_toImage_isIso_of_range
#print axioms AlgebraicGeometry.Scheme.isFinite_of_graph_image_range
#print axioms AlgebraicGeometry.isFinite_quotient_of_minimal_components

/-- End-to-end generated geometry exposes the actual infinity pullback and full retained boundary. -/
example (k B : Type u) [Field k] [Infinite k]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.Smooth k B]
    (P : PrimeSpectrum B) [P.asIdeal.IsMaximal] (I : Ideal B) (hI : I ≠ ⊥)
    {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ (a : Exponent σ → k) (c : Fin d × Exponent σ → k) (r : B), eval c q ≠ 0 ∧
    r - 1 ∈ Ideal.map (quadraticCoordinateHom k B g d c)
      (Ideal.comap (quadraticCoordinateHom k B g d c) P.asIdeal) ∧
    (∀ Q : PrimeSpectrum B,
      Ideal.comap (quadraticCoordinateHom k B g d c) P.asIdeal =
        Ideal.comap (quadraticCoordinateHom k B g d c) Q.asIdeal → r ∉ Q.asIdeal) ∧
    let R := MvPolynomial (Fin d) k
    let f := quadraticRelativeCoordinateHom k B g d a c
    let W : (Spec (.of B)).Opens := PrimeSpectrum.basicOpen r
    let s := Spec.map (CommRingCat.ofHom (f.comp Polynomial.C)) P
    let Z := Spec (.of (B ⧸ I))
    let z : Z ⟶ Spec (.of B) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
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
        PrimeSpectrum.basicOpen t → (z ≫ i) x ∈ i ''ᵁ W :=
  exists_simultaneous_good_quadratic_neighborhood k B P I hI g hg d hd q hq

#print axioms QuadraticIncidence.InfinityChart.quadraticTupleMap_isFinite
#print axioms QuadraticIncidence.InfinityChart.quadraticClosedTuple_isFinite
#print axioms QuadraticIncidence.exists_simultaneous_finite_quadratic_coordinates
#print axioms QuadraticIncidence.InfinityChart.exists_simultaneous_good_quadratic_neighborhood
