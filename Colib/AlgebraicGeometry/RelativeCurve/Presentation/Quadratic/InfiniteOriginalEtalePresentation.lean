/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Bertini.WholeFiberEtaleInfinityOpen
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.QuadraticFiniteCoordinates
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.PolynomialAlgebraProducer
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.FiniteLocusBadIdeal

/-! # Genuine original étale presentations over an infinite ground field

The original finite-locus ideal is fixed before a single simultaneous quadratic
parameter choice. The coordinate maps are proved finite by infinity avoidance.
The native normalization, whole-fiber affine retention and full Cartesian marked
diagram are then constructed. Neither finite coordinates nor a chosen
compactification, presentation, section, correspondence or lifting is an input.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Module _root_.MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve
universe u
namespace QuadraticIncidence.InfinityChart

/-- The original smooth affine domain and full marked étale diagram have an
actual retained presentation. The auxiliary generator choice is the only data
not yet internalized by this version; the following theorem supplies it. -/
theorem nonempty_originalEtalePresentation_of_generators
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥)
    {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B)) [Etale p] [QuasiCompact p] [IsSeparated p]
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    Nonempty (OriginalEtalePresentation k (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      p a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) s x) := by
  let := Fintype.ofFinite σ
  let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨I, hI, hIJ, U, hU, hpU⟩ := exists_fixed_finite_locus_bad_ideal k B p J hJ
  obtain ⟨a₀, c, _hq, hW, hZ, _he, hsm⟩ :=
    exists_wholeFiber_etale_closed_infinity k B x I hI g hg d hd 1 one_ne_zero
  let R := MvPolynomial (Fin d) k
  let φ : R →ₐ[k] B := aeval (R := k)
    (fun i => aeval g (parameterTuple k σ d c i).val)
  let ψ : Polynomial R →+* B := quadraticRelativeCoordinateHom k B g d a₀ c
  have hψ : ψ.comp Polynomial.C = φ.toRingHom :=
    quadraticRelativeCoordinateHom_comp_C k B g d a₀ c
  let : IsFinite (Spec.map (CommRingCat.ofHom ψ)) :=
    quadraticRelativeTuple_isFinite k B g d hg a₀ c hW
  let : IsFinite (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
    rw [← Spec.map_comp]
    exact quadraticClosedTuple_isFinite k B g d I hg c hZ
  let : IsFinite (p ∣_ U) := hpU
  exact nonempty_originalEtalePresentation_of_finite_algebra_coordinates
    k R B φ ψ hψ x hsm I J hIJ p a s hs H ha hcover U hU

/-- Finite generators, the fixed bad ideal, all quadratic parameters, actual
finite coordinate maps, normalization and full retained presentation are
constructed from the original diagram. The closed quotient J need not be
radical and the selected closed point need not be rational. -/
theorem nonempty_originalEtalePresentation
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B]
    [Algebra k B] [Algebra.Smooth k B]
    (x : PrimeSpectrum B) [x.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B)) [Etale p] [QuasiCompact p] [IsSeparated p]
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ y : Spec (.of B), y ∈ Set.range a ∨
      y ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    Nonempty (OriginalEtalePresentation k (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      p a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) s x) := by
  classical
  obtain ⟨G, hG⟩ := Algebra.FiniteType.out (R := k) (A := B)
  have hg : Algebra.adjoin k (Set.range (fun t : G => (t : B))) = ⊤ := by
    convert hG using 1
    congr 1
    ext b
    simp
  exact nonempty_originalEtalePresentation_of_generators
    k B x J hJ (fun t : G => (t : B)) hg d hd p a s hs H ha hcover

end QuadraticIncidence.InfinityChart
