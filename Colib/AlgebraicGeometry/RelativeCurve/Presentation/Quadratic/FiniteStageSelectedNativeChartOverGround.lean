/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteStageProducerInputs
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.SimultaneousFiniteCoordinates

/-! # Select the actual quadratic tuple before descending the same stage

This candidate calls the simultaneous producer with I = top and q = 1.
Its input contains no finite-map, etale-chart, or whole-fiber certificate.
The generators are the actual images 1 tensor g of the original generators.
Geometry is selected over F/L, but the native chart is reconstructed from the
same rational tuple and retained opens over the unchanged transfer ground K.

Validation status: full simultaneous-producer integration awaits CI. The local
postprocessing audit does not replace compilation of this complete module.
-/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry MvPolynomial IntermediateField
open AlgebraicGeometry.Scheme
universe u
namespace QuadraticIncidence.InfinityChart

theorem exists_selected_finsetSubfield_rational_native_chart_over_ground
    (K F L B : Type u) [Field K] [Field F] [Field L] [Infinite L]
    [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
    [Module.Finite K F] [Algebra.IsSeparable K F] [Algebra.IsSeparable F L]
    [CommRing B] [Algebra F B] [Algebra.Smooth F B] [IsDomain (L ⊗[F] B)]
    {σ : Type u} [Fintype σ] (g : σ → B)
    (hg : Algebra.adjoin F (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg L (L ⊗[F] B) = (d + 1 : ℕ))
    (ξ : Spec (.of L) ⟶ Spec (.of B))
    (hξ : ξ ≫ Spec.map (CommRingCat.ofHom (algebraMap F B)) =
      Spec.map (CommRingCat.ofHom (algebraMap F L))) :
    ∃ (t : Finset L),
      let E : Type u := adjoin F (t : Set L)
      ∃ (xE : Spec (.of E) ⟶ Spec (.of (E ⊗[F] B)))
        (a : Exponent σ → E) (c : Fin d × Exponent σ → E)
        (re r : E ⊗[F] B) (hfin : Module.Finite K E) (hsep : Algebra.IsSeparable K E),
        xE ≫ Spec.map (CommRingCat.ofHom (algebraMap E (E ⊗[F] B))) = 𝟙 _ ∧
        Spec.map (CommRingCat.ofHom (adjoin F (t : Set L)).val.toRingHom) ≫ xE =
          rationalTensorPoint F L B ξ hξ ≫
            Spec.map (CommRingCat.ofHom (finsetTensorInclusion F L B t).toRingHom) ∧
        re ∉ (xE default).asIdeal ∧
        ((algebraMap (E ⊗[F] B) (Localization.Away re)).comp
          (quadraticRelativeCoordinateHom E (E ⊗[F] B)
            (fun j => (1 : E) ⊗ₜ[F] g j) d a c)).Etale ∧
        HasTensorGoodQuadraticNeighborhood F E B g d ⊤ a c (xE default) r ∧
        HasQuadraticRetainedNativeChart K E (E ⊗[F] B) hfin hsep d
          (relativeCoordinateAlgHom E (E ⊗[F] B) d
            (fun i => aeval (fun j => (1 : E) ⊗ₜ[F] g j)
              (parameterTuple E σ (d + 1) (prependParameters E d a c) i).val)) xE re r := by
  classical
  let P := rationalTensorPoint F L B ξ hξ default
  let : P.asIdeal.IsMaximal := rationalTensorPoint_isMaximal F L B ξ hξ
  let gL : σ → L ⊗[F] B := fun j => 1 ⊗ₜ[F] g j
  have hgL : Algebra.adjoin L (Set.range gL) = ⊤ := tensor_generators_adjoin F L B g hg
  obtain ⟨a, c, _, _, hf, ⟨re, hre, he⟩, r, _, hW, _, hrel⟩ :=
    exists_simultaneous_finite_quadratic_coordinates L (L ⊗[F] B) P ⊤ top_ne_bot
      gL hgL d hd 1 one_ne_zero
  have hfFull := fullCoordinateHom_finite_of_relative L (L ⊗[F] B) gL d a c hf
  have hWMap : ∀ Q : Spec (.of (L ⊗[F] B)),
      Spec.map (CommRingCat.ofHom (quadraticCoordinateHom L (L ⊗[F] B) gL d c)) Q =
      Spec.map (CommRingCat.ofHom (quadraticCoordinateHom L (L ⊗[F] B) gL d c)) P →
      Q ∈ PrimeSpectrum.basicOpen r := by
    intro Q hQ
    exact hW Q (congrArg PrimeSpectrum.asIdeal hQ.symm)
  have hZ : (quadraticCoordinateHom L (L ⊗[F] (B ⧸ (⊤ : Ideal B)))
      (fun j => (1 : L) ⊗ₜ[F] Ideal.Quotient.mk ⊤ (g j)) d c).Finite := by
    apply RingHom.Finite.of_surjective
    intro z
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨t, _, _, _, xE, ε, a', c', re', r', _, _, _, _,
      _, _, hre', he', _, hW', _, hgood, hxE, hmark, hpoint, _, hfin, hsep, _⟩ :=
    exists_finsetSubfield_sameTuple_rational_native_chart F L B g d ⊤ ∅ a c ξ hξ
      re r hre hfFull he hrel hWMap hZ
  let E : Type u := adjoin F (t : Set L)
  let : Module.Finite F E := hfin
  let : Algebra.IsSeparable F E := hsep
  have hfinK : Module.Finite K E := Module.Finite.trans F E
  have hsepK : Algebra.IsSeparable K E := Algebra.IsSeparable.trans K F E
  have hreActual : re' ∉ (xE default).asIdeal := by
    rw [hpoint]
    exact hre'
  have hrActual : r' ∉ (xE default).asIdeal := by
    rw [hpoint]
    exact hW' _ rfl
  have heRelative := relativeCoordinateHom_etale_away E (E ⊗[F] B) d
    (fun i => aeval (fun j => (1 : E) ⊗ₜ[F] g j)
      (parameterTuple E σ (d + 1) (prependParameters E d a' c') i).val) re' he'
  have hnativeK := hasQuadraticRetainedNativeChart_of_rational_mark K E (E ⊗[F] B)
    hfinK hsepK d (relativeCoordinateAlgHom E (E ⊗[F] B) d
      (fun i => aeval (fun j => (1 : E) ⊗ₜ[F] g j)
        (parameterTuple E σ (d + 1) (prependParameters E d a' c') i).val))
    xE hxE re' r' hreActual hrActual heRelative
  refine ⟨t, xE, a', c', re', r', hfinK, hsepK, hxE, hmark,
    hreActual, heRelative, ?_, hnativeK⟩
  rw [hpoint]
  exact hgood

end QuadraticIncidence.InfinityChart
