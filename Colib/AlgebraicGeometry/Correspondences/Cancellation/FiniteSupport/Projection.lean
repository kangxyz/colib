/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Torus.Affine.NativeChart
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Non-finiteness of the uncut torus support projection

A finite dominant morphism onto a relative torus is surjective. Finiteness of
its composite with the torus projection would make that projection universally
closed. On a residue-field fibre this would make the Laurent coordinate integral.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

open _root_.AlgebraicGeometry.Scheme

private theorem not_universallyClosed_chartProjection (R : Type u) [CommRing R] [Nontrivial R] :
    ¬ UniversallyClosed (chartProjection (R := R)) := by
  intro h
  have hi : IsIntegralHom (chartProjection (R := R)) :=
    IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨h, by
      unfold chartProjection
      infer_instance⟩
  have hC : (LaurentPolynomial.C : R →+* LaurentPolynomial R).IsIntegral :=
    (IsIntegralHom.SpecMap_iff (φ := CommRingCat.ofHom LaurentPolynomial.C)).mp hi
  have hT : _root_.IsIntegral R (LaurentPolynomial.T 1 : LaurentPolynomial R) := hC _
  have hX : _root_.IsIntegral R (Polynomial.X : R[X]) :=
    (isIntegral_algHom_iff Polynomial.toLaurentAlg Polynomial.toLaurent_injective).mp (by
      simpa only [Polynomial.coe_toLaurentAlg, Polynomial.toLaurent_X] using hT)
  obtain ⟨p, hp, hzero⟩ := hX
  change Polynomial.aeval (Polynomial.X : R[X]) p = 0 at hzero
  exact hp.ne_zero (by simpa only [Polynomial.aeval_X_left_apply] using hzero)

set_option backward.isDefEq.respectTransparency false in
/-- The uncut projection of a finite dominant support over the native torus
is never finite if its base has a point. -/
theorem not_isFinite_support_projection {k : Type u} [Field k] {X P : Scheme.{u}}
    (f : X ⟶ Spec (.of k))
    (g : P ⟶ pullback f (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)))
    [IsFinite g] [IsDominant g] (x : X) :
    ¬ IsFinite (g ≫ pullback.fst f
      (multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k))) := by
  intro hp
  let R := X.residueField x
  let j : Spec R ⟶ X := X.fromSpecResidueField x
  let q := multiplicativeGroupBaseChange (Spec (.of k)) ↘ Spec (.of k)
  let p := pullback.fst f q
  let : IsFinite (g ≫ p) := hp
  let : UniversallyClosed p := UniversallyClosed.of_comp_surjective g p
  let e : Spec (.of (LaurentPolynomial R)) ≅ pullback j p :=
    nativeChartIso (j ≫ f) ≪≫ (pullbackRightPullbackFstIso f q j).symm
  have he : e.hom ≫ pullback.fst j p = chartProjection (R := R) := by
    simp only [e, p, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackRightPullbackFstIso_inv_fst, nativeChartIso]
    exact chartMap_fst (S := Spec (.of k)) (R := R) (j ≫ f)
  have : UniversallyClosed (chartProjection (R := R)) := by
    rw [← he]
    infer_instance
  exact not_universallyClosed_chartProjection R this

end AlgebraicGeometry.NativeTorusPolynomial
