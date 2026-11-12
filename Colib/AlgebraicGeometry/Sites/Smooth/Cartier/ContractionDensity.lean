/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.CylinderComplement
public import Colib.RingTheory.Spectrum.Prime.RegularOpenDensity
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Density of the literal native contraction puncture and its etale charts

Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Cartier/ContractionDensity.lean`,
blob `48bb5daea1318e5d377f51ae3cad1de6aaec47ad`.

The active parameter is the existing native additive group. Its proved full
zero-complement identity is transported through the actual polynomial comparison.
The polynomial variable is regular over every coefficient ring. Density is not
inferred by arbitrary base change of a dense open. Only the later smooth/etale
base changes use openness. No coefficient or cohomological Mono is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

private theorem denseRange_fst_of_cartesian {D A B C : Scheme.{u}}
    {d : D ⟶ A} {e : D ⟶ B} {a : A ⟶ C} {i : B ⟶ C}
    (h : IsPullback d e a i) (ha : IsOpenMap a) (hi : DenseRange i) :
    DenseRange d := by
  have hr : Set.range d = a ⁻¹' Set.range i := by
    rw [← h.isoPullback_hom_fst]
    change Set.range ((pullback.fst a i) ∘ h.isoPullback.hom) = _
    rw [Set.range_comp, Set.range_eq_univ.mpr h.isoPullback.hom.surjective,
      Set.image_univ, Scheme.Pullback.range_fst]
  change Dense (Set.range d)
  rw [hr]
  exact hi.preimage ha

/-- The native parameter puncture is dense over every ring, by its literal
zero-complement comparison and regularity of the polynomial variable. -/
theorem multiplicativeGroupOpen_denseRange (R : CommRingCat.{u}) :
    DenseRange (multiplicativeGroupOpen (Spec R)).left := by
  let e := nativePolynomialAffineLineIso R
  let U : Set (Spec (.of (Polynomial R))) :=
    (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) : Set (PrimeSpectrum (Polynomial R)))
  have hb : Function.Bijective e.inv :=
    ⟨e.inv.isOpenEmbedding.injective, e.inv.surjective⟩
  have hzpoly : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) =
      Uᶜ := by
    change Set.range (PrimeSpectrum.comap (Polynomial.evalRingHom (0 : R))) =
      (PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R) : Set (PrimeSpectrum (Polynomial R)))ᶜ
    rw [range_comap_of_surjective _ _ (fun x => ⟨Polynomial.C x, by simp⟩),
      Polynomial.ker_evalRingHom]
    simp only [Polynomial.C_0, sub_zero, PrimeSpectrum.zeroLocus_span]
    ext x
    simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, Set.mem_compl_iff]
    change (Polynomial.X : Polynomial R) ∈ x.asIdeal ↔
      ¬ (Polynomial.X : Polynomial R) ∉ x.asIdeal
    exact not_not.symm
  have hz := range_native_zero_point R
  change Set.range (e.inv ∘ (Spec.map
    (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))) =
      (Set.range (multiplicativeGroupOpen (Spec R)).left)ᶜ at hz
  rw [Set.range_comp, hzpoly] at hz
  have hc : e.inv '' Uᶜ = (e.inv '' U)ᶜ := Set.image_compl_eq hb
  have hr : e.inv '' U = Set.range (multiplicativeGroupOpen (Spec R)).left := by
    exact compl_injective (hc.symm.trans hz)
  have hd := PrimeSpectrum.dense_basicOpen_of_isRegular
    (Polynomial.X : Polynomial R) Polynomial.isRegular_X
  change Dense (Set.range (multiplicativeGroupOpen (Spec R)).left)
  rw [← hr]
  exact e.inv.surjective.denseRange.dense_image e.inv.continuous hd

/-- The original native Laurent-cylinder open is dense, including disconnected
smooth objects. The density proof uses only the actual smooth projection. -/
theorem openInclusion_denseRange (R : CommRingCat.{u}) (X : SmoothSite (Spec R)) :
    DenseRange (openInclusion.app X).left := by
  let : Smooth (productSnd X (additiveGroupObject (Spec R))).left :=
    inferInstanceAs (Smooth (pullback.snd X.hom (additiveGroupObject (Spec R)).hom))
  exact denseRange_fst_of_cartesian
    (productMap_right_isPullback X (multiplicativeGroupOpen (Spec R)))
    (productSnd X (additiveGroupObject (Spec R))).left.isOpenMap
    (multiplicativeGroupOpen_denseRange R)

/-- An actual etale chart retains the dense literal puncture. This is geometry,
not an assumed coefficient-restriction or cohomological monomorphism. -/
theorem chartOpen_denseRange (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
    {U E : SmoothSite (Spec R)} (b : E ⟶ affineLineCylinder.obj X) [Etale b.left]
    (j : U ⟶ E) (q : U ⟶ torusCylinder.obj X)
    (hpb : IsPullback q j (openInclusion.app X) b) : DenseRange j.left :=
  denseRange_fst_of_cartesian ((forgetScheme (Spec R)).map_isPullback hpb.flip)
    b.left.isOpenMap (openInclusion_denseRange R X)

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
