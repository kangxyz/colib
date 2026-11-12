/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.RingTheory.Kaehler.ResidueIndependentSmoothMap
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.Algebra.MvPolynomial.Equiv

/-! # Prescribed independent residue coordinates produce a local smooth curve

Adapted from the Motivic 2026-10-21 checkpoint, with the compactification imports
replaced by native smoothness of a polynomial projection. The original tuple is unchanged.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry

/-- The literal polynomial affine line is smooth of relative dimension one. -/
theorem polynomialProjection_smooth_one (k : Type u) [CommRing k] :
    SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := by
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  apply RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso
  change RingHom.IsStandardSmoothOfRelativeDimension 1 (algebraMap k (Polynomial k))
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial PUnit.{u + 1} k) := by
    simpa using Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial k PUnit.{u + 1}
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 1
    (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1})

/-- The original polynomial map on the genuine principal neighborhood is smooth
of relative dimension one. Adding a coordinate is used only to prove this property. -/
@[colib_tag "COL-1073"]
theorem exists_smooth_one_of_residue_independent
    (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (p : Ideal R) [p.IsPrime] (d : ℕ) (f : Fin d → R)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (hf : LinearIndependent p.ResidueField
      (fun i => (1 ⊗ₜ[R] D k R (f i) : p.ResidueField ⊗[R] Ω[R⁄k]))) :
    ∃ r ∉ p, SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom ((algebraMap R (Localization.Away r)).comp
        (MvPolynomial.aeval (R := k) f).toRingHom))) := by
  obtain ⟨t, r, hr, he⟩ := Algebra.exists_etale_cons_of_residue_independent k R p d f hd hf
  let P := MvPolynomial (Fin d) k
  let Q := MvPolynomial (Fin (d + 1)) k
  let a : Q →+* Localization.Away r := (algebraMap R (Localization.Away r)).comp
    (MvPolynomial.aeval (R := k) (Fin.cons t f : Fin (d + 1) → R)).toRingHom
  let e := (MvPolynomial.finSuccEquiv k d).toRingEquiv.toCommRingCatIso
  let m := Spec.map (CommRingCat.ofHom a)
  let j := Spec.map e.inv
  let π := Spec.map (CommRingCat.ofHom (Polynomial.C : P →+* Polynomial P))
  have : Etale m := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr he
  have : SmoothOfRelativeDimension 1 π :=
    polynomialProjection_smooth_one P
  have hcomp : SmoothOfRelativeDimension 1 ((m ≫ j) ≫ π) :=
    inferInstanceAs (SmoothOfRelativeDimension (0 + 1) ((m ≫ j) ≫ π))
  refine ⟨r, hr, ?_⟩
  convert hcomp using 1
  dsimp only [m, j, π]
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro x
    change algebraMap R (Localization.Away r) ((MvPolynomial.aeval f) (MvPolynomial.C x)) =
      a ((MvPolynomial.finSuccEquiv k d).symm (Polynomial.C (MvPolynomial.C x)))
    have hx : (MvPolynomial.finSuccEquiv k d).symm (Polynomial.C (MvPolynomial.C x)) =
        MvPolynomial.C x := by
      apply (MvPolynomial.finSuccEquiv k d).injective
      simp [MvPolynomial.finSuccEquiv_apply]
    rw [hx]
    change algebraMap R (Localization.Away r) _ = algebraMap R (Localization.Away r) _
    congr 1
    exact (MvPolynomial.aeval_C f x).trans
      (MvPolynomial.aeval_C (Fin.cons t f : Fin (d + 1) → R) x).symm
  · intro i
    change algebraMap R (Localization.Away r) ((MvPolynomial.aeval f) (MvPolynomial.X i)) =
      a ((MvPolynomial.finSuccEquiv k d).symm (Polynomial.C (MvPolynomial.X i)))
    have hx : (MvPolynomial.finSuccEquiv k d).symm (Polynomial.C (MvPolynomial.X i)) =
        MvPolynomial.X i.succ := by
      apply (MvPolynomial.finSuccEquiv k d).injective
      simp [MvPolynomial.finSuccEquiv_X_succ]
    rw [hx]
    change algebraMap R (Localization.Away r) _ = algebraMap R (Localization.Away r) _
    congr 1
    exact (MvPolynomial.aeval_X f i).trans
      (MvPolynomial.aeval_X (Fin.cons t f : Fin (d + 1) → R) i.succ).symm

end AlgebraicGeometry
