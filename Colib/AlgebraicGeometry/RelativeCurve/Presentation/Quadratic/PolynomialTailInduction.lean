/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteSeparableRetainedEtaleSmoothSite
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ZeroCoordinateStructuralIso
public import StacksFrontier.AlgebraicGeometry.FieldToResidue

/-! # The literal lower-dimensional polynomial-tail induction contract -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe u
namespace QuadraticIncidence.InfinityChart
local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

/-- The hypothesis mentions only the lower-dimensional polynomial space, on the
unchanged K-site, for every finite separable coefficient field. -/
def PolynomialTailIsomorphisms
    (K Ω : Type u) [Field K] [Field Ω] [IsAlgClosed Ω]
    (F : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) (d : ℕ) : Prop :=
  ∀ (E : Type u) [Field E] [Algebra K E] [Module.Finite K E]
    [Algebra.IsSeparable K E]
    (η : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin d) E)))
    (_hs : letI := (fieldToResidue
      (Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin d) E))))
        (η (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable E
        ((Spec (.of (MvPolynomial (Fin d) E))).residueField
          (η (IsLocalRing.closedPoint Ω)))),
    let Y := SmoothSite.mk
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))))
    let : IsAffine Y.left := inferInstanceAs
      (IsAffine (Spec (.of (MvPolynomial (Fin d) E))))
    IsIso (etaleNeighborhoodValuePullback
      (homMk Y.hom (by change Y.hom ≫ 𝟙 _ = Y.hom; simp) :
        Y ⟶ base (Spec (.of K))) (ξ := η) rfl F)

/-- Dimension zero follows from the actual finite-separable etale structure map. -/
theorem polynomialTailIsomorphisms_zero
    (K Ω : Type u) [Field K] [Field Ω] [IsAlgClosed Ω]
    (F : (SmoothSite (Spec (.of K)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    PolynomialTailIsomorphisms K Ω F 0 := by
  intro E _ _ _ _ η _
  let Y := SmoothSite.mk
    (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin 0) E))))
  let : IsAffine Y.left := inferInstanceAs
    (IsAffine (Spec (.of (MvPolynomial (Fin 0) E))))
  have hId : Etale (𝟙 (Spec (.of (MvPolynomial (Fin 0) E)))) := by
    have h : Etale (Spec.map (CommRingCat.ofHom
        (RingHom.id (MvPolynomial (Fin 0) E)))) :=
      (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
        (RingHom.Etale.of_bijective Function.bijective_id)
    simpa only [CommRingCat.ofHom_id, Spec.map_id] using h
  exact @isIso_structuralNeighborhoodPullback_of_zeroCoordinates K E _ _ _ _ _
    Y inferInstance (𝟙 (Spec (.of (MvPolynomial (Fin 0) E)))) hId
    (Category.id_comp _) Ω _ _ η F

end QuadraticIncidence.InfinityChart
