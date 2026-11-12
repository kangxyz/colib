/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.FiniteSeparableRetainedEtaleSmoothSite
public import Colib.AlgebraicGeometry.Limits.FiniteSubfieldRationalMarking

/-! # The finite-stage chart still maps to the original target over K -/
@[expose] public noncomputable section
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- The second tensor projection, without changing the original target. -/
abbrev finiteStageOriginalTarget (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] : Spec (.of (E ⊗[K] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := B)).toRingHom)

/-- Scalar compatibility of the unchanged coordinate map is exactly the over-K
condition needed for the original target, not a new compatibility hypothesis. -/
theorem finiteStageOriginalTarget_coordinate_base
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] (d : ℕ)
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] (E ⊗[K] B)) :
    finiteStageOriginalTarget K E B ≫
        Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom f.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (Polynomial.C : MvPolynomial (Fin d) E →+* Polynomial (MvPolynomial (Fin d) E))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))) := by
  have hleft :
      (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := B)).toRingHom.comp
        (algebraMap K B) = algebraMap K (E ⊗[K] B) := by
    ext a
    exact (Algebra.TensorProduct.includeRight (R := K) (A := E) (B := B)).commutes a
  have hright : f.toRingHom.comp
      ((Polynomial.C : MvPolynomial (Fin d) E →+*
        Polynomial (MvPolynomial (Fin d) E)).comp
          (algebraMap K (MvPolynomial (Fin d) E))) = algebraMap K (E ⊗[K] B) := by
    change f.toRingHom.comp (algebraMap K (Polynomial (MvPolynomial (Fin d) E))) = _
    ext a
    exact (f.restrictScalars K).commutes a
  dsimp only [finiteStageOriginalTarget]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact hleft.trans hright.symm

/-- The actual retained projection of the intersection recovers the unchanged q.
This is the compatibility used by the native target arrow below. -/
theorem retainedIntersection_coordinate {B R : Type u} [CommRing B] [CommRing R]
    (f : Polynomial R →+* B) (re r : B) :
    let je := Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away re)))
    let jr := Scheme.Opens.ι (X := Spec (.of B)) (PrimeSpectrum.basicOpen r)
    (pullback.snd je jr ≫ jr) ≫ Spec.map (CommRingCat.ofHom f) =
      pullback.fst je jr ≫ je ≫ Spec.map (CommRingCat.ofHom f) := by
  intro je jr
  exact (congrArg (fun z => z ≫ Spec.map (CommRingCat.ofHom f))
    (pullback.condition (f := je) (g := jr)).symm).trans (Category.assoc _ _ _)

/-- The original affine target lies in the original smooth site. Separatedness
and quasi-compactness are supplied by its affine presentation. -/
def originalAffineTargetSite (K B : Type u) [Field K] [CommRing B] [Algebra K B]
    [Algebra.Smooth K B] : SmoothSite (Spec (.of K)) := by
  let : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K B))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  exact SmoothSite.mk (Spec.map (CommRingCat.ofHom (algebraMap K B)))

/-- Compose a genuine affine etale chart into the tensor scheme with the original
second projection. No map from the whole retained curve into this chart is used. -/
def finiteStageChartOriginalTarget
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [CommRing B] [Algebra K B] [Algebra.Smooth K B] (d : ℕ)
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] (E ⊗[K] B))
    {A : Scheme.{u}} [IsAffine A] (i : A ⟶ Spec (.of (E ⊗[K] B)))
    (q : A ⟶ Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) [Etale q]
    (hi : i ≫ Spec.map (CommRingCat.ofHom f.toRingHom) = q) :
    let Y := SmoothSite.mk
      (Spec.map (CommRingCat.ofHom (algebraMap K (MvPolynomial (Fin d) E))))
    let hY : IsAffine Y.left := inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin d) E))))
    let p := Spec.map (CommRingCat.ofHom
      (Polynomial.C : MvPolynomial (Fin d) E →+* Polynomial (MvPolynomial (Fin d) E)))
    let hp : Smooth p := @SmoothOfRelativeDimension.smooth 1 _ _ p
      (polynomialProjection_smooth_one (MvPolynomial (Fin d) E))
    @SmoothSite.EtaleChart.chartSite (Spec (.of K)) Y hY A
      (Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) inferInstance inferInstance p hp
      q inferInstance ⟶
        originalAffineTargetSite K B := by
  refine SmoothSite.homMk (i ≫ finiteStageOriginalTarget K E B) ?_
  change (i ≫ finiteStageOriginalTarget K E B) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K B)) =
    q ≫ _
  rw [Category.assoc, finiteStageOriginalTarget_coordinate_base K E B d f,
    ← Category.assoc i, hi]
  rfl

@[simp] theorem finiteStageChartOriginalTarget_left
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [CommRing B] [Algebra K B] [Algebra.Smooth K B] (d : ℕ)
    (f : Polynomial (MvPolynomial (Fin d) E) →ₐ[E] (E ⊗[K] B))
    {A : Scheme.{u}} [IsAffine A] (i : A ⟶ Spec (.of (E ⊗[K] B)))
    (q : A ⟶ Spec (.of (Polynomial (MvPolynomial (Fin d) E)))) [Etale q]
    (hi : i ≫ Spec.map (CommRingCat.ofHom f.toRingHom) = q) :
    (finiteStageChartOriginalTarget K E B d f i q hi).left =
      i ≫ finiteStageOriginalTarget K E B := rfl

/-- Restoring the tensor marking restores its original target marking exactly. -/
theorem finiteStageChartOriginalTarget_mark
    (K E B : Type u) [Field K] [Field E] [Algebra K E]
    [CommRing B] [Algebra K B] {A : Scheme.{u}}
    (i : A ⟶ Spec (.of (E ⊗[K] B)))
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ A)
    (x : Spec (.of Ω) ⟶ Spec (.of (E ⊗[K] B))) (hx : ξ ≫ i = x) :
    ξ ≫ (i ≫ finiteStageOriginalTarget K E B) =
      x ≫ finiteStageOriginalTarget K E B :=
  (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ finiteStageOriginalTarget K E B) hx)

/-- The original L-valued point, rather than just its finite-stage image, is
recovered after the same scalar inclusion. -/
theorem finiteStageChartOriginalTarget_original_mark
    (K E L B : Type u) [Field K] [Field E] [Field L]
    [Algebra K E] [Algebra K L] [CommRing B] [Algebra K B]
    (φ : E →ₐ[K] L) {A : Scheme.{u}}
    (i : A ⟶ Spec (.of (E ⊗[K] B)))
    (ξE : Spec (.of E) ⟶ A) (xE : Spec (.of E) ⟶ Spec (.of (E ⊗[K] B)))
    (hchart : ξE ≫ i = xE)
    (ξL : Spec (.of L) ⟶ Spec (.of B))
    (hξL : ξL ≫ Spec.map (CommRingCat.ofHom (algebraMap K B)) =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hmark : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ xE =
      rationalTensorPoint K L B ξL hξL ≫ Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id K B)).toRingHom)) :
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ ξE) ≫
      (i ≫ finiteStageOriginalTarget K E B) = ξL := by
  rw [Category.assoc, ← Category.assoc ξE, hchart, ← Category.assoc, hmark,
    Category.assoc]
  rw [tensorSpec_map_snd K E L B φ]
  exact rationalTensorPoint_snd K L B ξL hξL

/-- Presheaf representatives are pulled back on the unchanged K-site only. -/
theorem originalTarget_representative_comp {S : Scheme.{u}}
    {C : Type*} [Category C] (F : (SmoothSite S)ᵒᵖ ⥤ C)
    {X Y T : SmoothSite S} (i : X ⟶ Y) (f : Y ⟶ T) :
    F.map (i ≫ f).op = F.map f.op ≫ F.map i.op :=
  F.map_comp f.op i.op

end AlgebraicGeometry.Scheme
