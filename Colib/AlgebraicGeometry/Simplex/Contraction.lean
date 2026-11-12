/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.AffineSectionNaturality
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholeFibers
import Colib.AlgebraicGeometry.Scheme.PolynomialQuotient.Ambient

/-!
# The native affine-line contraction of the algebraic simplex

Linear interpolation of the barycentric coordinates joins vertex zero to
the identity. The polynomial chart identifies the endpoints with the
literal zero and one sections of the native affine-line cylinder. The
relative contraction retains an arbitrary smooth base.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction
open AlgebraicGeometry.Scheme.PolynomialSectionPencil
open AlgebraicGeometry.PolynomialOpenQuotient
open scoped BigOperators Polynomial

universe u

namespace AlgebraicSimplex

private theorem spec_eval_comp_ambientIso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) (a : R) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (f a))) ≫ (ambientIso f).hom =
      endpoint (Spec.map (CommRingCat.ofHom f)) a := by
  let b := Spec.map (CommRingCat.ofHom f)
  let e : Spec (.of A[X]) ≅ parameterSpace b := ambientIso f
  let v : Spec (.of A) ⟶ Spec (.of A[X]) :=
    (polynomialAffinePoint (.of A) (f a)).left
  let p := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X]))
  change v ≫ e.hom = endpoint b a
  apply pullback.hom_ext
  · change (v ≫ e.hom) ≫ projection b = endpoint b a ≫ projection b
    have h : e.hom ≫ projection b =
        Scheme.PolynomialLaurent.polynomialProjection (CommRingCat.of A) := ambientIso_fst f
    rw [Category.assoc, h, endpoint_projection]
    exact MorphismProperty.Over.w (polynomialAffinePoint (.of A) (f a))
  · change (v ≫ e.hom) ≫ pullback.snd b p = endpoint b a ≫ pullback.snd b p
    have h : e.hom ≫ pullback.snd b p =
        Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) := ambientIso_snd f
    have hs : endpoint b a ≫ pullback.snd b p =
        b ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) := endpoint_snd b a
    rw [Category.assoc, h, hs]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp

private theorem sum_polynomial_C {A : Type u} [CommRing A] {ι : Type*}
    (s : Finset ι) (f : ι → A) :
    (∑ i ∈ s, Polynomial.C (f i)) = Polynomial.C (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      simp only [Finset.sum_insert hi, ih, Polynomial.C_add]

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "Rₙ" => CoordinateRing R n
local notation "Δₙ" => smoothSiteObj R n
local notation "A₁" => additiveGroupObject (Spec (CommRingCat.of R))
local notation "pₙ" => Scheme.PolynomialLaurent.polynomialProjection (CommRingCat.of Rₙ)

private def vertexZeroRingHom : Rₙ →+* R :=
  lift (RingHom.id R) (fun i => if i = (0 : Fin (n + 1)) then 1 else 0) (by simp)

/-- Vertex zero of the original barycentric simplex. -/
@[no_expose]
def simplexVertexZero : base (Spec (.of R)) ⟶ Δₙ :=
  homMk (Spec.map (CommRingCat.ofHom (vertexZeroRingHom R n))) (by
    change Spec.map _ ≫ structureMap R n = 𝟙 _
    rw [structureMap, ← Spec.map_comp]
    have h : CommRingCat.ofHom (constant R n) ≫
        CommRingCat.ofHom (vertexZeroRingHom R n) = 𝟙 (CommRingCat.of R) := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro r
      change vertexZeroRingHom R n (constant R n r) = r
      simp [vertexZeroRingHom]
    rw [h, Spec.map_id])

private def contractionRingHom : Rₙ →+* Rₙ[X] :=
  lift (Polynomial.C.comp (constant R n)) (fun i =>
    Polynomial.X * Polynomial.C (coordinate R n i) +
      (1 - Polynomial.X) * (if i = 0 then 1 else 0)) (by
        have h : (∑ i : Fin (n + 1), if i = 0 then (1 : Rₙ[X]) else 0) = 1 := by simp
        have hC : (∑ i : Fin (n + 1), Polynomial.C (coordinate R n i)) = (1 : Rₙ[X]) :=
          (sum_polynomial_C Finset.univ (coordinate R n)).trans
            ((congrArg (fun r : Rₙ => Polynomial.C r) (sum_coordinate R n)).trans Polynomial.C_1)
        rw [Finset.sum_add_distrib,
          ← Finset.mul_sum Finset.univ (fun i => Polynomial.C (coordinate R n i)) Polynomial.X,
          ← Finset.mul_sum Finset.univ (fun i : Fin (n + 1) => if i = 0 then (1 : Rₙ[X]) else 0)
            (1 - (Polynomial.X : Rₙ[X])), hC, h]
        simpa only [mul_one] using
          (add_comm (Polynomial.X : Rₙ[X]) (1 - Polynomial.X)).trans (sub_add_cancel _ _))

private theorem contractionRingHom_eval_zero :
    (Polynomial.evalRingHom (0 : Rₙ)).comp (contractionRingHom R n) =
      (constant R n).comp (vertexZeroRingHom R n) := by
  apply ringHom_ext (R := R) (n := n) (S := Rₙ)
  · intro r
    simp [contractionRingHom, vertexZeroRingHom]
  · intro i
    by_cases hi : i = 0 <;> simp [contractionRingHom, vertexZeroRingHom, hi]

private theorem contractionRingHom_eval_one :
    (Polynomial.evalRingHom (1 : Rₙ)).comp (contractionRingHom R n) = RingHom.id Rₙ := by
  apply ringHom_ext (R := R) (n := n) (S := Rₙ)
  · intro r
    simp [contractionRingHom]
  · intro i
    by_cases hi : i = 0 <;> simp [contractionRingHom, hi]

private def simplexPolynomialAmbientIso :
    Spec (.of Rₙ[X]) ≅ parameterSpace (Δₙ).hom :=
  ambientIso (constant R n)

private def simplexCylinderChart :
    (affineLineCylinder.obj Δₙ).left ≅ Spec (.of Rₙ[X]) :=
  nativeParameterIso (.of R) Δₙ ≪≫ (simplexPolynomialAmbientIso R n).symm

private theorem simplexCylinderChart_projection :
    (simplexCylinderChart R n).hom ≫ pₙ =
      ((SmoothSite.Contraction.projection A₁).app Δₙ).left := by
  have h : (simplexPolynomialAmbientIso R n).hom ≫ projection (Δₙ).hom =
      pₙ := ambientIso_fst (constant R n)
  rw [← h, simplexCylinderChart, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc]
  exact congrArg (fun f => f.left) (affineCylinderPolynomialIso_hom_projection (.of R) Δₙ)

private theorem simplexCylinderChart_section (a : R) :
    (nativeAffineSection (.of R) Δₙ a).left ≫ (simplexCylinderChart R n).hom =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (constant R n a))) := by
  have h : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (constant R n a))) ≫
      (simplexPolynomialAmbientIso R n).hom = endpoint (Δₙ).hom a :=
    spec_eval_comp_ambientIso (constant R n) a
  apply (cancel_mono (simplexPolynomialAmbientIso R n).hom).mp
  simp only [simplexCylinderChart, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, nativeSection_parameterIso, h]

private abbrev contractionSpectrumMap : Spec (CommRingCat.of (Rₙ[X])) ⟶ (Δₙ).left :=
  Spec.map (CommRingCat.ofHom (R := Rₙ) (S := Rₙ[X]) (contractionRingHom R n))

private theorem contractionSpectrumMap_over :
    contractionSpectrumMap R n ≫ (Δₙ).hom =
      pₙ ≫ (Δₙ).hom := by
  let c : CommRingCat.of R ⟶ CommRingCat.of Rₙ := CommRingCat.ofHom (constant R n)
  let p : CommRingCat.of Rₙ ⟶ CommRingCat.of (Rₙ[X]) := CommRingCat.ofHom Polynomial.C
  let h : CommRingCat.of Rₙ ⟶ CommRingCat.of (Rₙ[X]) :=
    CommRingCat.ofHom (contractionRingHom R n)
  have he : c ≫ h = c ≫ p := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change contractionRingHom R n (constant R n r) = Polynomial.C (constant R n r)
    exact lift_constant _ _ _ r
  exact (Spec.map_comp c h).symm.trans
    ((congrArg Spec.map he).trans (Spec.map_comp c p))

/-- The actual affine-line homotopy from vertex zero to the identity of the simplex. -/
@[no_expose]
def simplexContraction : affineLineCylinder.obj Δₙ ⟶ Δₙ :=
  homMk ((simplexCylinderChart R n).hom ≫ contractionSpectrumMap R n) (by
      rw [Category.assoc, contractionSpectrumMap_over, ← Category.assoc,
        simplexCylinderChart_projection]
      exact MorphismProperty.Over.w ((SmoothSite.Contraction.projection A₁).app Δₙ))

/-- At zero the contraction is the original structural map followed by vertex zero. -/
@[reassoc]
theorem nativeAffineSection_comp_simplexContraction_zero :
    nativeAffineSection (.of R) Δₙ 0 ≫ simplexContraction R n =
      toBase Δₙ ≫ simplexVertexZero R n := by
  apply MorphismProperty.Over.Hom.ext
  change (nativeAffineSection (.of R) Δₙ 0).left ≫
      (simplexCylinderChart R n).hom ≫ contractionSpectrumMap R n =
    Spec.map (CommRingCat.ofHom (constant R n)) ≫
      Spec.map (CommRingCat.ofHom (vertexZeroRingHom R n))
  rw [← Category.assoc, simplexCylinderChart_section, map_zero, contractionSpectrumMap,
    ← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (contractionRingHom_eval_zero R n))

/-- At one the contraction is the identity on the actual simplex. -/
@[reassoc]
theorem nativeAffineSection_comp_simplexContraction_one :
    nativeAffineSection (.of R) Δₙ 1 ≫ simplexContraction R n = 𝟙 Δₙ := by
  apply MorphismProperty.Over.Hom.ext
  change (nativeAffineSection (.of R) Δₙ 1).left ≫
      (simplexCylinderChart R n).hom ≫ contractionSpectrumMap R n =
    𝟙 (Spec (.of Rₙ))
  rw [← Category.assoc, simplexCylinderChart_section, map_one, contractionSpectrumMap,
    ← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map (CommRingCat.hom_ext (contractionRingHom_eval_one R n))

variable (U : SmoothSite (Spec (CommRingCat.of R)))

/-- The section of the original simplex projection at vertex zero. -/
def simplexZeroSection : U ⟶ product U Δₙ :=
  productLift (𝟙 U) (toBase U ≫ simplexVertexZero R n)

@[reassoc (attr := simp)]
theorem simplexZeroSection_projection :
    simplexZeroSection R n U ≫ productFst U Δₙ = 𝟙 U :=
  productLift_fst _ _

/-- The original affine-line cylinder contracts the simplex factor over any smooth base. -/
def relativeSimplexContraction : affineLineCylinder.obj (product U Δₙ) ⟶ product U Δₙ :=
  productLift
    (((SmoothSite.Contraction.projection A₁).app (product U Δₙ)) ≫ productFst U Δₙ)
    (affineLineCylinder.map (productSnd U Δₙ) ≫ simplexContraction R n)

/-- At zero the relative contraction is projection followed by its vertex section. -/
@[reassoc]
theorem nativeAffineSection_comp_relativeSimplexContraction_zero :
    nativeAffineSection (.of R) (product U Δₙ) 0 ≫ relativeSimplexContraction R n U =
      productFst U Δₙ ≫ simplexZeroSection R n U := by
  apply product_hom_ext
  · simp only [relativeSimplexContraction, Category.assoc, productLift_fst,
      nativeAffineSection_projection_assoc, simplexZeroSection_projection, Category.comp_id]
  · simp only [relativeSimplexContraction, Category.assoc, productLift_snd]
    rw [nativeAffineSection_naturality_assoc, nativeAffineSection_comp_simplexContraction_zero]
    simp only [simplexZeroSection, productLift_snd, comp_toBase_assoc]

/-- At one the relative contraction is the identity on the original product. -/
@[reassoc]
theorem nativeAffineSection_comp_relativeSimplexContraction_one :
    nativeAffineSection (.of R) (product U Δₙ) 1 ≫ relativeSimplexContraction R n U =
      𝟙 (product U Δₙ) := by
  apply product_hom_ext
  · simp only [relativeSimplexContraction, Category.assoc, productLift_fst,
      nativeAffineSection_projection_assoc, Category.id_comp]
  · simp only [relativeSimplexContraction, Category.assoc, productLift_snd, Category.id_comp]
    rw [nativeAffineSection_naturality_assoc, nativeAffineSection_comp_simplexContraction_one,
      Category.comp_id]

end AlgebraicSimplex
