/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.LinearFrameChange
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.Coordinates
public import Mathlib.LinearAlgebra.Matrix.MvPolynomial
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocalizationAwayPolynomial

/-!
# The determinant open as a parameter for changes of basis

Over an integral base ring, the principal open defined by the generic
determinant is integral. Its generic matrix specializes to the given
matrix of any invertible change of basis.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (I : Type u) [Fintype I] [DecidableEq I]
  (R : Type u) [CommRing R]

/-- The exact polynomial inverted for the frame parameter. -/
abbrev frameDeterminant : MvPolynomial (I × I) R := (Matrix.mvPolynomialX I I R).det

/-- Coordinates of the determinant open over the specified coefficient ring. -/
abbrev FrameParameterRing := Localization.Away (frameDeterminant I R)

/-- The actual structure map of the frame parameter. -/
def frameParameterProjection : Spec (CommRingCat.of (FrameParameterRing I R)) ⟶
    Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (FrameParameterRing I R)))

instance [IsDomain R] : IsDomain (FrameParameterRing I R) :=
  Localization.Away.isDomain (Matrix.det_mvPolynomialX_ne_zero I R)

instance [IsDomain R] : IsIntegral (Spec (CommRingCat.of (FrameParameterRing I R))) := by
  infer_instance

instance : Smooth (frameParameterProjection I R) :=
  smooth_Spec_map_algebraMap_of_isLocalization_away_mvPolynomial R
    (frameDeterminant I R) (FrameParameterRing I R)

/-- The generic matrix in the original determinant localization. -/
def frameParameterMatrix : Matrix I I (FrameParameterRing I R) :=
  (Matrix.mvPolynomialX I I R).map (algebraMap _ _)

/-- The generic matrix is invertible since its determinant was inverted. -/
theorem isUnit_frameParameterMatrix : IsUnit (frameParameterMatrix I R) := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  change IsUnit ((algebraMap (MvPolynomial (I × I) R) (FrameParameterRing I R)).mapMatrix
    (Matrix.mvPolynomialX I I R)).det
  rw [← RingHom.map_det]
  exact IsLocalization.Away.algebraMap_isUnit (frameDeterminant I R)

variable {R}

/-- Polynomial evaluation at the entries of an actual frame matrix. -/
def frameEvaluate (A : Matrix I I R) : MvPolynomial (I × I) R →+* R :=
  MvPolynomial.eval (fun ij => A ij.1 ij.2)

private theorem frameEvaluate_det (A : Matrix I I R) :
    frameEvaluate I A (frameDeterminant I R) = A.det :=
  Matrix.eval_det_mvPolynomialX I R (fun ij => A ij.1 ij.2)

/-- Evaluation at an actual invertible matrix defines a coefficient specialization. -/
def frameParameterSpecialization (A : (Matrix I I R)ˣ) : FrameParameterRing I R →+* R :=
  IsLocalization.Away.lift (frameDeterminant I R) (g := frameEvaluate I A.val) (by
    rw [frameEvaluate_det]
    exact Matrix.isUnits_det_units A)

/-- Every original generic entry specializes to the same entry of the given matrix. -/
theorem frameParameterSpecialization_matrix (A : (Matrix I I R)ˣ) :
    (frameParameterMatrix I R).map (frameParameterSpecialization I A) = A.val := by
  ext i j
  change frameParameterSpecialization I A
    (algebraMap (MvPolynomial (I × I) R) (FrameParameterRing I R) (MvPolynomial.X (i, j))) =
      A.val i j
  rw [frameParameterSpecialization, IsLocalization.Away.lift_eq]
  exact MvPolynomial.eval_X _

/-- Specialization is a section of the original coefficient projection. -/
def frameParameterSection (A : (Matrix I I R)ˣ) :
    Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of (FrameParameterRing I R)) :=
  Spec.map (CommRingCat.ofHom (frameParameterSpecialization I A))

@[reassoc (attr := simp)]
theorem frameParameterSection_projection (A : (Matrix I I R)ˣ) :
    frameParameterSection I A ≫ frameParameterProjection I R = 𝟙 _ := by
  unfold frameParameterSection frameParameterProjection
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap R (FrameParameterRing I R)) ≫
      CommRingCat.ofHom (frameParameterSpecialization I A) = 𝟙 _ := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change frameParameterSpecialization I A
      (algebraMap (MvPolynomial (I × I) R) (FrameParameterRing I R) (MvPolynomial.C x)) = x
    rw [frameParameterSpecialization, IsLocalization.Away.lift_eq]
    exact MvPolynomial.eval_C _
  rw [h, Spec.map_id]

section Site

open SmoothSite

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k))) [IsAffine X.left]

set_option quotPrecheck false in
local notation "R₀" => Γ(X.left, ⊤)
local notation "R₁" => FrameParameterRing I R₀
local notation "p" => frameParameterProjection I R₀

/-- The determinant open over the actual smooth affine base. -/
def frameParameterObject : SmoothSite (Spec (.of k)) :=
  mk (p ≫ X.left.isoSpec.inv ≫ X.hom)

instance frameParameterObject_isAffine : IsAffine (frameParameterObject I X).left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of R₁)))

instance frameParameterObject_isIntegral [IsIntegral X.left] :
    IsIntegral (frameParameterObject I X).left :=
  inferInstanceAs (IsIntegral (Spec (CommRingCat.of R₁)))

/-- The section defined by the given basis matrix on the original affine scheme. -/
def frameParameterSmoothSection (A : (Matrix I I R₀)ˣ) :
    X ⟶ frameParameterObject I X :=
  homMk (X.left.isoSpec.hom ≫ frameParameterSection I A) (by
    change (X.left.isoSpec.hom ≫ frameParameterSection I A) ≫
      p ≫ X.left.isoSpec.inv ≫ X.hom = X.hom
    rw [Category.assoc, frameParameterSection_projection_assoc, Iso.hom_inv_id_assoc])

set_option maxHeartbeats 600000 in
-- The global section ring and literal determinant localization have dependent types.
/-- The generic entries specialize to the actual entries on the original scheme. -/
theorem frameParameterSmoothSection_matrix (A : (Matrix I I R₀)ˣ) :
    ((frameParameterMatrix I R₀).map (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom).map
      (frameParameterSmoothSection I X A).left.appTop.hom = A.val := by
  ext i j
  change (X.left.isoSpec.hom ≫ frameParameterSection I A).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv (frameParameterMatrix I R₀ i j)) = A.val i j
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  let r := CommRingCat.of R₀
  let r' := CommRingCat.of R₁
  let q : r' ⟶ r := CommRingCat.ofHom (frameParameterSpecialization I A)
  let x : r' := frameParameterMatrix I R₀ i j
  let e := Scheme.ΓSpecIso r
  let e' := Scheme.ΓSpecIso r'
  have h₀ : q ≫ e.inv = e'.inv ≫ (Spec.map q).appTop :=
    Scheme.ΓSpecIso_inv_naturality q
  have he : e.inv (q x) = (Spec.map q).appTop (e'.inv x) :=
    ConcreteCategory.congr_hom h₀ x
  change (X.left.isoSpec.hom).appTop ((Spec.map q).appTop (e'.inv x)) = A.val i j
  rw [← he]
  change X.left.toSpecΓ.appTop
    ((Scheme.ΓSpecIso (CommRingCat.of R₀)).inv
      (frameParameterSpecialization I A (frameParameterMatrix I R₀ i j))) = A.val i j
  rw [Scheme.toSpecΓ_appTop]
  have hid : e.hom (e.inv (q x)) = q x := ConcreteCategory.congr_hom e.inv_hom_id (q x)
  change e.hom (e.inv (q x)) = A.val i j
  rw [hid]
  exact congrArg (fun M => M i j) (frameParameterSpecialization_matrix I A)

end Site

end AlgebraicGeometry.MotivicHomotopy
