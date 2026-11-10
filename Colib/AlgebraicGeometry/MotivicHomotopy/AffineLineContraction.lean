/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.MotivicHomotopy.AffineLineLocalization
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# The actual affine line contracts to its point one

The polynomial map `H(x,t) = 1 + t * (x - 1)` is constructed on the literal
relative product of the native polynomial spectra, using the `Γ`--`Spec`
adjunction. Its endpoints are the constant map at one and the identity, and
it fixes the point one for every parameter.

This gives a map from the existing pointed affine-line cylinder. Its two
endpoint maps agree in the selected interval localization, so the actual
collapse of the pointed affine line to the point becomes an isomorphism.
No homotopical cofiber or Tate-sphere comparison is asserted here.

The coordinate construction follows the native adjunction pattern in
`Colib.AlgebraicGeometry.Simplex.IntervalMultiplication`, while retaining the
polynomial affine line and the formula based at one.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open CategoryTheory.PointedSimplicialPresheaf

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

/-- Pullback of the actual polynomial coordinate ring along a smooth-site affine-line map. -/
def affineLinePullback {U : SmoothSite (Spec R)} (f : U ⟶ affineLine R) :
    Polynomial R →+* Γ(U.left, ⊤) :=
  ((ΓSpecIso (.of (Polynomial R))).inv ≫ f.left.appTop).hom

/-- The coordinate value of an actual map to the polynomial affine line. -/
def affineLineValue {U : SmoothSite (Spec R)} (f : U ⟶ affineLine R) : Γ(U.left, ⊤) :=
  affineLinePullback R f Polynomial.X

theorem affineLinePullback_C {U : SmoothSite (Spec R)} (f : U ⟶ affineLine R) (r : R) :
    affineLinePullback R f (Polynomial.C r) = U.hom.appTop ((ΓSpecIso R).inv r) := by
  have h := congrArg
    (fun k : R ⟶ Γ((affineLine R).left, ⊤) => k r)
    (ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
  change (ΓSpecIso (.of (Polynomial R))).inv (Polynomial.C r) =
    (polynomialProjection R).appTop ((ΓSpecIso R).inv r) at h
  exact (congrArg (fun s => f.left.appTop s) h).trans
    (congrArg (fun g : U.left ⟶ Spec R => g.appTop ((ΓSpecIso R).inv r))
      (MorphismProperty.Over.w f))

/-- Maps over the base into the actual polynomial affine line are determined by the coordinate. -/
theorem affineLine_hom_ext {U : SmoothSite (Spec R)} {f g : U ⟶ affineLine R}
    (h : affineLineValue R f = affineLineValue R g) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  change affineLinePullback R f = affineLinePullback R g
  apply Polynomial.ringHom_ext
  · intro r
    rw [affineLinePullback_C, affineLinePullback_C]
  · exact h

/-- A constant polynomial section evaluates the native coordinate to its actual coefficient. -/
theorem polynomialSection_appTop_coordinate (a : R) :
    (polynomialSection R a).appTop (polynomialCoordinate R) = (ΓSpecIso R).inv a := by
  have h := congrArg
    (fun k : CommRingCat.of (Polynomial R) ⟶ Γ(Spec R, ⊤) => k Polynomial.X)
    (ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.evalRingHom a)))
  change (ΓSpecIso R).inv (Polynomial.eval a Polynomial.X) =
    (polynomialSection R a).appTop (polynomialCoordinate R) at h
  simpa only [Polynomial.eval_X] using h.symm

@[simp]
theorem affineLineValue_zeroAt (U : SmoothSite (Spec R)) :
    affineLineValue R ((baseIsTerminal (Spec R)).from U ≫ affineLineZero R) = 0 := by
  change U.hom.appTop ((polynomialSection R 0).appTop (polynomialCoordinate R)) = 0
  rw [polynomialSection_appTop_coordinate]
  change U.hom.appTop.hom ((ΓSpecIso R).inv.hom 0) = 0
  simp only [map_zero]

@[simp]
theorem affineLineValue_oneAt (U : SmoothSite (Spec R)) :
    affineLineValue R ((baseIsTerminal (Spec R)).from U ≫ affineLineOne R) = 1 := by
  change U.hom.appTop ((polynomialSection R 1).appTop (polynomialCoordinate R)) = 1
  rw [polynomialSection_appTop_coordinate]
  change U.hom.appTop.hom ((ΓSpecIso R).inv.hom 1) = 1
  simp only [map_one]

/-- The actual polynomial ring map with coordinate image `1 + t * (x - 1)`. -/
def affineLineContractionRingHom :
    Polynomial R →+* Γ((product (affineLine R) (affineLine R)).left, ⊤) :=
  Polynomial.eval₂RingHom
    (((ΓSpecIso R).inv ≫ (product (affineLine R) (affineLine R)).hom.appTop).hom)
    (1 + affineLineValue R (productSnd (affineLine R) (affineLine R)) *
      (affineLineValue R (productFst (affineLine R) (affineLine R)) - 1))

/-- The contraction based at one, on the actual relative scheme product. -/
def affineLineContraction : product (affineLine R) (affineLine R) ⟶ affineLine R :=
  homMk
    (ΓSpec.adjunction.homEquiv (product (affineLine R) (affineLine R)).left
      (op (.of (Polynomial R))) (CommRingCat.ofHom (affineLineContractionRingHom R)).op) (by
    apply ext_to_Spec
    change (ΓSpecIso R).inv ≫
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))).appTop ≫
      (ΓSpec.adjunction.homEquiv (product (affineLine R) (affineLine R)).left
        (op (.of (Polynomial R)))
        (CommRingCat.ofHom (affineLineContractionRingHom R)).op).appTop =
      (ΓSpecIso R).inv ≫ (product (affineLine R) (affineLine R)).hom.appTop
    rw [← ΓSpecIso_inv_naturality_assoc, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact Polynomial.eval₂_C _ _)

theorem affineLineContraction_pullback :
    affineLinePullback R (affineLineContraction R) = affineLineContractionRingHom R :=
  congrArg CommRingCat.Hom.hom
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (CommRingCat.ofHom (affineLineContractionRingHom R)))

/-- The contraction has the stated actual coordinate formula. -/
theorem affineLineContraction_coordinate :
    (affineLineContraction R).left.appTop (polynomialCoordinate R) =
      1 + (productSnd (affineLine R) (affineLine R)).left.appTop (polynomialCoordinate R) *
        ((productFst (affineLine R) (affineLine R)).left.appTop (polynomialCoordinate R) - 1) := by
  change affineLinePullback R (affineLineContraction R) Polynomial.X = _
  rw [affineLineContraction_pullback]
  exact Polynomial.eval₂_X _ _

theorem affineLineValue_comp_contraction {U : SmoothSite (Spec R)}
    (f : U ⟶ product (affineLine R) (affineLine R)) :
    affineLineValue R (f ≫ affineLineContraction R) =
      1 + affineLineValue R (f ≫ productSnd (affineLine R) (affineLine R)) *
        (affineLineValue R (f ≫ productFst (affineLine R) (affineLine R)) - 1) := by
  change f.left.appTop ((affineLineContraction R).left.appTop (polynomialCoordinate R)) = _
  rw [affineLineContraction_coordinate]
  simp only [map_add, map_one, map_mul, map_sub]
  rfl

/-- At parameter zero the contraction is the actual constant map at one. -/
@[reassoc (attr := simp)]
theorem affineLineContraction_zero :
    productLift (𝟙 (affineLine R))
        ((baseIsTerminal (Spec R)).from (affineLine R) ≫ affineLineZero R) ≫
      affineLineContraction R =
        (baseIsTerminal (Spec R)).from (affineLine R) ≫ affineLineOne R := by
  apply affineLine_hom_ext R
  rw [affineLineValue_comp_contraction]
  simp

/-- At parameter one the contraction is the actual identity. -/
@[reassoc (attr := simp)]
theorem affineLineContraction_one :
    productLift (𝟙 (affineLine R))
        ((baseIsTerminal (Spec R)).from (affineLine R) ≫ affineLineOne R) ≫
      affineLineContraction R = 𝟙 (affineLine R) := by
  apply affineLine_hom_ext R
  rw [affineLineValue_comp_contraction]
  simp only [productLift_fst, productLift_snd, affineLineValue_oneAt, one_mul]
  rw [add_comm, sub_add_cancel]

/-- The contraction fixes the point one for every parameter. -/
@[reassoc (attr := simp)]
theorem affineLineContraction_basepoint :
    productLift ((baseIsTerminal (Spec R)).from (affineLine R) ≫ affineLineOne R)
        (𝟙 (affineLine R)) ≫ affineLineContraction R =
      (baseIsTerminal (Spec R)).from (affineLine R) ≫ affineLineOne R := by
  apply affineLine_hom_ext R
  rw [affineLineValue_comp_contraction]
  simp

/-- Yoneda of the actual constant scheme map is the original global-point factorization. -/
theorem simplicialYoneda_map_constant (U : SmoothSite (Spec R))
    {X : SmoothSite (Spec R)} (x : base (Spec R) ⟶ X) :
    (simplicialYoneda (SmoothSite (Spec R))).map ((baseIsTerminal (Spec R)).from U ≫ x) =
      terminal.from ((simplicialYoneda (SmoothSite (Spec R))).obj U) ≫
        representablePoint R x := by
  apply NatTrans.ext
  funext V
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro f
  change f ≫ ((baseIsTerminal (Spec R)).from U ≫ x) =
    (baseIsTerminal (Spec R)).from V.unop ≫ x
  rw [← Category.assoc]
  congr 1
  exact (baseIsTerminal (Spec R)).hom_ext _ _

/-- The existing product comparison also retains the second actual scheme projection. -/
@[reassoc (attr := simp)]
theorem simplicialYonedaProductIso_hom_snd (U V : SmoothSite (Spec R)) :
    (simplicialYonedaProductIso R U V).hom ≫ prod.snd =
      (simplicialYoneda (SmoothSite (Spec R))).map (productSnd U V) := by
  simp only [simplicialYonedaProductIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    PreservesLimitPair.iso_hom, Category.assoc, prodComparison_snd, ← Functor.map_comp,
    categoricalProductIso_inv_snd]

theorem affineLineAxis_productIso :
    intervalAxis (pointedAffineLine R) (affineLineParameter R) ≫
        (simplicialYonedaProductIso R (affineLine R) (affineLine R)).inv =
      (simplicialYoneda (SmoothSite (Spec R))).map
        (productLift ((baseIsTerminal (Spec R)).from (affineLine R) ≫ affineLineOne R)
          (𝟙 (affineLine R))) := by
  change prod.lift
      (terminal.from (affineLineParameter R) ≫ representablePoint R (affineLineOne R))
      (𝟙 (affineLineParameter R)) ≫
        (simplicialYonedaProductIso R (affineLine R) (affineLine R)).inv = _
  apply (cancel_mono (simplicialYonedaProductIso R (affineLine R) (affineLine R)).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext
  · simp only [Category.assoc, simplicialYonedaProductIso_hom_fst, ← Functor.map_comp,
      productLift_fst, prod.lift_fst]
    exact (simplicialYoneda_map_constant R (affineLine R) (affineLineOne R)).symm
  · simp [Category.assoc, ← Functor.map_comp]

theorem affineLineEndpoint_productIso (i : base (Spec R) ⟶ affineLine R) :
    prod.lift (𝟙 (affineLineParameter R))
        (terminal.from (affineLineParameter R) ≫ representablePoint R i) ≫
        (simplicialYonedaProductIso R (affineLine R) (affineLine R)).inv =
      (simplicialYoneda (SmoothSite (Spec R))).map
        (productLift (𝟙 (affineLine R))
          ((baseIsTerminal (Spec R)).from (affineLine R) ≫ i)) := by
  apply (cancel_mono (simplicialYonedaProductIso R (affineLine R) (affineLine R)).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply prod.hom_ext
  · simp [Category.assoc, ← Functor.map_comp]
  · simp only [Category.assoc, simplicialYonedaProductIso_hom_snd, ← Functor.map_comp,
      productLift_snd, prod.lift_snd]
    exact (simplicialYoneda_map_constant R (affineLine R) i).symm

theorem affineLineContraction_axis :
    intervalAxis (pointedAffineLine R) (affineLineParameter R) ≫
        ((simplicialYonedaProductIso R (affineLine R) (affineLine R)).inv ≫
          (simplicialYoneda (SmoothSite (Spec R))).map (affineLineContraction R)) =
      terminal.from (affineLineParameter R) ≫ (pointedAffineLine R).hom := by
  rw [← Category.assoc, affineLineAxis_productIso, ← Functor.map_comp,
    affineLineContraction_basepoint, simplicialYoneda_map_constant]
  rfl

/-- The actual basepoint-preserving polynomial contraction descends to the pointed cylinder. -/
def pointedAffineLineContraction :
    parameterizedCylinder (pointedAffineLine R) (affineLineParameter R) ⟶ pointedAffineLine R :=
  Under.homMk
    (pushout.desc
      ((simplicialYonedaProductIso R (affineLine R) (affineLine R)).inv ≫
        (simplicialYoneda (SmoothSite (Spec R))).map (affineLineContraction R))
      (pointedAffineLine R).hom (affineLineContraction_axis R))
    (pushout.inr_desc _ _ _)

/-- Each cylinder endpoint is precisely Yoneda of the corresponding polynomial-scheme map. -/
theorem cylinderSection_pointedAffineLineContraction_right
    (i : base (Spec R) ⟶ affineLine R) :
    (cylinderSection (pointedAffineLine R) (representablePoint R i) ≫
        pointedAffineLineContraction R).right =
      (simplicialYoneda (SmoothSite (Spec R))).map
        (productLift (𝟙 (affineLine R))
          ((baseIsTerminal (Spec R)).from (affineLine R) ≫ i) ≫
            affineLineContraction R) := by
  change (prod.lift (𝟙 _) (terminal.from _ ≫ representablePoint R i) ≫
    pushout.inl _ _) ≫ pushout.desc _ _ _ = _
  rw [Category.assoc, pushout.inl_desc]
  change prod.lift (𝟙 (affineLineParameter R))
      (terminal.from (affineLineParameter R) ≫ representablePoint R i) ≫
      ((simplicialYonedaProductIso R (affineLine R) (affineLine R)).inv ≫
        (simplicialYoneda (SmoothSite (Spec R))).map (affineLineContraction R)) = _
  rw [← Category.assoc, affineLineEndpoint_productIso, ← Functor.map_comp]

/-- The zero endpoint is the actual pointed constant map. -/
@[reassoc (attr := simp)]
theorem pointedAffineLineContraction_zero :
    cylinderSection (pointedAffineLine R) (representablePoint R (affineLineZero R)) ≫
      pointedAffineLineContraction R = 0 := by
  apply Under.UnderMorphism.ext
  rw [cylinderSection_pointedAffineLineContraction_right, affineLineContraction_zero]
  exact simplicialYoneda_map_constant R (affineLine R) (affineLineOne R)

/-- The one endpoint is the actual pointed identity. -/
@[reassoc (attr := simp)]
theorem pointedAffineLineContraction_one :
    cylinderSection (pointedAffineLine R) (representablePoint R (affineLineOne R)) ≫
      pointedAffineLineContraction R = 𝟙 (pointedAffineLine R) := by
  apply Under.UnderMorphism.ext
  rw [cylinderSection_pointedAffineLineContraction_right, affineLineContraction_one]
  exact (simplicialYoneda (SmoothSite (Spec R))).map_id (affineLine R)

/-- The identity and actual point-factorization agree in the selected interval localization. -/
theorem toAffineLineHomotopyCategory_map_id_eq_zero :
    (toAffineLineHomotopyCategory R).map (𝟙 (pointedAffineLine R)) =
      (toAffineLineHomotopyCategory R).map (0 : pointedAffineLine R ⟶ pointedAffineLine R) := by
  have h := toIntervalHomotopyCategory_map_of_cylinder
    (SmoothSite (Spec R)) (nisnevichTopology (Spec R)) (affineLineParameter R)
    (pointedAffineLineContraction R)
    (representablePoint R (affineLineOne R)) (representablePoint R (affineLineZero R))
  simpa only [pointedAffineLineContraction_one, pointedAffineLineContraction_zero] using h

/-- The original collapse to the point is an isomorphism after affine-line interval localization. -/
def pointedAffineLineLocalizationIsoPoint :
    (toAffineLineHomotopyCategory R).obj (pointedAffineLine R) ≅
      (toAffineLineHomotopyCategory R).obj (point (SmoothSite (Spec R))) where
  hom := (toAffineLineHomotopyCategory R).map
    (toPoint (SmoothSite (Spec R)) (pointedAffineLine R))
  inv := (toAffineLineHomotopyCategory R).map
    (fromPoint (SmoothSite (Spec R)) (pointedAffineLine R))
  hom_inv_id := by
    have h : toPoint (SmoothSite (Spec R)) (pointedAffineLine R) ≫
        fromPoint (SmoothSite (Spec R)) (pointedAffineLine R) =
          (0 : pointedAffineLine R ⟶ pointedAffineLine R) := by
      apply Under.UnderMorphism.ext
      rfl
    rw [← Functor.map_comp, h, ← toAffineLineHomotopyCategory_map_id_eq_zero]
    exact (toAffineLineHomotopyCategory R).map_id (pointedAffineLine R)
  inv_hom_id := by
    have h : fromPoint (SmoothSite (Spec R)) (pointedAffineLine R) ≫
        toPoint (SmoothSite (Spec R)) (pointedAffineLine R) =
          𝟙 (point (SmoothSite (Spec R))) := by
      apply Under.UnderMorphism.ext
      exact terminal.hom_ext _ _
    rw [← Functor.map_comp, h]
    exact (toAffineLineHomotopyCategory R).map_id (point (SmoothSite (Spec R)))

/-- The map inverted by contractibility is precisely the original pointed collapse. -/
theorem isIso_toAffineLineHomotopyCategory_map_toPoint :
    IsIso ((toAffineLineHomotopyCategory R).map
      (toPoint (SmoothSite (Spec R)) (pointedAffineLine R))) :=
  (pointedAffineLineLocalizationIsoPoint R).isIso_hom

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-0390"]
  AlgebraicGeometry.MotivicHomotopy.affineLineContraction
  AlgebraicGeometry.MotivicHomotopy.pointedAffineLineLocalizationIsoPoint
