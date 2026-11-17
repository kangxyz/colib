/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSectionConormal

/-!
# Marked affine charts of a vector bundle

A basis on an affine open identifies the relative spectrum of the
symmetric algebra with affine space over that open. The original
augmentation becomes evaluation at the zero vector.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite Stacks.RelativeSpec
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (E : X.Modules) [E.IsQuasicoherent] (V : X.affineOpens)

set_option quotPrecheck false in
local notation "U" => (V.1 : X.Opens)
set_option quotPrecheck false in
local notation "T" => (U).toScheme
local notation "π" => vectorBundleToBase X E
local notation "z" => vectorBundleZeroSection X E
local notation "G" => gluedSpectrum (vectorBundleSituation X E)
set_option quotPrecheck false in
local notation "R" => Γ(X, U)
set_option quotPrecheck false in
local notation "aug" => (symmetricAlgebraSheafAugmentation X E).app (op U)
set_option quotPrecheck false in
local notation "η" => (symmetricAlgebraSheaf X E).hom.hom.app (op U)
set_option quotPrecheck false in
local notation "A" => (symmetricAlgebraSheaf X E).sections U

/-- The original zero section restricted to the chart over an affine open. -/
def vectorBundleZeroSectionOn : T ⟶ (π ⁻¹ᵁ U).toScheme :=
  (z).resLE _ U (le_of_eq (Stacks.VectorBundleConormal.preimage_chartOpen E U).symm)

@[reassoc (attr := simp)]
theorem vectorBundleZeroSectionOn_ι :
    vectorBundleZeroSectionOn E V ≫ (π ⁻¹ᵁ U).ι = (U).ι ≫ z :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The original zero section and its affine chart restriction form a pullback. -/
theorem vectorBundleZeroSectionOn_isPullback :
    IsPullback (vectorBundleZeroSectionOn E V) (U).ι (π ⁻¹ᵁ U).ι z := by
  apply IsOpenImmersion.isPullback
  · exact (vectorBundleZeroSectionOn_ι E V).symm
  · simpa only [Scheme.Opens.opensRange_ι] using
      Stacks.VectorBundleConormal.preimage_chartOpen E U

/-- The restricted zero section is the spectrum of the original augmentation in the chart. -/
@[reassoc]
theorem vectorBundleZeroSectionOn_comp_chartInv :
    vectorBundleZeroSectionOn E V ≫ ((G).chartIsoPreimage V).inv = (U).toSpecΓ ≫ Spec.map aug := by
  apply (cancel_mono (((G).chartIsoPreimage V).hom ≫ (π ⁻¹ᵁ U).ι)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, vectorBundleZeroSectionOn_ι]
  exact (ι_vectorBundleZeroSection X E V).trans (congrArg
    (fun f => (U).toSpecΓ ≫ Spec.map aug ≫ f)
    ((GluedSpectrum.chartIsoPreimage_hom_ι (G) V).symm))

variable {c : ℕ} (b : Module.Basis (Fin c) Γ(X, (V.1 : X.Opens)) Γ(E, (V.1 : X.Opens)))

local notation "P" => CommRingCat.of (MvPolynomial (Fin c) R)
set_option quotPrecheck false in
local notation "ψ" => Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv E
  (show IsAffineOpen U from V.2) b
set_option quotPrecheck false in
local notation "e" => AffineSpace.isoSpecFinOfIso c (show IsAffineOpen U from V.2).isoSpec
set_option quotPrecheck false in
local notation "ε" => CommRingCat.ofHom (MvPolynomial.constantCoeff : MvPolynomial (Fin c) R →+* R)

private theorem basisChart_constants (r : R) : (ψ).symm (MvPolynomial.C (σ := Fin c) r) = η r :=
  (ψ).symm_apply_eq.2 (Stacks.Chow.symmetricAlgebraSectionsMvPolynomialEquiv_app E V.2 b r).symm

private theorem basisChart_augmentation :
    CommRingCat.ofHom (ψ).symm.toRingHom ≫ aug = ε := by
  apply CommRingCat.hom_ext
  apply MvPolynomial.ringHom_ext
  · intro r
    change aug ((ψ).symm (MvPolynomial.C r)) = MvPolynomial.constantCoeff (MvPolynomial.C r)
    rw [basisChart_constants E V b r, MvPolynomial.constantCoeff_C]
    exact ConcreteCategory.congr_hom
      (NatTrans.congr_app (hom_comp_symmetricAlgebraSheafAugmentation X E) (op U)) r
  · intro j
    change aug ((ψ).symm (MvPolynomial.X j)) = MvPolynomial.constantCoeff (MvPolynomial.X j)
    change aug (Stacks.SymAlgSections.symSectionsRingEquiv E V.2
      ((SymmetricAlgebra.equivMvPolynomial b).symm (MvPolynomial.X j))) = _
    rw [SymmetricAlgebra.equivMvPolynomial_symm_X,
      Stacks.SymAlgSections.symmetricAlgebraSheafAugmentation_app_symSectionsRingEquiv E V.2,
      SymmetricAlgebra.algebraMapInv_ι, MvPolynomial.constantCoeff_X]

/-- The chosen basis identifies the original vector-bundle chart with literal affine space. -/
def vectorBundleBasisChart : (π ⁻¹ᵁ U).toScheme ≅ AffineSpace (ULift.{u} (Fin c)) T :=
  ((G).chartIsoPreimage V).symm ≪≫ Scheme.Spec.mapIso ((ψ).toCommRingCatIso.symm.op) ≪≫ (e).symm

/-- The affine basis chart preserves the projection to the original open. -/
@[reassoc]
theorem vectorBundleBasisChart_hom_over :
    (vectorBundleBasisChart E V b).hom ≫ (AffineSpace (ULift.{u} (Fin c)) T ↘ T) = π ∣_ U := by
  let φ : P ⟶ A := (ψ).toCommRingCatIso.inv
  let C : R ⟶ P := CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin c) R)
  let w := (show IsAffineOpen U from V.2).isoSpec
  let chart := (G).chartIsoPreimage V
  have hη : C ≫ φ = η := by
    apply CommRingCat.hom_ext
    refine RingHom.ext fun r => ?_
    exact basisChart_constants E V b r
  have hπ : chart.hom ≫ π ∣_ U = Spec.map η ≫ w.inv :=
    GluedSpectrum.chartIsoPreimage_hom_comp_morphismRestrict (G) V
  have hp : (e).inv ≫ (AffineSpace (ULift.{u} (Fin c)) T ↘ T) = Spec.map C ≫ w.inv :=
    AffineSpace.isoSpecFinOfIso_inv_over c (show IsAffineOpen U from V.2).isoSpec
  have hC : Spec.map φ ≫ Spec.map C = Spec.map η := (Spec.map_comp _ _).symm.trans
    (congrArg (fun m : R ⟶ A => Spec.map m) hη)
  apply (cancel_epi chart.hom).1
  calc
    _ = chart.hom ≫ chart.inv ≫ Spec.map φ ≫ (e).inv ≫
        (AffineSpace (ULift.{u} (Fin c)) T ↘ T) := by
      simp only [vectorBundleBasisChart, Iso.trans_hom, Iso.symm_hom, Category.assoc]
      rfl
    _ = Spec.map η ≫ w.inv := by
      simp only [Iso.hom_inv_id_assoc, hp, reassoc_of% hC]
    _ = _ := hπ.symm

private theorem basisChart_polyZero :
    (U).toSpecΓ ≫ Spec.map ε ≫ (e).inv =
      AffineSpace.homOfVector (𝟙 T) (fun _ : ULift.{u} (Fin c) => 0) := by
  apply AffineSpace.hom_ext
  · let w := (show IsAffineOpen U from V.2).isoSpec
    have hp : (e).inv ≫ (AffineSpace (ULift.{u} (Fin c)) T ↘ T) =
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin c) R)) ≫
          V.2.isoSpec.inv :=
      AffineSpace.isoSpecFinOfIso_inv_over c (show IsAffineOpen U from V.2).isoSpec
    have h : CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin c) R) ≫ ε = 𝟙 R :=
      CommRingCat.hom_ext (RingHom.ext (MvPolynomial.constantCoeff_C _))
    have hg : Spec.map ε ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Fin c) R)) =
          𝟙 (Spec R) := by
      exact (Spec.map_comp _ _).symm.trans
        ((congrArg (fun f : R ⟶ R => Spec.map f) h).trans (Spec.map_id R))
    have heq : (U).toSpecΓ ≫ V.2.isoSpec.inv = 𝟙 T := V.2.toSpecΓ_isoSpec_inv
    exact (Category.assoc _ _ _).trans
      ((Category.assoc _ _ _).trans ((congrArg ((U).toSpecΓ ≫ Spec.map ε ≫ ·) hp).trans
        ((congrArg ((U).toSpecΓ ≫ ·) ((reassoc_of% hg) w.inv)).trans
          ((congrArg ((U).toSpecΓ ≫ ·) (Category.id_comp _)).trans
            (heq.trans (AffineSpace.homOfVector_over _ _).symm)))))
  · intro j
    rw [AffineSpace.homOfVector_appTop_coord]
    have he :
        (e).inv.appTop (AffineSpace.coord T j) = (ΓSpecIso P).inv (MvPolynomial.X j.down) := by
      simp only [AffineSpace.isoSpecFinOfIso, Iso.trans_inv, Scheme.Hom.comp_appTop,
        CommRingCat.comp_apply, AffineSpace.map_appTop_coord, AffineSpace.SpecIso_inv_appTop_coord]
      rw [← CommRingCat.comp_apply, ← ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      congr 1
      simp [AffineSpace.mvPolynomialFinUliftIso, MvPolynomial.renameEquiv_symm]
    have hε : (Spec.map ε).appTop ((ΓSpecIso P).inv (MvPolynomial.X j.down)) = 0 := by
      rw [← CommRingCat.comp_apply, ← ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      simp
    change (U).toSpecΓ.appTop ((Spec.map ε).appTop ((e).inv.appTop (AffineSpace.coord T j))) = 0
    rw [he, hε, map_zero]

/-- The affine basis chart carries the actual restricted zero section to the literal zero vector. -/
@[reassoc]
theorem vectorBundleBasisChart_zeroSection :
    vectorBundleZeroSectionOn E V ≫ (vectorBundleBasisChart E V b).hom =
      AffineSpace.homOfVector (𝟙 T) (fun _ : ULift.{u} (Fin c) => 0) := by
  let φ : P ⟶ A := (ψ).toCommRingCatIso.inv
  let chart := (G).chartIsoPreimage V
  have hε : Spec.map aug ≫ Spec.map φ = Spec.map ε :=
    (Spec.map_comp _ _).symm.trans
      (congrArg (fun m : P ⟶ R => Spec.map m) (basisChart_augmentation E V b))
  calc
    _ = vectorBundleZeroSectionOn E V ≫ chart.inv ≫ Spec.map φ ≫ (e).inv := by
      simp only [vectorBundleBasisChart, Iso.trans_hom, Iso.symm_hom]
      rfl
    _ = (U).toSpecΓ ≫ Spec.map ε ≫ (e).inv := by
      have hzero := (vectorBundleZeroSectionOn_comp_chartInv_assoc E V)
        (Spec.map φ ≫ (e).inv)
      exact hzero.trans ((Category.assoc _ _ _).trans
        (congrArg ((U).toSpecΓ ≫ ·) ((reassoc_of% hε) (e).inv)))
    _ = _ := basisChart_polyZero (c := c) V

end AlgebraicGeometry.Scheme.Modules
