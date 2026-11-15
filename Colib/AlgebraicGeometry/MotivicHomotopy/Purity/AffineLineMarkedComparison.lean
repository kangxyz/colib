/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.WholeZeroCoordinates
import Colib.AlgebraicGeometry.Sites.Smooth.Affine.LineOpenMaps
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLine

/-! # The native affine cylinder with its zero section -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Contraction

open AffineCoordinates AffineSectionCoordinates
open AlgebraicGeometry.Scheme.PolynomialLaurent

private theorem specPolynomialToAffineLine_appTop_coord (R : CommRingCat.{u})
    (j : ULift.{u} (Fin 1)) :
    (Stacks.Chow.specPolynomialToAffineLine R).appTop (AffineSpace.coord (Spec R) j) =
      (Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X := by
  let φ : CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) R) ⟶
      CommRingCat.of (Polynomial R) :=
    CommRingCat.ofHom (Stacks.Chow.mvPolynomialULiftFinOneEquiv R).toRingHom
  change (Spec.map φ).appTop ((AffineSpace.SpecIso (ULift.{u} (Fin 1)) R).inv.appTop
    (AffineSpace.coord (Spec R) j)) = _
  rw [AffineSpace.SpecIso_inv_appTop_coord, ← CommRingCat.comp_apply,
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  congr 1
  change Stacks.Chow.mvPolynomialULiftFinOneEquiv R (MvPolynomial.X j) = Polynomial.X
  simp [Stacks.Chow.mvPolynomialULiftFinOneEquiv, MvPolynomial.uniqueAlgEquiv_apply]

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k))) [IsAffine X.left]

attribute [local instance] AffineSectionCoordinates.sectionsAlgebra

set_option quotPrecheck false in
local notation "R" => Γ(X.left, ⊤)
local notation "S" => Spec (CommRingCat.of k)
set_option quotPrecheck false in
local notation "p" => (projection (additiveGroupObject S)).app X

/-- The original native affine cylinder over an affine smooth scheme is relative affine space. -/
def nativeAffineCylinderAffineSpaceIso :
    (affineLineCylinder.obj X).left ≅ AffineSpace (ULift.{u} (Fin 1)) X.left := by
  let chart := (forgetScheme S).mapIso (affineLineIso X)
  let f := AffineSpace.map (ULift.{u} (Fin 1)) X.left.isoSpec.inv
  let : IsIso f :=
    (AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) X.left.isoSpec.inv).isIso_fst_of_isIso
  exact chart.symm ≪≫ asIso (Stacks.Chow.specPolynomialToAffineLine R) ≪≫ asIso f

/-- This isomorphism lies over the original projection of the native cylinder. -/
@[reassoc]
theorem nativeAffineCylinderAffineSpaceIso_hom_over :
    (nativeAffineCylinderAffineSpaceIso X).hom ≫
      (AffineSpace (ULift.{u} (Fin 1)) X.left ↘ X.left) = (p).left := by
  have h : (affineLineIso X).hom.left ≫ (p).left =
      polynomialProjection R ≫ X.left.isoSpec.inv :=
    congrArg (fun f => f.left) (affineLineIso_projection X)
  let chart := (forgetScheme S).mapIso (affineLineIso X)
  change chart.hom ≫ (p).left = _ at h
  change (chart.inv ≫ Stacks.Chow.specPolynomialToAffineLine R ≫
    AffineSpace.map (ULift.{u} (Fin 1)) X.left.isoSpec.inv) ≫
      (AffineSpace (ULift.{u} (Fin 1)) X.left ↘ X.left) = _
  simp only [Category.assoc, AffineSpace.map_over,
    Stacks.Chow.specPolynomialToAffineLine_over_assoc]
  exact (congrArg (chart.inv ≫ ·) h.symm).trans (chart.inv_hom_id_assoc _)

/-- The original native zero section goes to the zero vector in relative affine space. -/
@[reassoc]
theorem nativeAffineCylinderAffineSpaceIso_zero :
    (nativeAffineSection (.of k) X 0).left ≫ (nativeAffineCylinderAffineSpaceIso X).hom =
      AffineSpace.homOfVector (𝟙 X.left) (fun _ : ULift.{u} (Fin 1) => 0) := by
  let chart := (forgetScheme S).mapIso (affineLineIso X)
  let f := AffineSpace.map (ULift.{u} (Fin 1)) X.left.isoSpec.inv
  have h : Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫ chart.hom =
      X.left.isoSpec.inv ≫ (nativeAffineSection (.of k) X 0).left :=
    congrArg (fun m => m.left) (affineLineIso_zero X)
  have hh : (nativeAffineSection (.of k) X 0).left ≫ chart.inv =
      X.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) := by
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun m => X.left.isoSpec.hom ≫ m ≫ chart.inv) h.symm
  apply AffineSpace.hom_ext
  · rw [Category.assoc, nativeAffineCylinderAffineSpaceIso_hom_over, AffineSpace.homOfVector_over]
    exact congrArg (fun m => m.left) (nativeAffineSection_projection (.of k) X 0)
  · intro j
    rw [AffineSpace.homOfVector_appTop_coord]
    have hcomp :
        (nativeAffineSection (.of k) X 0).left ≫ (nativeAffineCylinderAffineSpaceIso X).hom =
          (X.left.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ≫
            Stacks.Chow.specPolynomialToAffineLine R ≫ f := by
      change (nativeAffineSection (.of k) X 0).left ≫ chart.inv ≫
        Stacks.Chow.specPolynomialToAffineLine R ≫ f = _
      exact ((Category.assoc _ _ _).symm.trans
        (congrArg (fun m => m ≫ Stacks.Chow.specPolynomialToAffineLine R ≫ f) hh))
    rw [hcomp]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, f, AffineSpace.map_appTop_coord,
      specPolynomialToAffineLine_appTop_coord]
    have hval : (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X) = 0 := by
      rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
      simp
    change X.left.isoSpec.hom.appTop
      ((Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))).appTop
        ((Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X)) = 0
    rw [hval, map_zero]

local notation "A" => affineLineCylinder («S» := S)

set_option maxHeartbeats 1200000 in
-- The comparison unfolds the two affine scheme charts and their polynomial section maps.
/-- The affine-line comparison commutes with the original maps of smooth affine schemes. -/
@[reassoc]
theorem nativeAffineCylinderAffineSpaceIso_naturality
    {U₀ V₀ : SmoothSite S} [IsAffine U₀.left] [IsAffine V₀.left] (g : U₀ ⟶ V₀) :
    ((A).map g).left ≫
      (@nativeAffineCylinderAffineSpaceIso k _ V₀ ‹IsAffine V₀.left›).hom =
      (@nativeAffineCylinderAffineSpaceIso k _ U₀ ‹IsAffine U₀.left›).hom ≫
        AffineSpace.map (ULift.{u} (Fin 1)) g.left := by
  let cX := (forgetScheme S).mapIso (affineLineIso U₀)
  let cY := (forgetScheme S).mapIso (affineLineIso V₀)
  let φ := AffineSectionCoordinates.sectionsMap g
  let m := PolynomialOpenQuotient.SmoothSite.lineMap φ
  have hm : m ≫ (affineLineIso V₀).hom = (affineLineIso U₀).hom ≫ (A).map g := by
    let lX := lineCylinderIso (k := k) («R» := Γ(U₀.left, ⊤))
    let lY := lineCylinderIso (k := k) («R» := Γ(V₀.left, ⊤))
    change m ≫ lY.hom ≫ (A).map (affineIso V₀).hom =
      (lX.hom ≫ (A).map (affineIso U₀).hom) ≫ (A).map g
    dsimp only [m, lX, lY]
    rw [lineCylinderIso_naturality_assoc, Category.assoc, ← Functor.map_comp,
      affineIso_naturality, Functor.map_comp]
  have h : m.left ≫ cY.hom = cX.hom ≫ ((A).map g).left :=
    congrArg (fun h => h.left) hm
  apply (cancel_epi cX.hom).1
  apply AffineSpace.hom_ext
  · let π := projection (additiveGroupObject S)
    have hp : ((A).map g).left ≫ (π.app V₀).left = (π.app U₀).left ≫ g.left :=
      congrArg (fun a => a.left) (π.naturality g)
    simp only [Category.assoc, nativeAffineCylinderAffineSpaceIso_hom_over]
    rw [AffineSpace.map_over, nativeAffineCylinderAffineSpaceIso_hom_over_assoc]
    exact congrArg (cX.hom ≫ ·) hp
  · intro j
    have hX : cX.hom ≫ (nativeAffineCylinderAffineSpaceIso U₀).hom =
        Stacks.Chow.specPolynomialToAffineLine Γ(U₀.left, ⊤) ≫
          AffineSpace.map (ULift.{u} (Fin 1)) U₀.left.isoSpec.inv := by
      change cX.hom ≫ cX.inv ≫ _ = _
      exact cX.hom_inv_id_assoc _
    have hY : cY.hom ≫ (nativeAffineCylinderAffineSpaceIso V₀).hom =
        Stacks.Chow.specPolynomialToAffineLine Γ(V₀.left, ⊤) ≫
          AffineSpace.map (ULift.{u} (Fin 1)) V₀.left.isoSpec.inv := by
      change cY.hom ≫ cY.inv ≫ _ = _
      exact cY.hom_inv_id_assoc _
    rw [← Category.assoc cX.hom, ← h, Category.assoc m.left, hY,
      ← Category.assoc cX.hom, hX]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.map_appTop_coord]
    change (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom φ.toRingHom))).appTop
      ((Stacks.Chow.specPolynomialToAffineLine Γ(V₀.left, ⊤)).appTop
        (AffineSpace.coord (Spec Γ(V₀.left, ⊤)) j)) =
      (Stacks.Chow.specPolynomialToAffineLine Γ(U₀.left, ⊤)).appTop
        (AffineSpace.coord (Spec Γ(U₀.left, ⊤)) j)
    rw [specPolynomialToAffineLine_appTop_coord, specPolynomialToAffineLine_appTop_coord]
    let ρ : CommRingCat.of (Polynomial Γ(V₀.left, ⊤)) ⟶
        CommRingCat.of (Polynomial Γ(U₀.left, ⊤)) :=
      CommRingCat.ofHom (Polynomial.mapRingHom φ.toRingHom)
    change ((Scheme.ΓSpecIso _).inv ≫ (Spec.map ρ).appTop) Polynomial.X = _
    rw [← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    congr 1
    exact Polynomial.map_X φ.toRingHom

end AlgebraicGeometry.Scheme.SmoothSite.Contraction
