/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.GroupScheme.SectionPoints
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.ParameterFiber
public import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.NativeSections
import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.ZeroComparison

/-!
# Polynomial coordinates for the actual additive parameter

The existing native affine-line comparison carries the additive coordinate
to the polynomial variable. The section determined by a scalar is therefore
the entire polynomial fiber, including on singular coefficient schemes.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The fixed polynomial comparison pulls the polynomial variable back to the native coordinate. -/
theorem nativePolynomialAffineLineIso_hom_appTop_coordinate (R : CommRingCat.{u}) :
    (nativePolynomialAffineLineIso R).hom.appTop
      ((Scheme.ΓSpecIso (.of (Polynomial R))).inv Polynomial.X) =
        additiveGroupBaseChangeCoordinate (Spec R) := by
  let i : ULift.{u} Unit := ⟨()⟩
  let Z := Spec (.of (ULift.{u} ℤ))
  have h := congrArg (fun f => f.appTop (AffineSpace.coord Z i))
    (additiveGroupBaseChangeAffineSpaceIso_hom_map (Spec R))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  have hmap :
      (AffineSpace.map (ULift.{u} Unit) (specULiftZIsTerminal.from (Spec R))).appTop
        (AffineSpace.coord Z i) = AffineSpace.coord (Spec R) i :=
    AffineSpace.map_appTop_coord (specULiftZIsTerminal.from (Spec R)) i
  have hZ : additiveGroupAffineSpaceIso.{u}.hom.appTop (AffineSpace.coord Z i) =
      additiveCoordinate := by
    change (polynomialAffineSpaceIso (.of (ULift.{u} ℤ))).hom.appTop
      (AffineSpace.coord Z i) = _
    rw [polynomialAffineSpaceIso_hom_appTop_coord]
    rfl
  rw [hmap, hZ] at h
  have hm : (nativePolynomialAffineLineIso R).hom ≫ (polynomialAffineSpaceIso R).hom =
      (additiveGroupBaseChangeAffineSpaceIso (Spec R)).hom := by
    simp only [nativePolynomialAffineLineIso, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc
    _ = ((nativePolynomialAffineLineIso R).hom ≫ (polynomialAffineSpaceIso R).hom).appTop
        (AffineSpace.coord (Spec R) i) := by
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        polynomialAffineSpaceIso_hom_appTop_coord]
    _ = _ := by rw [hm]; exact h

namespace Scheme

open AffineLineFiber PolynomialSectionPencil

variable {k : Type u} [Field k] {P : Scheme.{u}} (b : P ⟶ Spec (.of k))

local notation "Sₖ" => Spec (CommRingCat.of k)
set_option quotPrecheck false in
local notation "τ" => (additiveGroupBaseChange Sₖ ↘ Sₖ)
local notation "c" => Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
local notation "e" => nativePolynomialAffineLineIso (CommRingCat.of k)

/-- The constant section-valued point becomes literal polynomial evaluation. -/
theorem nativeAdditivePoint_constant_comp_polynomialIso (a : k) :
    (nativeAdditivePoint b (b.appTop ((ΓSpecIso (.of k)).inv a))).left ≫ (e).hom =
      b ≫ point a := by
  let v : P ⟶ additiveGroupBaseChange Sₖ :=
    (nativeAdditivePoint b (b.appTop ((ΓSpecIso (.of k)).inv a))).left
  let f : P ⟶ Spec (.of (Polynomial k)) := v ≫ (e).hom
  have hf : f ≫ c = b := by
    dsimp only [f]
    rw [Category.assoc, nativePolynomialAffineLineIso_hom_over]
    exact nativeAdditivePoint_over _ _
  apply ext_to_Spec
  simp only [Scheme.Γ_map_op]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    have hC (g : P ⟶ Spec (.of (Polynomial k))) :
        g.appTop ((ΓSpecIso (.of (Polynomial k))).inv (Polynomial.C r)) =
          (g ≫ c).appTop ((ΓSpecIso (.of k)).inv r) := by
      rw [Hom.comp_appTop, CommRingCat.comp_apply]
      exact congrArg (fun s => g.appTop s) (ConcreteCategory.congr_hom
        (ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) r)
    change f.appTop ((ΓSpecIso (.of (Polynomial k))).inv (Polynomial.C r)) =
      (b ≫ point a).appTop ((ΓSpecIso (.of (Polynomial k))).inv (Polynomial.C r))
    calc
      _ = (f ≫ c).appTop ((ΓSpecIso (.of k)).inv r) := hC f
      _ = ((b ≫ point a) ≫ c).appTop ((ΓSpecIso (.of k)).inv r) := by
        rw [hf, Category.assoc, point_comp_polynomialProjection, Category.comp_id]
      _ = _ := (hC (b ≫ point a)).symm
  · change f.appTop ((ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) =
      (b ≫ point a).appTop ((ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)
    have hv : v.appTop (additiveGroupBaseChangeCoordinate Sₖ) =
        b.appTop ((ΓSpecIso (.of k)).inv a) := nativeAdditivePoint_coordinate b _
    have hcoord : (e).hom.appTop ((ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) =
        additiveGroupBaseChangeCoordinate Sₖ :=
      nativePolynomialAffineLineIso_hom_appTop_coordinate (CommRingCat.of k)
    have hX := ConcreteCategory.congr_hom
      (ΓSpecIso_inv_naturality (CommRingCat.ofHom (Polynomial.evalRingHom a))) Polynomial.X
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hX
    change (ΓSpecIso (.of k)).inv (Polynomial.eval a Polynomial.X) =
      (point a).appTop ((ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) at hX
    calc
      _ = v.appTop ((e).hom.appTop ((ΓSpecIso (.of (Polynomial k))).inv Polynomial.X)) := by
        change (v ≫ (e).hom).appTop _ = _
        rw [Hom.comp_appTop, CommRingCat.comp_apply]
      _ = b.appTop ((ΓSpecIso (.of k)).inv a) := by rw [hcoord, hv]
      _ = _ := by
        rw [Hom.comp_appTop, CommRingCat.comp_apply, ← hX, Polynomial.eval_X]

/-- The actual additive product's map to the polynomial affine line. -/
abbrev nativeAdditivePolynomialParameter : pullback b τ ⟶ Spec (.of (Polynomial k)) :=
  pullback.snd b τ ≫ (e).hom

/-- The comparison preserves the entire coefficient pullback square. -/
theorem nativeAdditivePolynomialParameter_isPullback :
    IsPullback (nativeAdditivePolynomialParameter b) (pullback.fst b τ) c b := by
  have h : IsPullback (e).hom τ c (𝟙 Sₖ) :=
    IsPullback.of_horiz_isIso ⟨(nativePolynomialAffineLineIso_hom_over (.of k)).trans
      (Category.comp_id _).symm⟩
  simpa only [nativeAdditivePolynomialParameter, Category.comp_id] using
    (IsPullback.of_hasPullback b τ).flip.paste_horiz h

/-- The parameter of the constant section is the original scalar evaluation map. -/
@[reassoc]
theorem nativeAdditiveParameterSection_polynomialParameter (a : k) :
    nativeAdditiveParameterSection b a ≫ nativeAdditivePolynomialParameter b = b ≫ point a := by
  rw [nativeAdditivePolynomialParameter, nativeAdditiveParameterSection_snd_assoc,
    nativeAdditivePoint_constant_comp_polynomialIso]

/-- A scalar section is the actual full fiber of the polynomial parameter. -/
theorem nativeAdditiveParameterSection_isPullback (a : k) :
    IsPullback (nativeAdditiveParameterSection b a) b
      (nativeAdditivePolynomialParameter b) (point a) := by
  have h : IsPullback (nativeAdditiveParameterSection b a ≫ pullback.fst b τ) b b
      (point a ≫ c) := by
    rw [nativeAdditiveParameterSection_fst, point_comp_polynomialProjection]
    exact IsPullback.of_id_fst
  exact h.of_right (nativeAdditiveParameterSection_polynomialParameter b a)
    (nativeAdditivePolynomialParameter_isPullback b).flip

/-- The entire endpoint fiber with its original section. -/
def nativeAdditiveParameterFiberIso (a : k) :
    P ≅ fiber (nativeAdditivePolynomialParameter b) a :=
  (nativeAdditiveParameterSection_isPullback b a).flip.isoPullback

@[reassoc (attr := simp)]
theorem nativeAdditiveParameterFiberIso_hom_inclusion (a : k) :
    (nativeAdditiveParameterFiberIso b a).hom ≫ inclusion (nativeAdditivePolynomialParameter b) a =
      nativeAdditiveParameterSection b a :=
  (nativeAdditiveParameterSection_isPullback b a).flip.isoPullback_hom_snd

instance nativeAdditivePolynomialParameter_flat : Flat (nativeAdditivePolynomialParameter b) :=
  inferInstanceAs (Flat (pullback.snd b τ ≫ (e).hom))

namespace SmoothSite.Contraction

/-- The section on a smooth coefficient scheme is the existing smooth-site endpoint. -/
theorem nativeAdditiveParameterSection_eq_nativeAffineSection_left
    (X : SmoothSite (Spec (.of k))) (a : k) :
    nativeAdditiveParameterSection X.hom a = (nativeAffineSection (.of k) X a).left := by
  apply pullback.hom_ext (f := X.hom) (g := τ)
  · rw [nativeAdditiveParameterSection_fst]
    exact (congrArg (fun f => f.left) (nativeAffineSection_projection (.of k) X a)).symm
  · apply (cancel_mono (e).hom).mp
    have h := congrArg (fun f => f.left) (productLift_snd (𝟙 X)
      (toBase X ≫ polynomialAffinePoint (.of k) a ≫ (affineLinePolynomialIso (.of k)).inv))
    change (nativeAffineSection (.of k) X a).left ≫ pullback.snd X.hom τ =
      X.hom ≫ point a ≫ (e).inv at h
    simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact nativeAdditiveParameterSection_polynomialParameter X.hom a

end SmoothSite.Contraction
end Scheme
end AlgebraicGeometry
