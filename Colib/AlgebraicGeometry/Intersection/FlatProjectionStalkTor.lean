/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Intersection.OpenSectionPulledStalk
public import Colib.Algebra.Category.ModuleCat.Tor.FlatRestriction

/-!
# Removing a flat ambient projection from the actual stalk Tor

For `p : T → X`, a closed support `I` on `X`, and an actual point of its
inverse image, that inverse-image support stalk is scalar extension of the
actual original support stalk along `p.stalkMap`. This is the literal
closed-subscheme quotient/comap calculation and requires no section hypothesis.

If `p` is flat, one-sided native Tor base change then removes `p` from the
ambient ring, for the actual stalk of any map `i : C → T`. The first argument
becomes the same C-stalk with its action through `(i ≫ p).stalkMap`. Neither
the support nor `i` nor `i ≫ p` is assumed flat or open. All ambient point
identifications remain in the displayed ring actions.

This is the actual geometric Shapiro step in the affine-line graph strategy.
It does not identify a particular correspondence graph with a Cartier section;
that application still must provide its actual incidence points and maps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {T X : Scheme.{u}} (p : T ⟶ X) (I : X.IdealSheafData)
  (t : T) (d : (I.comap p).subscheme) (x : I.subscheme)
  (hd : t = (I.comap p).subschemeι d) (hx : p t = I.subschemeι x)

/-- The actual pulled closed-support stalk is induced from the actual original
support stalk, with both specified image-point equalities retained. -/
def comapStalkIsoExtend :
    (ModuleCat.restrictScalars
      ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
        (I.comap p).subschemeι.stalkMap d).hom).obj
      (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
        ((I.comap p).subscheme.presheaf.stalk d)) ≅
    (ModuleCat.extendScalars (p.stalkMap t).hom).obj
      ((ModuleCat.restrictScalars
        ((X.presheaf.stalkCongr (.of_eq hx)).hom ≫ I.subschemeι.stalkMap x).hom).obj
        (ModuleCat.of (I.subscheme.presheaf.stalk x) (I.subscheme.presheaf.stalk x))) := by
  let φ := (p.stalkMap t).hom
  letI : Algebra (X.presheaf.stalk (p t)) (T.presheaf.stalk t) := φ.toAlgebra
  let J := IdealSheafData.stalk I (p t)
  let K := IdealSheafData.stalk (I.comap p) t
  let eK := IdealSheafData.subschemeStalkModuleIsoQuotientOfEq (I.comap p) t d hd
  let eJ := IdealSheafData.subschemeStalkModuleIsoQuotientOfEq I (p t) x hx
  have hK : K = J.map φ := IdealSheafData.stalk_comap I p t
  let eQ : ModuleCat.of (T.presheaf.stalk t) (T.presheaf.stalk t ⧸ K) ≅
      (ModuleCat.extendScalars φ).obj
        (ModuleCat.of (X.presheaf.stalk (p t)) (X.presheaf.stalk (p t) ⧸ J)) :=
    (Submodule.quotEquivOfEq _ _ hK).toModuleIso ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (T.presheaf.stalk t) J).toLinearEquiv.toModuleIso
  exact eK ≪≫ eQ ≪≫ (ModuleCat.extendScalars φ).mapIso eJ.symm

variable {C : Scheme.{u}} (i : C ⟶ T) (c : C)
  (d' : (I.comap p).subscheme) (x' : I.subscheme)
  (hd' : i c = (I.comap p).subschemeι d') (hx' : p (i c) = I.subschemeι x')

/-- The whole actual stalk Tor comparison for a flat ambient projection.
The first module below is restricted by the actual composite stalk map. -/
def torStalkComapFlatProjectionIso [Flat p] (n : ℕ) :
    (((Tor (ModuleCat (X.presheaf.stalk (p (i c)))) n).obj
      ((ModuleCat.restrictScalars ((i ≫ p).stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.restrictScalars
        ((X.presheaf.stalkCongr (.of_eq hx')).hom ≫ I.subschemeι.stalkMap x').hom).obj
        (ModuleCat.of (I.subscheme.presheaf.stalk x') (I.subscheme.presheaf.stalk x')))) ≅
    (ModuleCat.restrictScalars (p.stalkMap (i c)).hom).obj
      ((((Tor (ModuleCat (T.presheaf.stalk (i c))) n).obj
        ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
          (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
        ((ModuleCat.restrictScalars
          ((T.presheaf.stalkCongr (.of_eq hd')).hom ≫
            (I.comap p).subschemeι.stalkMap d').hom).obj
          (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d')
            ((I.comap p).subscheme.presheaf.stalk d'))))) := by
  let φ := (p.stalkMap (i c)).hom
  let M := (ModuleCat.restrictScalars (i.stalkMap c).hom).obj
    (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c))
  let N := (ModuleCat.restrictScalars
    ((X.presheaf.stalkCongr (.of_eq hx')).hom ≫ I.subschemeι.stalkMap x').hom).obj
      (ModuleCat.of (I.subscheme.presheaf.stalk x') (I.subscheme.presheaf.stalk x'))
  let eM := ModuleCat.restrictScalarsComp'App φ (i.stalkMap c).hom
    ((i ≫ p).stalkMap c).hom (by simp only [Scheme.Hom.stalkMap_comp]; rfl)
      (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c))
  let eN := comapStalkIsoExtend p I (i c) d' x' hd' hx'
  exact (((Tor (ModuleCat (X.presheaf.stalk (p (i c)))) n).mapIso eM).app N) ≪≫
    ModuleCat.Tor.flatRestrictionIso φ (Flat.stalkMap p (i c)) M N n ≪≫
    (ModuleCat.restrictScalars φ).mapIso
      ((((Tor (ModuleCat (T.presheaf.stalk (i c))) n).obj M).mapIso eN.symm))

/-- Vanishing after removing the actual flat ambient projection implies
vanishing of the original native stalk Tor. There is no support-flatness input. -/
theorem isZero_torStalkComap_of_flatProjection [Flat p] (n : ℕ)
    (hzero : IsZero
      ((((Tor (ModuleCat (X.presheaf.stalk (p (i c)))) n).obj
        ((ModuleCat.restrictScalars ((i ≫ p).stalkMap c).hom).obj
          (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
        ((ModuleCat.restrictScalars
          ((X.presheaf.stalkCongr (.of_eq hx')).hom ≫ I.subschemeι.stalkMap x').hom).obj
          (ModuleCat.of (I.subscheme.presheaf.stalk x') (I.subscheme.presheaf.stalk x')))))) :
    IsZero ((((Tor (ModuleCat (T.presheaf.stalk (i c))) n).obj
      ((ModuleCat.restrictScalars (i.stalkMap c).hom).obj
        (ModuleCat.of (C.presheaf.stalk c) (C.presheaf.stalk c)))).obj
      ((ModuleCat.restrictScalars
        ((T.presheaf.stalkCongr (.of_eq hd')).hom ≫
          (I.comap p).subschemeι.stalkMap d').hom).obj
        (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d')
          ((I.comap p).subscheme.presheaf.stalk d'))))) := by
  have hrestricted := hzero.of_iso
    (torStalkComapFlatProjectionIso p I i c d' x' hd' hx' n).symm
  have hsub := ModuleCat.isZero_iff_subsingleton.mp hrestricted
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub

end AlgebraicGeometry.Scheme.Hom
