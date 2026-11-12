/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.FlatRestriction

public import Colib.AlgebraicGeometry.Intersection.OpenSectionPulledStalk
public import StacksFrontier.RingTheory.Tor.FlatExtendScalarsFirst
public import Colib.RingTheory.Length.LocalRestriction
public import StacksFrontier.AlgebraicGeometry.Scheme.FibreResidueField

/-!
# Actual support stalk Tor along a flat projection

The full inverse-image support stalk is extension of scalars of the original
support stalk. The maps are the actual projection and closed-inclusion stalk
maps, with their necessary point transports. Native flat change of rings then
removes the projection from Tor in every degree, without flatness of either
support. No regular sequence or comparison certificate is supplied.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {T X : Scheme.{u}} (p : T ⟶ X) (I : X.IdealSheafData)
    (x : T) (d : (I.comap p).subscheme) (e : I.subscheme)
    (hd : x = (I.comap p).subschemeι d) (he : p x = I.subschemeι e)

/-- The literal full inverse-image stalk is the actual extension of the original
support stalk. The proof does not assume flatness of the projection or support. -/
def comapStalkIsoExtendScalarsOfEq :
    (ModuleCat.restrictScalars
      ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
        (I.comap p).subschemeι.stalkMap d).hom).obj
      (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
        ((I.comap p).subscheme.presheaf.stalk d)) ≅
    (ModuleCat.extendScalars (p.stalkMap x).hom).obj
      ((ModuleCat.restrictScalars
        ((X.presheaf.stalkCongr (.of_eq he)).hom ≫ I.subschemeι.stalkMap e).hom).obj
        (ModuleCat.of (I.subscheme.presheaf.stalk e) (I.subscheme.presheaf.stalk e))) := by
  let a := (p.stalkMap x).hom
  let := a.toAlgebra
  let J := IdealSheafData.stalk I (p x)
  let D := IdealSheafData.stalk (I.comap p) x
  let eD := IdealSheafData.subschemeStalkModuleIsoQuotientOfEq (I.comap p) x d hd
  let eJ := IdealSheafData.subschemeStalkModuleIsoQuotientOfEq I (p x) e he
  let eQ : ModuleCat.of (T.presheaf.stalk x) (T.presheaf.stalk x ⧸ D) ≅
      (ModuleCat.extendScalars a).obj
        (ModuleCat.of (X.presheaf.stalk (p x)) (X.presheaf.stalk (p x) ⧸ J)) :=
    (Submodule.quotEquivOfEq _ _ (IdealSheafData.stalk_comap I p x)).toModuleIso ≪≫
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (T.presheaf.stalk x) J).toLinearEquiv.toModuleIso
  exact eD ≪≫ eQ ≪≫ (ModuleCat.extendScalars a).mapIso eJ.symm

/-- Native change of rings removes a flat projection from the actual full
pulled-support Tor. The output retains the original support stalk and its action. -/
def comapStalkTorIsoOfFlat [Flat p] (N : ModuleCat (T.presheaf.stalk x)) (n : ℕ) :
    (ModuleCat.restrictScalars (p.stalkMap x).hom).obj
      (((Tor (ModuleCat (T.presheaf.stalk x)) n).obj N).obj
        ((ModuleCat.restrictScalars
          ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
            (I.comap p).subschemeι.stalkMap d).hom).obj
          (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
            ((I.comap p).subscheme.presheaf.stalk d)))) ≅
    ((Tor (ModuleCat (X.presheaf.stalk (p x))) n).obj
      ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj N)).obj
      ((ModuleCat.restrictScalars
        ((X.presheaf.stalkCongr (.of_eq he)).hom ≫ I.subschemeι.stalkMap e).hom).obj
        (ModuleCat.of (I.subscheme.presheaf.stalk e) (I.subscheme.presheaf.stalk e))) :=
  (ModuleCat.restrictScalars (p.stalkMap x).hom).mapIso
    (((Tor (ModuleCat (T.presheaf.stalk x)) n).obj N).mapIso
      (comapStalkIsoExtendScalarsOfEq p I x d e hd he)) ≪≫
    Stacks.TorFlatExtendScalars.torExtendScalarsIso (p.stalkMap x).hom
      (Flat.stalkMap p x) N _ n

-- Expose the bundled residue-field composite and its underlying ring-hom application.
set_option backward.isDefEq.respectTransparency false in
/-- Along a preimmersed composite, the actual projection does not change residue
fields. Consequently restriction preserves all lengths, including infinite length. -/
theorem length_restrictScalars_stalkMap_of_preimmersion_comp
    {C : Scheme.{u}} (i : C ⟶ T) [IsPreimmersion (i ≫ p)] (c : C)
    (M : ModuleCat (T.presheaf.stalk (i c))) :
    Module.length (X.presheaf.stalk (p (i c)))
      ((ModuleCat.restrictScalars (p.stalkMap (i c)).hom).obj M) =
      Module.length (T.presheaf.stalk (i c)) M := by
  apply ModuleCat.length_restrictScalars_of_residue_surjective
  change Function.Surjective (p.residueFieldMap (i c)).hom
  intro b
  obtain ⟨a, ha⟩ := surjective_residueFieldMap_of_surjectiveOnStalks
    (i ≫ p) c ((i.residueFieldMap c) b)
  refine ⟨a, (i.residueFieldMap c).hom.injective ?_⟩
  rw [Scheme.residueFieldMap_comp] at ha
  exact ha

/-- The Tor comparison preserves the full module length when the actual
projection is taken along a preimmersed composite. No Tor finiteness is required. -/
theorem comapStalkTor_length_of_flat [Flat p]
    {C : Scheme.{u}} (i : C ⟶ T) [IsPreimmersion (i ≫ p)] (c : C) (hx : x = i c)
    (N : ModuleCat (T.presheaf.stalk x)) (n : ℕ) :
    Module.length (T.presheaf.stalk x)
      (((Tor (ModuleCat (T.presheaf.stalk x)) n).obj N).obj
        ((ModuleCat.restrictScalars
          ((T.presheaf.stalkCongr (.of_eq hd)).hom ≫
            (I.comap p).subschemeι.stalkMap d).hom).obj
          (ModuleCat.of ((I.comap p).subscheme.presheaf.stalk d)
            ((I.comap p).subscheme.presheaf.stalk d)))) =
    Module.length (X.presheaf.stalk (p x))
      (((Tor (ModuleCat (X.presheaf.stalk (p x))) n).obj
        ((ModuleCat.restrictScalars (p.stalkMap x).hom).obj N)).obj
        ((ModuleCat.restrictScalars
          ((X.presheaf.stalkCongr (.of_eq he)).hom ≫ I.subschemeι.stalkMap e).hom).obj
          (ModuleCat.of (I.subscheme.presheaf.stalk e) (I.subscheme.presheaf.stalk e)))) := by
  cases hx
  exact (length_restrictScalars_stalkMap_of_preimmersion_comp p i c _).symm.trans
    (comapStalkTorIsoOfFlat p I (i c) d e hd he N n).toLinearEquiv.length_eq

end AlgebraicGeometry.Scheme.Hom

/-!
## Composite-stalk Tor interfaces from strict affine-line invariance

Uncompiled integration draft. The original Tor-length interfaces above are retained.
The following three declarations are copied from
`codex/strict-a1-final@6fac947390fb8144a79ee31acbb98686baf0f7f2`,
`Colib/AlgebraicGeometry/Intersection/FlatProjectionStalkTor.lean`.
Original strict source attribution: Authors kangxyz, Apache-2.0.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

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

end
