/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

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
