/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.FlatPullback
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.NormalSupport
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.BaseChangeData
import Colib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineClosedSectionNeighborhood
import StacksFrontier.AlgebraicGeometry.DeformationNormalCone.ConormalNaturality

/-! # Change of base for the original closed-pair deformation -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Deformation

universe u

namespace Stacks.Deformation

open Opposite Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec Stacks.SymAlgSheaf

section Sections

variable {U U' : Scheme.{u}} (h : U' ⟶ U) (J : U.IdealSheafData) (J' : U'.IdealSheafData)
  (hJ : J.comap h ≤ J')

-- Adapted from the affine formula `Stacks.Deformation.deformationMap_appLE_chartIncl`.
/-- The original morphism of deformations pulls back homogeneous sections over every open. -/
theorem deformationMap_appLE_chartIncl_of_opens (W : U.Opens) (k : ℤ)
    (x : ((extReesGradedAlgebra J).piece k).val.obj (op W))
    (hle : (deformationSpaceToBase J' ≫ h) ⁻¹ᵁ W ≤
      deformationMap h J J' hJ ⁻¹ᵁ (deformationSpaceToBase J ⁻¹ᵁ W)) :
    ((deformationMap h J J' hJ).appLE (deformationSpaceToBase J ⁻¹ᵁ W)
        ((deformationSpaceToBase J' ≫ h) ⁻¹ᵁ W) hle).hom (chartIncl J k W x) =
      chartIncl J' k (h ⁻¹ᵁ W) (extReesPullback h J J' hJ k W x) := by
  have happLE := pairToHom_appLE_of_opens (deformationPair h J J' hJ) W hle
  refine (congrArg (fun φ => φ.hom (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U
    (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J)).hom.right.hom.app (op W)).hom
      (ungradedAlgebraSheafIncl U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) k
        W x))) happLE).trans ?_
  have hinv : ((ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
      (extReesGradedAlgebra_mul_comm J)).inv.right.hom.app (op W)).hom
      (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
        (extReesGradedAlgebra_mul_comm J)).hom.right.hom.app (op W)).hom
        (ungradedAlgebraSheafIncl U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) k
          W x)) =
      ungradedAlgebraSheafIncl U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) k
        W x :=
    congrArg (fun k' : ungradedAlgebraSheaf U (extReesGradedAlgebra J)
        (extReesGradedAlgebra_mul_comm J) ⟶ ungradedAlgebraSheaf U (extReesGradedAlgebra J)
        (extReesGradedAlgebra_mul_comm J) => (k'.right.hom.app (op W)).hom
          (ungradedAlgebraSheafIncl U (extReesGradedAlgebra J) (extReesGradedAlgebra_mul_comm J) k
            W x))
      (ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
        (extReesGradedAlgebra_mul_comm J)).hom_inv_id
  change ((universalAlgebraMap (extReesSituation J')).right.app (op (h ⁻¹ᵁ W))).hom
      (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U' (extReesGradedAlgebra J')
        (extReesGradedAlgebra_mul_comm J')).hom.right.hom.app (op (h ⁻¹ᵁ W))).hom
        (((deformationUngradedHom h J J' hJ).right.hom.app (op W)).hom
          (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
            (extReesGradedAlgebra_mul_comm J)).inv.right.hom.app (op W)).hom
            (((ungradedAlgebraSheafIsoGradedAlgebraSheaf U (extReesGradedAlgebra J)
              (extReesGradedAlgebra_mul_comm J)).hom.right.hom.app (op W)).hom
              (ungradedAlgebraSheafIncl U (extReesGradedAlgebra J)
                (extReesGradedAlgebra_mul_comm J) k W x))))) = _
  rw [hinv, deformationUngradedHom_app_incl]
  rfl

end Sections

/-- The original morphisms of deformation spaces compose according to their base maps. -/
theorem deformationMap_comp
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (K : Z.IdealSheafData)
    (hf : I.comap f ≤ J) (hg : J.comap g ≤ K) (hfg : I.comap (g ≫ f) ≤ K) :
    deformationMap g J K hg ≫ deformationMap f I J hf = deformationMap (g ≫ f) I K hfg := by
  let a := deformationMap f I J hf
  let b := deformationMap g J K hg
  let c := deformationMap (g ≫ f) I K hfg
  let πI := deformationSpaceToBase I
  let πJ := deformationSpaceToBase J
  let πK := deformationSpaceToBase K
  have ha : a ≫ πI = πJ ≫ f := deformationMap_toBase f I J hf
  have hb : b ≫ πJ = πK ≫ g := deformationMap_toBase g J K hg
  have hc : c ≫ πI = πK ≫ g ≫ f := deformationMap_toBase (g ≫ f) I K hfg
  have hd : (b ≫ a) ≫ πI = πK ≫ g ≫ f := by
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc]
  refine hom_ext_deformationSpace I (b ≫ a) c (hd.trans hc.symm) ?_
  intro W d x h₁ h₂
  let V : Y.Opens := f ⁻¹ᵁ W.1
  let U := ((b ≫ a) ≫ πI) ⁻¹ᵁ W.1
  have hU : U = πK ⁻¹ᵁ (g ⁻¹ᵁ V) := by
    change (((b ≫ a) ≫ πI) ⁻¹ᵁ W.1) = _
    rw [hd]
    rfl
  have hA : πJ ⁻¹ᵁ V ≤ a ⁻¹ᵁ (πI ⁻¹ᵁ W.1) := by
    exact le_of_eq (congrArg (fun f => f ⁻¹ᵁ W.1) ha.symm)
  have hB : πK ⁻¹ᵁ (g ⁻¹ᵁ V) ≤ b ⁻¹ᵁ (πJ ⁻¹ᵁ V) := by
    exact le_of_eq (congrArg (fun f => f ⁻¹ᵁ V) hb.symm)
  let hCa : πK ⁻¹ᵁ ((g ≫ f) ⁻¹ᵁ W.1) ≤ c ⁻¹ᵁ (πI ⁻¹ᵁ W.1) := by
    exact le_of_eq (congrArg (fun f => f ⁻¹ᵁ W.1) hc.symm)
  let hBa : πK ⁻¹ᵁ (g ⁻¹ᵁ V) ≤ (b ≫ a) ⁻¹ᵁ (πI ⁻¹ᵁ W.1) := by
    exact le_of_eq (congrArg (fun f => f ⁻¹ᵁ W.1) hd.symm)
  suffices he : ((b ≫ a).appLE (πI ⁻¹ᵁ W.1) (πK ⁻¹ᵁ (g ⁻¹ᵁ V)) hBa).hom
      (chartIncl I d W.1 x) =
    (c.appLE (πI ⁻¹ᵁ W.1) (πK ⁻¹ᵁ ((g ≫ f) ⁻¹ᵁ W.1)) hCa).hom
      (chartIncl I d W.1 x) by
    exact Eq.rec (motive := fun V' hV => ∀ h₁' h₂',
      ((b ≫ a).appLE (πI ⁻¹ᵁ W.1) V' h₁').hom (chartIncl I d W.1 x) =
        (c.appLE (πI ⁻¹ᵁ W.1) V' h₂').hom (chartIncl I d W.1 x))
      (fun _ _ => he) hU.symm h₁ h₂
  have hcomp := Scheme.Hom.appLE_comp_appLE b a (πI ⁻¹ᵁ W.1) (πJ ⁻¹ᵁ V)
    (πK ⁻¹ᵁ (g ⁻¹ᵁ V)) hA hB
  let x' := extReesPullback f I J hf d W.1 x
  have h₁' := deformationMap_appLE_chartIncl' f I J hf W d x hA
  have h₂' := deformationMap_appLE_chartIncl_of_opens g J K hg V d x' hB
  have h₃' := deformationMap_appLE_chartIncl' (g ≫ f) I K hfg W d x hCa
  rw [← hcomp, CommRingCat.comp_apply]
  refine (congrArg ((b.appLE (πJ ⁻¹ᵁ V) (πK ⁻¹ᵁ (g ⁻¹ᵁ V)) hB).hom) h₁').trans
    (h₂'.trans (Eq.trans ?_ h₃'.symm))
  apply congrArg (chartIncl K d (g ⁻¹ᵁ V))
  apply extReesAmbient_injective K d (g ⁻¹ᵁ V)
  rw [extReesAmbient_extReesPullback, extReesAmbient_extReesPullback]
  have hc' := extReesAmbient_extReesPullback (g ≫ f) I K hfg d W.1 x
  rw [Scheme.Hom.comp_app, CommRingCat.comp_apply] at hc'
  exact hc'.symm

end Stacks.Deformation

namespace AlgebraicGeometry.MotivicHomotopy

section BaseChange

open Opposite

variable {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {j : Z' ⟶ X'}
  [IsClosedImmersion i] [IsClosedImmersion j] {a : X' ⟶ X} {b : Z' ⟶ Z}
  (h : IsPullback j b a i)

/-- Over a flat map of coborders the literal morphism of deformation spaces
is the pullback of the original projection. -/
theorem isPullback_deformationMapOver_coborder [Flat (coborderMapOver i j a)] :
    IsPullback (deformationMapOver h) (deformationSpaceToBase (Stacks.Conormal.coborderIdeal j))
      (deformationSpaceToBase (Stacks.Conormal.coborderIdeal i)) (coborderMapOver i j a) := by
  let f := coborderMapOver i j a
  let I := Stacks.Conormal.coborderIdeal i
  let J := Stacks.Conormal.coborderIdeal j
  let e := deformationSpaceFlatPullbackIso f I
  have hJ : I.comap f = J := coborderIdeal_baseChange h
  have H : ∀ (K : j.coborderRange.toScheme.IdealSheafData) (hK : I.comap f = K),
      IsPullback (deformationMap f I K hK.le) (deformationSpaceToBase K)
        (deformationSpaceToBase I) f := by
    intro K hK
    subst K
    exact IsPullback.of_iso_pullback ⟨deformationMap_toBase f I _ le_rfl⟩ e
      (deformationSpaceFlatPullbackIso_hom_fst f I)
      (deformationSpaceFlatPullbackIso_hom_snd f I)
  exact H J hJ

/-- The original ambient fibre-one arrows commute with the native map of
deformation spaces induced by a cartesian map of closed pairs. -/
theorem closedPairOneSection_deformationMapOver :
    closedPairOneSection j ≫ deformationMapOver h = a ≫ closedPairOneSection i := by
  let : IsIso i.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion i
  let : IsIso j.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion j
  let f := coborderMapOver i j a
  have hc : inv j.coborderRange.ι ≫ f = a ≫ inv i.coborderRange.ι := by
    apply (cancel_mono i.coborderRange.ι).1
    rw [Category.assoc, show f ≫ i.coborderRange.ι = j.coborderRange.ι ≫ a
          from coborderMapOver_ι i j a, IsIso.inv_hom_id_assoc, Category.assoc,
      IsIso.inv_hom_id, Category.comp_id]
  change (inv j.coborderRange.ι ≫ deformationOneSection (Stacks.Conormal.coborderIdeal j)) ≫
      deformationMapOver h = a ≫ inv i.coborderRange.ι ≫
        deformationOneSection (Stacks.Conormal.coborderIdeal i)
  rw [Category.assoc, ← deformationOneSection_naturality (Stacks.Conormal.coborderIdeal i)
    f (Stacks.Conormal.coborderIdeal j) (coborderIdeal_baseChange h).le,
    ← Category.assoc, hc, Category.assoc]

/-- The original morphism between the zero-ideal deformations of the two centres. -/
def deformationCentreMap :
    deformationSpace (⊥ : Z'.IdealSheafData) ⟶ deformationSpace (⊥ : Z.IdealSheafData) :=
  deformationMap b ⊥ ⊥ (by rw [Scheme.IdealSheafData.comap_bot])

include h in
/-- The native deformation morphism commutes with the original closed support maps. -/
theorem deformationSupportMap_deformationMapOver :
    deformationSupportMap j ≫ deformationMapOver h =
      deformationCentreMap (b := b) ≫ deformationSupportMap i := by
  let f := coborderMapOver i j a
  let I := Stacks.Conormal.coborderIdeal i
  let J := Stacks.Conormal.coborderIdeal j
  have hh : j.liftCoborder ≫ f = b ≫ i.liftCoborder := (isPullback_liftCoborder h).w
  have h₁ : I.comap (j.liftCoborder ≫ f) ≤ (⊥ : Z'.IdealSheafData) := by
    rw [Scheme.IdealSheafData.comap_comp, coborderIdeal_baseChange h,
      coborderIdeal_comap_liftCoborder]
  have h₂ : I.comap (b ≫ i.liftCoborder) ≤ (⊥ : Z'.IdealSheafData) := hh ▸ h₁
  have l := deformationMap_comp f j.liftCoborder I J ⊥
    (coborderIdeal_baseChange h).le (coborderIdeal_comap_liftCoborder j).le h₁
  have r := deformationMap_comp i.liftCoborder b I ⊥ ⊥
    (coborderIdeal_comap_liftCoborder i).le (by rw [Scheme.IdealSheafData.comap_bot]) h₂
  have hcongr (f₁ f₂ : Z' ⟶ i.coborderRange.toScheme) (hf : f₁ = f₂)
      (h₁ : I.comap f₁ ≤ (⊥ : Z'.IdealSheafData))
      (h₂ : I.comap f₂ ≤ (⊥ : Z'.IdealSheafData)) :
      deformationMap f₁ I ⊥ h₁ = deformationMap f₂ I ⊥ h₂ := by
    subst f₂
    rfl
  exact l.trans ((hcongr _ _ hh h₁ h₂).trans r.symm)

/-- The deformation of the centre is cartesian over the original centre. -/
theorem isPullback_deformationCentreMap [Flat b] :
    IsPullback (deformationCentreMap (b := b))
      (deformationSpaceToBase (⊥ : Z'.IdealSheafData))
      (deformationSpaceToBase (⊥ : Z.IdealSheafData)) b := by
  let I : Z.IdealSheafData := ⊥
  have hI : I.comap b = ⊥ := Scheme.IdealSheafData.comap_bot b
  have H : ∀ (J : Z'.IdealSheafData) (hJ : I.comap b = J),
      IsPullback (deformationMap b I J hJ.le) (deformationSpaceToBase J)
        (deformationSpaceToBase I) b := by
    intro J hJ
    subst J
    exact IsPullback.of_iso_pullback ⟨deformationMap_toBase b I _ le_rfl⟩
      (deformationSpaceFlatPullbackIso b I) (deformationSpaceFlatPullbackIso_hom_fst b I)
      (deformationSpaceFlatPullbackIso_hom_snd b I)
  exact H _ hI

/-- The square of literal closed deformation supports over a flat map of pairs is cartesian. -/
theorem isPullback_deformationSupportMap_deformationMapOver [Flat a] :
    IsPullback (deformationSupportMap j) (deformationCentreMap (b := b))
      (deformationMapOver h) (deformationSupportMap i) := by
  let f := coborderMapOver i j a
  have : Flat b := MorphismProperty.of_isPullback h (inferInstance : Flat a)
  have hf : Flat f := by
    have : IsIso i.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion i
    have : IsIso j.coborderRange.ι := isIso_coborderRange_ι_of_isClosedImmersion j
    have h₀ : f = j.coborderRange.ι ≫ a ≫ inv i.coborderRange.ι := by
      apply (cancel_mono i.coborderRange.ι).1
      rw [coborderMapOver_ι, Category.assoc, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id]
    rw [h₀]
    infer_instance
  have htop := isPullback_deformationMapOver_coborder h
  have hbot := isPullback_liftCoborder h
  have hcentre := isPullback_deformationCentreMap (b := b)
  have hwhole := hcentre.paste_vert hbot.flip
  rw [← deformationSupportMap_toBase i, ← deformationSupportMap_toBase j] at hwhole
  exact hwhole.flip.of_right (deformationSupportMap_deformationMapOver h) htop.flip

variable {S : Scheme.{u}} (p : X ⟶ S) (p' : X' ⟶ S)
  [Smooth p] [Smooth p'] [Smooth (i ≫ p)] [Smooth (j ≫ p')]

private theorem ker_normalBundleToDeformation_baseChange :
    (Stacks.Deformation.normalBundleToDeformation i p).ker.comap (deformationMapOver h) =
      (Stacks.Deformation.normalBundleToDeformation j p').ker := by
  rw [Stacks.Deformation.ker_normalBundleToDeformation i p,
    Stacks.Deformation.ker_normalBundleToDeformation j p']
  exact comap_zeroScheme_paramGlobal _ _ _ (coborderIdeal_baseChange h).le

/-- The actual map of normal-bundle fibres is induced by the native
deformation map on the scheme-theoretic parameter-zero fibre. -/
def deformationNormalFibreMap : Stacks.Conormal.normalBundle j ⟶ Stacks.Conormal.normalBundle i :=
  IsClosedImmersion.lift (Stacks.Deformation.normalBundleToDeformation i p)
    (Stacks.Deformation.normalBundleToDeformation j p' ≫ deformationMapOver h) (by
      rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le,
        ker_normalBundleToDeformation_baseChange h p p'])

/-- The original normal-bundle maps are cartesian over the deformation map. -/
theorem isPullback_deformationNormalFibreMap :
    IsPullback (Stacks.Deformation.normalBundleToDeformation j p')
      (deformationNormalFibreMap h p p') (deformationMapOver h)
      (Stacks.Deformation.normalBundleToDeformation i p) :=
  isPullback_of_isClosedImmersion (Stacks.Deformation.normalBundleToDeformation j p')
    (Stacks.Deformation.normalBundleToDeformation i p) (deformationNormalFibreMap h p p')
    (deformationMapOver h) (IsClosedImmersion.lift_fac _ _ _).symm
    (ker_normalBundleToDeformation_baseChange h p p')

private theorem deformationCentreMap_zeroSection :
    deformationZeroSectionBot Z' ≫ deformationCentreMap (b := b) =
      b ≫ deformationZeroSectionBot Z := by
  let f := deformationCentreMap (b := b)
  let q := deformationZeroSectionBot Z
  let q' := deformationZeroSectionBot Z'
  have hker : q.ker.comap f = q'.ker := by
    dsimp only [q, q']
    rw [ker_deformationZeroSectionBot, ker_deformationZeroSectionBot]
    exact comap_zeroScheme_paramGlobal b ⊥ ⊥ (by rw [Scheme.IdealSheafData.comap_bot])
  let e := IsClosedImmersion.lift q (q' ≫ f) (by
    rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.le_map_iff_comap_le, hker])
  have he : e ≫ q = q' ≫ f := IsClosedImmersion.lift_fac _ _ _
  have hf : f ≫ deformationSpaceToBase (⊥ : Z.IdealSheafData) =
      deformationSpaceToBase (⊥ : Z'.IdealSheafData) ≫ b := deformationMap_toBase _ _ _ _
  have hbase : e = b := by
    calc
      e = e ≫ q ≫ deformationSpaceToBase (⊥ : Z.IdealSheafData) := by
        dsimp only [q]
        rw [deformationZeroSectionBot_toBase, Category.comp_id]
      _ = (q' ≫ f) ≫ deformationSpaceToBase (⊥ : Z.IdealSheafData) := by
        rw [← Category.assoc, he]
      _ = b := by
        dsimp only [q']
        rw [Category.assoc, hf, ← Category.assoc, deformationZeroSectionBot_toBase,
          Category.id_comp]
  exact he.symm.trans (congrArg (· ≫ q) hbase)

/-- The zero section in the conormal model of the normal bundle. -/
abbrev actualNormalZeroSection {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] :=
  Scheme.Modules.vectorBundleZeroSection Z (Stacks.Conormal.conormalSheafDegreeOne i)

/-- The map induced on the normal fibres takes the actual zero section to
the actual zero section over the original centre map. -/
theorem deformationNormalFibreMap_zeroSection :
    actualNormalZeroSection j ≫ deformationNormalFibreMap h p p' =
      b ≫ actualNormalZeroSection i := by
  apply (cancel_mono (Stacks.Deformation.normalBundleToDeformation i p)).1
  have hN := (isPullback_deformationNormalFibreMap h p p').w
  have hS := deformationSupportMap_deformationMapOver h
  rw [Category.assoc, ← hN, ← Category.assoc,
    ← deformationZeroSectionBot_comp_deformationSupportMap j p', Category.assoc, hS,
    ← Category.assoc, deformationCentreMap_zeroSection, Category.assoc,
    deformationZeroSectionBot_comp_deformationSupportMap i p]
  exact (Category.assoc _ _ _).symm

/-- The map of literal normal-bundle pairs is cartesian over the corresponding
map of closed deformation pairs. -/
theorem isPullback_deformationNormalZeroSection [Flat a] :
    IsPullback (actualNormalZeroSection j) b (deformationNormalFibreMap h p p')
      (actualNormalZeroSection i) := by
  let D := deformationMapOver h
  let C := deformationCentreMap (b := b)
  let q := deformationZeroSectionBot Z
  let q' := deformationZeroSectionBot Z'
  let z := actualNormalZeroSection i
  let z' := actualNormalZeroSection j
  let N := Stacks.Deformation.normalBundleToDeformation i p
  let N' := Stacks.Deformation.normalBundleToDeformation j p'
  have hw := deformationCentreMap_zeroSection (b := b)
  have hker : q.ker.comap C = q'.ker := by
    dsimp only [q, q']
    rw [ker_deformationZeroSectionBot, ker_deformationZeroSectionBot]
    exact comap_zeroScheme_paramGlobal b ⊥ ⊥ (by rw [Scheme.IdealSheafData.comap_bot])
  have hq : IsPullback q' b C q := isPullback_of_isClosedImmersion q' q b C hw hker
  have hD := isPullback_deformationSupportMap_deformationMapOver h
  have hwhole := hq.paste_horiz hD
  have hw₁ : q ≫ deformationSupportMap i = z ≫ N :=
    deformationZeroSectionBot_comp_deformationSupportMap i p
  have hw₂ : q' ≫ deformationSupportMap j = z' ≫ N' :=
    deformationZeroSectionBot_comp_deformationSupportMap j p'
  rw [hw₁, hw₂] at hwhole
  exact hwhole.of_right (deformationNormalFibreMap_zeroSection h p p')
    (isPullback_deformationNormalFibreMap h p p')

end BaseChange

/-- The common étale neighborhood of two affine marked charts can be
chosen affine while retaining the whole scheme-theoretic closed centre. -/
theorem exists_affine_common_etale_neighborhood
    {Z X Y T : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine T]
    (i : Z ⟶ X) (j : Z ⟶ Y) (f : X ⟶ T) (g : Y ⟶ T)
    [IsClosedImmersion i] [IsClosedImmersion j] [Etale f] [Etale g]
    (h : i ≫ f = j ≫ g) :
    ∃ (W : Scheme.{u}) (_ : IsAffine W) (a : W ⟶ X) (b : W ⟶ Y) (s : Z ⟶ W),
      Etale a ∧ Etale b ∧ a ≫ f = b ≫ g ∧ s ≫ a = i ∧ s ≫ b = j ∧
        IsPullback s (𝟙 Z) a i ∧ IsPullback s (𝟙 Z) b j := by
  let C := pullback f g
  let p : C ⟶ X := pullback.fst f g
  let q : C ⟶ Y := pullback.snd f g
  let t : Z ⟶ C := pullback.lift i j h
  have htp : t ≫ p = i := pullback.lift_fst _ _ _
  have htq : t ≫ q = j := pullback.lift_snd _ _ _
  let : IsAffine C := inferInstanceAs (IsAffine (pullback f g))
  let : Etale p := inferInstanceAs (Etale (pullback.fst f g))
  let : Etale q := inferInstanceAs (Etale (pullback.snd f g))
  have : IsClosedImmersion (t ≫ p) := htp.symm ▸ inferInstance
  let : IsClosedImmersion t := IsClosedImmersion.of_comp t p
  obtain ⟨U, u, hu, hU⟩ := exists_open_isPullback_of_etale_lift i p t htp
  obtain ⟨V, v, hv, hV⟩ := exists_open_isPullback_of_etale_lift j q t htq
  have hT : Set.range t ⊆ (U ⊓ V : C.Opens) := by
    rintro _ ⟨z, rfl⟩
    change t z ∈ U ∧ t z ∈ V
    exact ⟨(congrArg (fun e : Z ⟶ C => e z) hu) ▸ (u z).property,
      (congrArg (fun e : Z ⟶ C => e z) hv) ▸ (v z).property⟩
  obtain ⟨r, hr, hR⟩ := Scheme.exists_basicOpen_between_closed (Set.range t)
    t.isClosedEmbedding.isClosed_range (U ⊓ V) hT
  let A := C.basicOpen r
  let : IsAffine A.toScheme := (isAffineOpen_top C).basicOpen r
  let w : Z ⟶ A.toScheme := IsOpenImmersion.lift A.ι t (by simpa using hr)
  have hw : w ≫ A.ι = t := IsOpenImmersion.lift_fac _ _ _
  let eU := C.homOfLE (hR.trans inf_le_left)
  let eV := C.homOfLE (hR.trans inf_le_right)
  have heU : eU ≫ U.ι = A.ι := C.homOfLE_ι _
  have heV : eV ≫ V.ι = A.ι := C.homOfLE_ι _
  have hwu : w ≫ eU = u := by
    apply (cancel_mono U.ι).1
    rw [Category.assoc, heU, hw, hu]
  have hwv : w ≫ eV = v := by
    apply (cancel_mono V.ι).1
    rw [Category.assoc, heV, hw, hv]
  have hRU : Set.range u ⊆ Set.range eU := by
    rintro _ ⟨z, rfl⟩
    exact ⟨w z, congrArg (fun f : Z ⟶ U.toScheme => f z) hwu⟩
  have hRV : Set.range v ⊆ Set.range eV := by
    rintro _ ⟨z, rfl⟩
    exact ⟨w z, congrArg (fun f : Z ⟶ V.toScheme => f z) hwv⟩
  have hℓ : IsPullback w (𝟙 Z) eU u := by
    rw [IsOpenImmersion.lift_uniq eU u hRU w hwu]
    exact IsOpenImmersion.isPullback_lift_id u eU hRU
  have hr' : IsPullback w (𝟙 Z) eV v := by
    rw [IsOpenImmersion.lift_uniq eV v hRV w hwv]
    exact IsOpenImmersion.isPullback_lift_id v eV hRV
  refine ⟨A.toScheme, inferInstance, A.ι ≫ p, A.ι ≫ q, w, inferInstance, inferInstance,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Category.assoc] using congrArg (A.ι ≫ ·) (pullback.condition (f := f) (g := g))
  · rw [← Category.assoc, hw, htp]
  · rw [← Category.assoc, hw, htq]
  · simpa only [Category.assoc, reassoc_of% heU, Category.comp_id] using hℓ.paste_vert hU
  · simpa only [Category.assoc, reassoc_of% heV, Category.comp_id] using hr'.paste_vert hV

end AlgebraicGeometry.MotivicHomotopy
