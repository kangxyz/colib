/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.OneFibreAlgebra
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSection
import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleZeroSectionConormal
import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraSheafDegreewise
import StacksFrontier.AlgebraicGeometry.RelativeSpec.RetractionSectionAlgebraHom

/-!
# The normal zero section in the deformation support

The zero section of the actual normal bundle is the intersection of the
deformation support with the fibre at the original parameter zero.
The comparison uses the canonical augmentation of the symmetric algebra.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Conormal Stacks.RelativeSpec

universe u

namespace Stacks.Deformation

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

section Augmentation

variable [IsIso (conormalSymmetricAlgebraSheafHom i)]

private def coneAugmentation : (conormalAlgebraSheaf i).right.obj ⟶ Z.presheaf :=
  (asIso (conormalSymmetricAlgebraSheafHom i)).inv.right.hom ≫
    Scheme.Modules.symmetricAlgebraSheafAugmentation Z (conormalSheafDegreeOne i)

private theorem coneAugmentation_retraction :
    (conormalAlgebraSheaf i).hom.hom ≫ coneAugmentation i = 𝟙 Z.presheaf := by
  rw [coneAugmentation, ← Category.assoc,
    AlgebraSheaf.hom_comp_right_hom (asIso (conormalSymmetricAlgebraSheafHom i)).inv]
  exact Scheme.Modules.hom_comp_symmetricAlgebraSheafAugmentation Z (conormalSheafDegreeOne i)

private theorem comp_coneAugmentation :
    (conormalSymmetricAlgebraSheafHom i).right.hom ≫ coneAugmentation i =
      Scheme.Modules.symmetricAlgebraSheafAugmentation Z (conormalSheafDegreeOne i) := by
  have h : (conormalSymmetricAlgebraSheafHom i ≫
      (asIso (conormalSymmetricAlgebraSheafHom i)).inv).right.hom =
      𝟙 (normalBundleAlgebra i).right.obj :=
    congrArg (fun f => f.right.hom) (asIso (conormalSymmetricAlgebraSheafHom i)).hom_inv_id
  rw [coneAugmentation, ← Category.assoc, AlgebraSheaf.comp_right_hom, h, Category.id_comp]

private def coneSection : Z ⟶ normalCone i :=
  retractionSection (normalConeSituation i) (coneAugmentation i) (coneAugmentation_retraction i)

private theorem coneSection_toBase :
    coneSection i ≫ normalConeToBase i = 𝟙 Z :=
  retractionSection_comp_toBase (normalConeSituation i) (coneAugmentation i)
    (coneAugmentation_retraction i)

private theorem coneSection_comp_comparison :
    coneSection i ≫ normalConeToNormalBundle i =
      Scheme.Modules.vectorBundleZeroSection Z (conormalSheafDegreeOne i) := by
  refine (retractionSection_comp_relativeSpectrumMapOfAlgebraHom
    (normalBundleSituation i) (conormalAlgebraSheaf i) (isQuasicoherent_conormalAlgebraSheaf i)
    (conormalSymmetricAlgebraSheafHom i) (coneAugmentation i) (coneAugmentation_retraction i)).trans
      ?_
  exact retractionSection_congr _ _ (comp_coneAugmentation i)

private theorem coneAugmentation_ungradedIncl (V : Z.Opens) (n : ℤ) (hn : n ≠ 0)
    (hiso : IsIso ((conormalSymmetricHom i).app n))
    (x : ((conormalAlgebra i).algebra.piece n).val.obj (op V)) :
    ((coneAugmentation i).app (op V)).hom ((conormalAlgebra i).algebra.ungradedIncl n x) = 0 := by
  let E := conormalSheafDegreeOne i
  have : IsIso (((conormalSymmetricHom i).app n).val.app (op V)) :=
    inferInstanceAs (IsIso
      ((_root_.SheafOfModules.evaluation (R := Z.ringCatSheaf) (op V)).map
        ((conormalSymmetricHom i).app n)))
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso
    (((conormalSymmetricHom i).app n).val.app (op V))).2 x
  have hF := (conormalSymmetricAlgebraSheafHom_ungradedIncl i n V y).trans
    (congrArg (fun z => (conormalAlgebra i).algebra.ungradedIncl n z) hy)
  have hρ := ConcreteCategory.congr_hom (NatTrans.congr_app (comp_coneAugmentation i) (op V))
    ((conormalSymmetricAlgebra i).ungradedIncl n y)
  refine (congrArg ((coneAugmentation i).app (op V)).hom hF.symm).trans (hρ.trans ?_)
  exact (Stacks.SymAlgSections.symmetricAlgebraSheafAugmentation_app_totalUnit E (op V) _).trans
    (Stacks.SymAlgSections.symmetricAlgebraTotalAugmentation_app_incl_of_ne E hn (op V) y)

private theorem coneSection_appLE_universalAlgebraMap (V : Z.affineOpens)
    (h : V.1 ≤ coneSection i ⁻¹ᵁ (normalConeToBase i ⁻¹ᵁ V.1))
    (a : (conormalAlgebraSheaf i).right.obj.obj (op V.1)) :
    ((coneSection i).appLE _ V.1 h).hom
        (((universalAlgebraMap (normalConeSituation i)).right.app (op V.1)).hom a) =
      ((coneAugmentation i).app (op V.1)).hom a :=
  ConcreteCategory.congr_hom
    (pairToHom_appLE
      (retractionPair (normalConeSituation i) (coneAugmentation i) (coneAugmentation_retraction i))
      V h) a

end Augmentation

private theorem comp_appLE_eq_zero_of_appLE_eq_zero {A B C : Scheme.{u}}
    (f : A ⟶ B) (g : B ⟶ C) {U : C.Opens} {V : B.Opens} {W W' : A.Opens}
    (hV : V ≤ g ⁻¹ᵁ U) (hW : W ≤ f ⁻¹ᵁ V) (h : W' ≤ W)
    (h' : W' ≤ (f ≫ g) ⁻¹ᵁ U) (x : Γ(C, U))
    (hx : (f.appLE V W hW).hom ((g.appLE U V hV).hom x) = 0) :
    ((f ≫ g).appLE U W' h').hom x = 0 := by
  have hc := Scheme.Hom.appLE_comp_appLE f g U V W' hV (h.trans hW)
  have hr := Scheme.Hom.appLE_map f hW (homOfLE h).op
  exact (ConcreteCategory.congr_hom hc x).symm.trans
    ((ConcreteCategory.congr_hom hr ((g.appLE U V hV).hom x)).symm.trans
      ((congrArg (A.presheaf.map (homOfLE h).op).hom hx).trans (map_zero _)))

section Comparison

variable [IsIso (conormalSymmetricAlgebraSheafHom i)]

private theorem coneSection_comp_normalConeToDeformation_appLE_of_ne
    (hiso : ∀ n, IsIso ((conormalSymmetricHom i).app n))
    (W : i.coborderRange.toScheme.affineOpens) (n : ℤ) (hn : n ≠ 0)
    (x : ((extReesGradedAlgebra (coborderIdeal i)).piece n).val.obj (op W.1))
    (h₁ : (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ W.1 ≤
      normalConeToDeformation i ⁻¹ᵁ (deformationSpaceToBase (coborderIdeal i) ⁻¹ᵁ W.1))
    (h₂ : i.liftCoborder ⁻¹ᵁ W.1 ≤
      coneSection i ⁻¹ᵁ (normalConeToBase i ⁻¹ᵁ (i.liftCoborder ⁻¹ᵁ W.1))) :
    ((coneSection i).appLE _ _ h₂).hom
        (((normalConeToDeformation i).appLE _ _ h₁).hom (chartIncl (coborderIdeal i) n W.1 x)) =
      0 := by
  let V : Z.affineOpens := ⟨i.liftCoborder ⁻¹ᵁ W.1, W.2.preimage i.liftCoborder⟩
  let e := ungradedAlgebraSheafIsoGradedAlgebraSheaf Z (conormalAlgebra i).algebra
    (conormalAlgebra i).mul_comm_int
  refine (congrArg ((coneSection i).appLE _ _ h₂).hom
    (normalConeToDeformation_appLE_chartIncl i W n x h₁)).trans ?_
  refine (coneSection_appLE_universalAlgebraMap i V h₂
    ((e.hom.right.hom.app (op V.1)).hom (toConormalExtAdd i n (op W.1) x))).trans ?_
  let f := (e.hom.right.hom.app (op V.1)).hom
  let g := ((coneAugmentation i).app (op V.1)).hom
  change g (f (toConormalExtAdd i n (op W.1) x)) = 0
  rcases lt_or_ge n 0 with hneg | hnonneg
  · have hz := congrArg (fun φ => φ x) (toConormalExtAdd_of_neg i hneg (op W.1))
    exact (congrArg (fun a => g (f a)) hz).trans
      ((congrArg g (map_zero f)).trans (map_zero g))
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hnonneg
    have hd := congrArg (fun φ => φ x) (toConormalExtAdd_of_nonneg i hnonneg (op W.1))
    refine (congrArg (fun a => g (f a)) (hd.trans (toConormalAdd_apply i m _ x))).trans ?_
    exact (congrArg g (ungradedToGradedRight_ungradedAlgebraSheafIncl Z
      (conormalAlgebra i).algebra (conormalAlgebra i).mul_comm_int (m : ℤ) V.1 _)).trans
        (coneAugmentation_ungradedIncl i V.1 (m : ℤ) hn (hiso _) _)

private theorem deformationZeroSectionBot_comp_deformationSupportMap_toCone
    (hiso : ∀ n, IsIso ((conormalSymmetricHom i).app n)) :
    deformationZeroSectionBot Z ≫ deformationSupportMap i =
      coneSection i ≫ normalConeToDeformation i := by
  let I := coborderIdeal i
  let π := deformationSpaceToBase I
  let π₀ := deformationSpaceToBase (⊥ : Z.IdealSheafData)
  let t := deformationZeroSectionBot Z
  let s := deformationSupportMap i
  let z := coneSection i
  let κ := normalConeToDeformation i
  have hs : s ≫ π = π₀ ≫ i.liftCoborder := deformationSupportMap_toBase i
  have hκ : κ ≫ π = normalConeToBase i ≫ i.liftCoborder := normalConeToDeformation_toBase i
  have hL : (t ≫ s) ≫ π = i.liftCoborder := by
    rw [Category.assoc, hs, ← Category.assoc, deformationZeroSectionBot_toBase, Category.id_comp]
  have hR : (z ≫ κ) ≫ π = i.liftCoborder := by
    rw [Category.assoc, hκ, ← Category.assoc, coneSection_toBase, Category.id_comp]
  have hb := hL.trans hR.symm
  refine hom_ext_deformationSpace I (t ≫ s) (z ≫ κ) hb fun W n x h₁ h₂ => ?_
  let W' := ((t ≫ s) ≫ π) ⁻¹ᵁ W.1
  let V : Z.affineOpens := ⟨i.liftCoborder ⁻¹ᵁ W.1, W.2.preimage i.liftCoborder⟩
  let K := π ⁻¹ᵁ W.1
  have hV : W' ≤ V.1 := by
    change ((t ≫ s) ≫ π) ⁻¹ᵁ W.1 ≤ i.liftCoborder ⁻¹ᵁ W.1
    rw [hL]
  by_cases hn : n = 0
  · subst n
    let a := extReesAmbient I 0 W.1 x
    have hx : extReesOfMem I W 0 a (by simp) = x :=
      extReesAmbient_injective I 0 W.1 (extReesAmbient_extReesOfMem I W 0 a _)
    have hxa := (deformationSpaceToBase_app_eq_chartIncl I W a).trans
      (congrArg (chartIncl I 0 W.1) hx)
    have h₁' : W' ≤ ((t ≫ s) ≫ π) ⁻¹ᵁ W.1 := le_rfl
    have h₂' : W' ≤ ((z ≫ κ) ≫ π) ⁻¹ᵁ W.1 := by
      change ((t ≫ s) ≫ π) ⁻¹ᵁ W.1 ≤ ((z ≫ κ) ≫ π) ⁻¹ᵁ W.1
      rw [hb]
    rw [← hxa]
    exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_appLE (t ≫ s) π W.1 W' h₁') a).symm.trans
      ((ConcreteCategory.congr_hom
        (Stacks.AffineAlgebraEquivalence.appLE_congr_hom hb h₁' h₂') a).trans
          (ConcreteCategory.congr_hom (Scheme.Hom.comp_appLE (z ≫ κ) π W.1 W' h₂') a))
  · have hs' : π₀ ⁻¹ᵁ V.1 ≤ s ⁻¹ᵁ K := by
      change (π₀ ≫ i.liftCoborder) ⁻¹ᵁ W.1 ≤ (s ≫ π) ⁻¹ᵁ W.1
      rw [hs]
    have ht' : V.1 ≤ t ⁻¹ᵁ (π₀ ⁻¹ᵁ V.1) := by
      rw [← Scheme.Hom.comp_preimage, deformationZeroSectionBot_toBase, Scheme.Hom.id_preimage]
    have hκ' : (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ W.1 ≤ κ ⁻¹ᵁ K := by
      change (normalConeToBase i ≫ i.liftCoborder) ⁻¹ᵁ W.1 ≤ (κ ≫ π) ⁻¹ᵁ W.1
      rw [hκ]
    have hz' : V.1 ≤ z ⁻¹ᵁ (normalConeToBase i ⁻¹ᵁ V.1) := by
      rw [← Scheme.Hom.comp_preimage, coneSection_toBase, Scheme.Hom.id_preimage]
    have hmap := deformationMap_appLE_chartIncl' i.liftCoborder I ⊥
      (coborderIdeal_comap_liftCoborder i).le W n x hs'
    have htzero := (congrArg (t.appLE _ _ ht').hom hmap).trans
      ((deformationZeroSectionBot_appLE_chartIncl Z V n _ ht').trans
        (extReesBotEvalZero_incl_of_ne Z V.1 n hn _))
    have hzzero := coneSection_comp_normalConeToDeformation_appLE_of_ne i hiso W n hn x hκ' hz'
    exact (comp_appLE_eq_zero_of_appLE_eq_zero t s hs' ht' hV h₁ _ htzero).trans
      (comp_appLE_eq_zero_of_appLE_eq_zero z κ hκ' hz' hV h₂ _ hzzero).symm

end Comparison

variable (p : X ⟶ S) [Smooth p] [Smooth (i ≫ p)]

/-- The zero section of the deformation support is the zero section of the
actual normal bundle followed by its closed fibre map. -/
theorem deformationZeroSectionBot_comp_deformationSupportMap :
    deformationZeroSectionBot Z ≫ deformationSupportMap i =
      Scheme.Modules.vectorBundleZeroSection Z (conormalSheafDegreeOne i) ≫
        normalBundleToDeformation i p := by
  have hq := Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_isRegularImmersion i
    (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_of_smooth i p)
  have hiso := isIso_conormalSymmetricHom_app i hq
  have := isIso_conormalSymmetricAlgebraSheafHom i hiso
  refine (deformationZeroSectionBot_comp_deformationSupportMap_toCone i hiso).trans ?_
  rw [← normalConeIsoNormalBundleOfSmooth_hom_toDeformation i p, ← Category.assoc]
  exact congrArg (fun f => f ≫ normalBundleToDeformation i p) (coneSection_comp_comparison i)

/-- The actual normal-bundle fibre meets the closed deformation support in its zero section. -/
theorem isPullback_normalBundleToDeformation_support :
    IsPullback (Scheme.Modules.vectorBundleZeroSection Z (conormalSheafDegreeOne i))
      (deformationZeroSectionBot Z) (normalBundleToDeformation i p) (deformationSupportMap i) := by
  refine (isPullback_of_isClosedImmersion (deformationZeroSectionBot Z)
    (normalBundleToDeformation i p)
    (Scheme.Modules.vectorBundleZeroSection Z (conormalSheafDegreeOne i))
    (deformationSupportMap i) (deformationZeroSectionBot_comp_deformationSupportMap i p) ?_).flip
  rw [ker_normalBundleToDeformation, deformationSupportMap_comap_zeroScheme,
    ker_deformationZeroSectionBot]

end Stacks.Deformation

end
