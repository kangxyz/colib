/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.Gysin.OpenNaturality.BundleChart
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.DeformationBaseChange
import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom
import StacksFrontier.AlgebraicGeometry.ProjTwistCompTwistMap.Generic

/-! # Degree-one coordinates of the actual deformation fibre map -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme Opposite
open Stacks.Conormal Stacks.Deformation Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.ProjTwistCompTwistMap
open Stacks.AlgebraicGeometry.PullbackUnit

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable {Z X Z' X' S : Scheme.{u}} {i : Z ⟶ X} {j : Z' ⟶ X'}
  [IsClosedImmersion i] [IsClosedImmersion j] {f : X ⟶ X'} {g : Z ⟶ Z'}
  (h : IsPullback i g f j)

local notation "F₀" => conormalSheafDegreeOne i
local notation "F₁" => conormalSheafDegreeOne j
local notation "N" => Modules.vectorBundleOver Z (F := F₀)
local notation "N'" => Modules.vectorBundleOver Z' (F := F₁)
local notation "θ" => canonicalPullbackHomOne i j g f h.w.symm

/-- The canonical map on degree-one conormal sections over the full preimage. -/
abbrev conormalSectionBaseChange (V : Z'.Opens) : Γ(F₁, V) →+ Γ(F₀, g ⁻¹ᵁ V) :=
  conormalHomSection i j g (conormalAlgebraHom i j g f h.w.symm).hom 1 _ V le_rfl

private def conormalBundleMapOver : (Over.map g).obj N ⟶ N' :=
  let := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g F₁
  (Over.map g).map (Modules.vectorBundleMap Z (θ)) ≫ Modules.vectorBundleBaseChangeOver g F₁

section Fibre

variable (p : X ⟶ S) (p' : X' ⟶ S)
  [Smooth p] [Smooth p'] [Smooth (i ≫ p)] [Smooth (j ≫ p')]

set_option maxHeartbeats 700000 in
-- Compare both maps after the native normal-cone and deformation inclusions.
/-- The map on the parameter-zero fibre is the map of vector bundles furnished
by the canonical conormal morphism of the square. -/
private theorem deformationNormalFibreMap_eq_conormalBundleMapOver :
    deformationNormalFibreMap h p' p = (conormalBundleMapOver h).left := by
  let e := normalConeIsoNormalBundleOfSmooth i p
  let e' := normalConeIsoNormalBundleOfSmooth j p'
  let a := normalConeMapOfSquare i j g f h.w.symm
  let m := deformationMapOver h
  let b := deformationNormalFibreMap h p' p
  let c := (conormalBundleMapOver h).left
  have hn : normalBundleToDeformation i p ≫ m = b ≫ normalBundleToDeformation j p' :=
    (isPullback_deformationNormalFibreMap h p' p).w
  have hd : normalConeToDeformation i ≫ m = a ≫ normalConeToDeformation j :=
    normalConeToDeformation_comp_deformationMap i j g f h.w.symm
      (coborderMapOver j i f) (coborderMapOver_ι j i f) (coborderIdeal_baseChange h).le
  have he : e.hom ≫ normalBundleToDeformation i p = normalConeToDeformation i :=
    normalConeIsoNormalBundleOfSmooth_hom_toDeformation i p
  have he' : e'.hom ≫ normalBundleToDeformation j p' = normalConeToDeformation j :=
    normalConeIsoNormalBundleOfSmooth_hom_toDeformation j p'
  let := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g F₁
  have hc : a ≫ e'.hom = e.hom ≫ c := by
    change a ≫ (normalConeIsoNormalBundleOfSmooth j p').hom =
      (normalConeIsoNormalBundleOfSmooth i p).hom ≫ (conormalBundleMapOver h).left
    rw [normalConeIsoNormalBundleOfSmooth_hom, normalConeIsoNormalBundleOfSmooth_hom]
    have hmap : (conormalBundleMapOver h).left =
        (Modules.vectorBundleMap Z (θ)).left ≫ Modules.vectorBundleBaseChangeMap g F₁ := by
      change (Modules.vectorBundleMap Z (θ)).left ≫
        (Modules.vectorBundleBaseChangeOver g F₁).left = _
      exact congrArg ((Modules.vectorBundleMap Z (θ)).left ≫ ·)
        (Modules.vectorBundleBaseChangeMap_eq g F₁).symm
    rw [hmap]
    exact normalConeMapOfSquare_comp_normalConeToNormalBundle i j g f h.w.symm
  apply (cancel_epi e.hom).1
  apply (cancel_mono (normalBundleToDeformation j p')).1
  change (e.hom ≫ b) ≫ normalBundleToDeformation j p' =
    (e.hom ≫ c) ≫ normalBundleToDeformation j p'
  calc
    _ = e.hom ≫ (b ≫ normalBundleToDeformation j p') := Category.assoc _ _ _
    _ = e.hom ≫ (normalBundleToDeformation i p ≫ m) := congrArg (e.hom ≫ ·) hn.symm
    _ = normalConeToDeformation i ≫ m :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ m) he)
    _ = (a ≫ e'.hom) ≫ normalBundleToDeformation j p' :=
      hd.trans ((congrArg (a ≫ ·) he'.symm).trans (Category.assoc _ _ _).symm)
    _ = _ := congrArg (· ≫ normalBundleToDeformation j p') hc

/-- The original normal-fibre map commutes with the two bundle projections. -/
theorem deformationNormalFibreMap_toBase :
    deformationNormalFibreMap h p' p ≫ normalBundleToBase j = normalBundleToBase i ≫ g := by
  rw [deformationNormalFibreMap_eq_conormalBundleMapOver h p p']
  exact Over.w (conormalBundleMapOver h)

/-- Evaluation of the conormal map on linear functions, using the original opens of
the normal fibres. -/
theorem deformationNormalFibreMap_appLE_linearFunction (V : Z'.Opens) (a : Γ(F₁, V))
    (hV : (N).hom ⁻¹ᵁ (g ⁻¹ᵁ V) ≤
      (deformationNormalFibreMap h p' p) ⁻¹ᵁ ((N').hom ⁻¹ᵁ V)) :
    (deformationNormalFibreMap h p' p).appLE ((N').hom ⁻¹ᵁ V)
        ((N).hom ⁻¹ᵁ (g ⁻¹ᵁ V)) hV (Modules.vectorBundleLinearFunction F₁ V a) =
      Modules.vectorBundleLinearFunction F₀ (g ⁻¹ᵁ V) (conormalSectionBaseChange h V a) := by
  let v := conormalBundleMapOver h
  let A := (Over.map g).obj N
  let θ₁ := Modules.vectorBundleHomEquiv F₀ N (𝟙 N)
  let θ₂ := canonicalPushforwardHom i j g f h.w.symm 1
  let := Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g F₁
  have ht : Modules.vectorBundleHomEquiv F₁ A v =
      Modules.transposeEquiv g F₁ N ((θ) ≫ θ₁) := by
    change Modules.vectorBundleHomEquiv F₁ A ((Over.map g).map (Modules.vectorBundleMap Z (θ)) ≫
      Modules.vectorBundleBaseChangeOver g F₁) = _
    rw [Modules.vectorBundleHomEquiv_map_comp_vectorBundleBaseChangeOver]
    have hw := Modules.vectorBundleHomEquiv_comp_vectorBundleMap (θ) N (𝟙 N)
    rw [Category.id_comp] at hw
    rw [hw]
  have hφ : (Modules.pullbackPushforwardAdjunction g).homEquiv _ _ (θ) = θ₂ :=
    Equiv.apply_symm_apply _ _
  have hv : Modules.vectorBundleHomEquiv F₁ A v =
      (θ₂ ≫ (Modules.pushforward g).map θ₁) ≫
        ((Modules.pushforwardComp (N).hom g).app _).hom := by
    rw [ht, Modules.transposeEquiv_apply, Adjunction.homEquiv_naturality_right, hφ]
  have hsec₀ := congrArg (fun e : F₁ ⟶ Modules.structurePushforward A.hom =>
    (e.val.app (op V)).hom a) hv
  have hsec₁ := Modules.comp_pushforwardComp_hom_val_app_apply (N).hom g
    (SheafOfModules.unit (N).left.ringCatSheaf) (θ₂ ≫ (Modules.pushforward g).map θ₁) (op V) a
  have hsec₂ := Modules.comp_val_app_apply θ₂ ((Modules.pushforward g).map θ₁) (op V) a
  have hsec₃ := Modules.pushforward_map_val_app_apply g θ₁ V ((θ₂.val.app (op V)).hom a)
  have hsec₄ := congrArg (fun r => (θ₁.val.app (op (g ⁻¹ᵁ V))).hom r)
    (canonicalPushforwardHom_val_app_apply i j g f h.w.symm 1 V a)
  have hsec := hsec₀.trans (hsec₁.trans (hsec₂.trans (hsec₃.trans hsec₄)))
  have hcomp := Modules.vectorBundleHomEquiv_appLE_linearFunction F₁ v V a
    (preimage_le_preimage_preimage v V)
  have hh := appLE_congr_hom
    (deformationNormalFibreMap_eq_conormalBundleMapOver h p p').symm
    (preimage_le_preimage_preimage v V) hV
  exact (ConcreteCategory.congr_hom hh _).symm.trans (hcomp.symm.trans hsec)

/-- The inverse image of a chart of the target normal bundle lies over the
corresponding inverse image of its base. -/
theorem preimage_normalBundleToBase_le_deformationNormalFibreMap (V : Z'.Opens) :
    normalBundleToBase i ⁻¹ᵁ (g ⁻¹ᵁ V) ≤
      (deformationNormalFibreMap h p' p) ⁻¹ᵁ (normalBundleToBase j ⁻¹ᵁ V) := by
  exact ((Scheme.Hom.comp_preimage (normalBundleToBase i) g V).symm.trans
    ((congrArg (fun m => m ⁻¹ᵁ V) (deformationNormalFibreMap_toBase h p p').symm).trans
      (Scheme.Hom.comp_preimage (deformationNormalFibreMap h p' p) (normalBundleToBase j) V))).le

set_option maxHeartbeats 750000 in
-- Compare the native maps on the base and on each degree-one generator.
/-- Charts whose frames are related by conormal base change identify the original
normal-fibre map with the ordinary map of affine spaces in the base variable. -/
theorem vectorBundleBasisChart_deformationNormalFibreMap
    (V : Z'.affineOpens) (hW : IsAffineOpen (g ⁻¹ᵁ V.1))
    {c : ℕ} (b : Module.Basis (Fin c) Γ(Z', V.1) Γ(F₁, V.1))
    (b' : Module.Basis (Fin c) Γ(Z, g ⁻¹ᵁ V.1) Γ(F₀, g ⁻¹ᵁ V.1))
    (hb : ∀ r, b' r = conormalSectionBaseChange h V.1 (b r)) :
    let W : Z.affineOpens := ⟨g ⁻¹ᵁ V.1, hW⟩
    let v := deformationNormalFibreMap h p' p
    v.resLE (normalBundleToBase j ⁻¹ᵁ V.1) (normalBundleToBase i ⁻¹ᵁ W.1)
        (preimage_normalBundleToBase_le_deformationNormalFibreMap h p p' V.1) ≫
      (Modules.vectorBundleBasisChart F₁ V b).hom =
    (Modules.vectorBundleBasisChart F₀ W b').hom ≫
      AffineSpace.map (ULift.{u} (Fin c)) (g ∣_ V.1) := by
  intro W v
  let B := normalBundleToBase i ⁻¹ᵁ W.1
  let C := normalBundleToBase j ⁻¹ᵁ V.1
  let hle := preimage_normalBundleToBase_le_deformationNormalFibreMap h p p' V.1
  let a := v.resLE C B hle
  let e := Modules.vectorBundleBasisChart F₀ W b'
  let e' := Modules.vectorBundleBasisChart F₁ V b
  change a ≫ e'.hom = e.hom ≫ AffineSpace.map (ULift.{u} (Fin c)) (g ∣_ V.1)
  apply AffineSpace.hom_ext
  · simp only [Category.assoc, e, e', Modules.vectorBundleBasisChart_hom_over,
      AffineSpace.map_over, Modules.vectorBundleBasisChart_hom_over_assoc]
    apply (cancel_mono V.1.ι).1
    dsimp only [a]
    have hL : ((v.resLE C B hle) ≫ (normalBundleToBase j ∣_ V.1)) ≫ V.1.ι =
        B.ι ≫ normalBundleToBase i ≫ g := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.Hom.resLE_comp_ι,
        Category.assoc, deformationNormalFibreMap_toBase h p p']
    have hR : ((normalBundleToBase i ∣_ W.1) ≫ (g ∣_ V.1)) ≫ V.1.ι =
        B.ι ≫ normalBundleToBase i ≫ g := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι, Category.assoc]
    exact hL.trans hR.symm
  · intro r
    simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.map_appTop_coord, e, e']
    have h' := Modules.vectorBundleBasisChart_appTop_coord F₁ V b r
    have h₀ := Modules.vectorBundleBasisChart_appTop_coord F₀ W b' r
    refine (congrArg (fun t => a.appTop t) h').trans (Eq.trans ?_ h₀.symm)
    let y := Modules.vectorBundleLinearFunction F₁ V.1 (b r.down)
    have hy : C.topIso.hom (C.topIso.inv y) = y :=
      ConcreteCategory.congr_hom C.topIso.inv_hom_id y
    change (v.resLE C B hle).app ⊤ (C.topIso.inv y) =
      B.topIso.inv (Modules.vectorBundleLinearFunction F₀ W.1 (b' r.down))
    have ha : (v.resLE C B hle).app ⊤ = C.topIso.hom ≫ v.appLE C B hle ≫ B.topIso.inv :=
      Scheme.Hom.resLE_app_top v hle
    have ha' := ConcreteCategory.congr_hom ha (C.topIso.inv y)
    have hg : v.appLE C B hle y = Modules.vectorBundleLinearFunction F₀ W.1 (b' r.down) :=
      (deformationNormalFibreMap_appLE_linearFunction h p p' V.1 (b r.down) hle).trans
        (congrArg (Modules.vectorBundleLinearFunction F₀ W.1) (hb r.down).symm)
    change _ = B.topIso.inv (v.appLE C B hle (C.topIso.hom (C.topIso.inv y))) at ha'
    exact ha'.trans ((congrArg (fun t => B.topIso.inv (v.appLE C B hle t)) hy).trans
      (congrArg (fun t => B.topIso.inv t) hg))

end Fibre

section Frame

variable [Flat f] [IsOpenImmersion g]

omit [Flat f] [IsOpenImmersion g] in
private theorem conormalSectionBaseChange_eq_pullback (V : Z'.Opens) (a : Γ(F₁, V)) :
    conormalSectionBaseChange h V a =
      ((θ).val.app (op (g ⁻¹ᵁ V))) (pullbackSectionOn g F₁ V a) := by
  have hv := (canonicalPullbackHom i j g f h.w.symm).agrees 1 V a
  change (((Modules.pullbackPushforwardAdjunction g).homEquiv _ _ (θ)).val.app (op V)) a =
    conormalSectionBaseChange h V a at hv
  rw [Adjunction.homEquiv_unit, Modules.comp_val_app_apply] at hv
  exact hv.symm.trans (Modules.pushforward_map_val_app_apply g (θ) V (pullbackSectionOn g F₁ V a))

private theorem bijective_conormalSectionBaseChange (V : Z'.Opens) (hV : V ≤ g.opensRange) :
    Function.Bijective (conormalSectionBaseChange h V) := by
  let W := g ⁻¹ᵁ V
  have he : g ''ᵁ W = V :=
    (g.image_preimage_eq_opensRange_inf V).trans (inf_eq_right.mpr hV)
  let P := Modules.presheaf (F₁ : Z'.Modules)
  let e := P.mapIso (eqToIso he).op
  let : IsIso (θ) := conormalAlgebraMap_isIso_of_flat i j g f h 1
  let c := (Modules.restrictFunctorIsoPullback g).app F₁ ≪≫ asIso (θ)
  let ψ := (SheafOfModules.evaluation Z.ringCatSheaf (op W)).mapIso c
  have hunit (a : Γ(F₁, V)) :
      ((Modules.restrictAdjunction g).unit.app F₁).val.app (op V) a = e.hom a := by
    change P.map (homOfLE (g.image_preimage_le V)).op a = _
    have hw : homOfLE (g.image_preimage_le V) = (eqToIso he).hom := Subsingleton.elim _ _
    exact congrArg (fun f => P.map f.op a) hw
  have hsec (a : Γ(F₁, V)) : conormalSectionBaseChange h V a = ψ.hom (e.hom a) := by
    refine (conormalSectionBaseChange_eq_pullback h V a).trans ?_
    refine (congrArg (fun r => ((θ).val.app (op W)) r)
      (pullbackSectionOn_eq_restrictIso g F₁ V a)).trans ?_
    exact congrArg (fun r => ψ.hom r) (hunit a)
  have hbij₀ : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  have hbij₁ : Function.Bijective ψ.hom := ConcreteCategory.bijective_of_isIso ψ.hom
  exact (show (conormalSectionBaseChange h V : Γ(F₁, V) → Γ(F₀, W)) = ψ.hom ∘ e.hom from
    funext hsec).symm ▸ hbij₁.comp hbij₀

/-- A basis over an affine open contained in the image of the centre immersion
pulls back to a basis of the native conormal module on its preimage. -/
theorem exists_conormalBasisBaseChange_open (V : Z'.Opens) (hV : V ≤ g.opensRange)
    {c : ℕ} (b : Module.Basis (Fin c) Γ(Z', V) Γ(F₁, V)) :
    ∃ b' : Module.Basis (Fin c) Γ(Z, g ⁻¹ᵁ V) Γ(F₀, g ⁻¹ᵁ V),
      ∀ r, b' r = conormalSectionBaseChange h V (b r) := by
  let : IsIso (g.app V) := g.isIso_app V hV
  let e := (asIso (g.app V)).commRingCatIsoToRingEquiv
  let R := Γ(Z, g ⁻¹ᵁ V)
  let M := Γ(F₁, V)
  let : Module R M := Module.compHom M e.symm.toRingHom
  have hs (r : Γ(Z', V)) (a : M) : e r • a = r • a := by
    change e.symm (e r) • a = r • a
    rw [e.symm_apply_apply]
  let b₀ := b.mapCoeffs e hs
  let σ : M →ₗ[R] Γ(F₀, g ⁻¹ᵁ V) :=
    { conormalSectionBaseChange h V with
      map_smul' := fun r a => by
        change conormalSectionBaseChange h V (e.symm r • a) =
          r • conormalSectionBaseChange h V a
        have hh := conormalHomSection_smul i j g (conormalAlgebraHom i j g f h.w.symm).hom
          1 (g ⁻¹ᵁ V) V le_rfl (e.symm r) a
        have hr : (g.app V).hom (e.symm r) = r := e.apply_symm_apply r
        apply hh.trans
        have hidr : (homOfLE (le_rfl : g ⁻¹ᵁ V ≤ g ⁻¹ᵁ V)).op = 𝟙 _ :=
          Subsingleton.elim _ _
        have hid := (Z.presheaf.congr_map hidr).trans (Z.presheaf.map_id _)
        exact congrArg (fun a₀ => a₀ • conormalSectionBaseChange h V a)
          ((ConcreteCategory.congr_hom hid _).trans hr) }
  let e₁ := LinearEquiv.ofBijective σ (bijective_conormalSectionBaseChange h V hV)
  refine ⟨b₀.map e₁, fun r => ?_⟩
  change e₁ (b₀ r) = e₁ (b r)
  exact congrArg (fun a => e₁ a) (b.mapCoeffs_apply e hs r)


end Frame

end AlgebraicGeometry.MotivicHomotopy
