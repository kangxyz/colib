/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasquePushforwardComparison
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalDerivedBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatDegreewise
public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.RestrictScalarsPasting

/-! # The literal base change map for the diagonal coefficient resolution

The degreewise base-change mate, followed by the first projection of an
augmentation, is a quasi-isomorphism on flasque representatives. The proof
compares this exact chain map with the canonical derived base change map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPullback derivedPullbackComparison)
open Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.DerivedPullbackTensor
open Stacks.AlgebraicGeometry.FlatSourceBaseChange

namespace AlgebraicGeometry.Scheme

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => CategoryTheory.Limits.pullback π π
local notation "p₁" => CategoryTheory.Limits.pullback.fst π π
local notation "p₂" => CategoryTheory.Limits.pullback.snd π π
local notation "c" => ComplexShape.up ℤ
local notation "πᵣ" => LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom π)
local notation "p₁ᵣ" => LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom p₁)
local notation "p₂ᵣ" => LocallyRingedSpace.Hom.toShHom (Scheme.Hom.toLRSHom p₂)
local notation "BC" =>
  comp_toShHom_of_comm (CommSq.w (IsPullback.toCommSq (projectiveLineDiagonal_isPullback X)))

private theorem diagonalIsFlatToShHom {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Flat f] :
    AlgebraicGeometry.IsFlat f.toLRSHom.toShHom :=
  fun x => Flat.stalkMap f x

/-- The actual base change mate on cochain complexes, induced degreewise by the module mate. -/
def projectiveLineDiagonalBaseChangeCochain :
    (Modules.pushforward π).mapHomologicalComplex c ⋙
        (Modules.pullback π).mapHomologicalComplex c ⟶
      (Modules.pullback p₂).mapHomologicalComplex c ⋙
        (Modules.pushforward p₁).mapHomologicalComplex c :=
  NatTrans.mapHomologicalComplex (moduleBaseChangeSquare p₂ᵣ p₁ᵣ πᵣ πᵣ BC) c

private theorem isIso_middle_of_iso_pasting {C : Type*} [Category* C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (d : D ⟶ E) (r : A ⟶ E)
    (h : a ≫ b ≫ d = r) [IsIso a] [IsIso d] [IsIso r] :
    IsIso b := by
  let : IsIso (a ≫ b ≫ d) := h.symm ▸ (inferInstance : IsIso r)
  let : IsIso (b ≫ d) := IsIso.of_isIso_comp_left a _
  exact IsIso.of_isIso_comp_right b d

set_option maxHeartbeats 1400000 in
-- The canonical pasting compares scheme, ringed-space, and homotopy-category spellings.
/-- The underived mate followed by a pushed augmentation is a quasi-isomorphism
between the literal cochain complexes computing the derived direct images. -/
theorem projectiveLineDiagonalBaseChangeCochain_comp_quasiIso
    (J : CochainComplex (P).Modules ℤ) (J' : CochainComplex (Q).Modules ℤ)
    (hJ : IsPerfectComplex (X := (P).toRingedSpace) J)
    (hbJ : CochainComplex.plus (P).Modules J)
    (hbJ' : CochainComplex.plus (Q).Modules J')
    (hfJ : ∀ n, TopCat.Sheaf.IsFlasque
      ((_root_.SheafOfModules.toSheaf (P).ringCatSheaf).obj (J.X n)))
    (hfJ' : ∀ n, TopCat.Sheaf.IsFlasque
      ((_root_.SheafOfModules.toSheaf (Q).ringCatSheaf).obj (J'.X n)))
    (a : ((Modules.pullback p₂).mapHomologicalComplex c).obj J ⟶ J') [QuasiIso a] :
    QuasiIso ((projectiveLineDiagonalBaseChangeCochain X).app J ≫
      ((Modules.pushforward p₁).mapHomologicalComplex c).map a) := by
  let := isProper_projectiveSpaceOver 1 X
  have : Flat (p₂) := inferInstance
  have : QuasiCompact (p₁) := inferInstance
  have : QuasiSeparated (p₁) := inferInstance
  let hAdd : (modulePushforward p₁ᵣ).Additive := by
    change (Modules.pushforward p₁).Additive
    infer_instance
  let := hAdd
  let U := (HomotopyCategory.quotient (P).Modules c).obj J
  let U' := (HomotopyCategory.quotient (Q).Modules c).obj J'
  let χ := (HomotopyCategory.quotient (Q).Modules c).map a
  let θ := projectiveLineDiagonalBaseChangeCochain X
  let M := θ.app J ≫ ((Modules.pushforward p₁).mapHomologicalComplex c).map a
  let q := HomotopyCategory.quotient (P).Modules c
  have hθ : (underivedBaseChangeSquare p₂ᵣ p₁ᵣ πᵣ πᵣ BC).app U = q.map (θ.app J) :=
    underivedBaseChangeSquare_app_quotient p₂ᵣ p₁ᵣ πᵣ πᵣ BC J
  have hχ : ((modulePushforward p₁ᵣ).mapHomotopyCategory c).map χ =
      q.map (((Modules.pushforward p₁).mapHomologicalComplex c).map a) :=
    rfl
  have hMap :
      (underivedBaseChangeSquare p₂ᵣ p₁ᵣ πᵣ πᵣ BC).app U ≫
        ((modulePushforward p₁ᵣ).mapHomotopyCategory c).map χ = q.map M := by
    rw [hθ]
    erw [hχ]
    exact (q.map_comp (θ.app J) _).symm
  have hc :=
    derivedPullbackComparison_comp_underived_comp_unit p₂ᵣ p₁ᵣ πᵣ πᵣ BC U U' χ
  rw [hMap] at hc
  have hQJ : IsPerfect (X := (P).toRingedSpace) (DerivedCategory.Qh.obj U) :=
    ⟨J, hJ, ⟨((DerivedCategory.quotientCompQhIso (P).Modules).app J).symm⟩⟩
  have hbc : IsIso (derivedBaseChangeMap p₂ᵣ p₁ᵣ πᵣ πᵣ BC (DerivedCategory.Qh.obj U)) :=
    projectiveLineDiagonalDerivedBaseChangeMap_isIso X _ hQJ
  have hπ : IsIso ((derivedPushforwardUnit πᵣ).app U) :=
    Modules.isIso_flasquePushforwardUnit_app π J hbJ hfJ
  have h₁ : IsIso ((derivedPushforwardUnit p₁ᵣ).app U') :=
    Modules.isIso_flasquePushforwardUnit_app p₁ J' hbJ' hfJ'
  have hsrc : IsIso ((derivedPullbackComparison πᵣ).app
      (((modulePushforward πᵣ).mapHomotopyCategory c).obj U)) :=
    isIso_derivedPullbackComparison_app_of_isFlat πᵣ (diagonalIsFlatToShHom π) _
  have h₂ : IsIso ((derivedPullbackComparison p₂ᵣ).app U) :=
    isIso_derivedPullbackComparison_app_of_isFlat p₂ᵣ (diagonalIsFlatToShHom p₂) _
  have hQχ : IsIso (DerivedCategory.Qh.map χ) :=
    (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (Q).Modules) a).2 inferInstance
  let rhs :=
    (derivedPullback πᵣ).map ((derivedPushforwardUnit πᵣ).app U) ≫
      derivedBaseChangeMap p₂ᵣ p₁ᵣ πᵣ πᵣ BC (DerivedCategory.Qh.obj U) ≫
      (derivedPushforward p₁ᵣ).map
        ((derivedPullbackComparison p₂ᵣ).app U ≫ DerivedCategory.Qh.map χ)
  have hrhs : IsIso rhs := by
    dsimp only [rhs]
    let hcomp := IsIso.comp_isIso' h₂ hQχ
    have hleft := @CategoryTheory.Functor.map_isIso _ _ _ _ _ _ (derivedPullback πᵣ) _ hπ
    have hright :=
      @CategoryTheory.Functor.map_isIso _ _ _ _ _ _ (derivedPushforward p₁ᵣ) _ hcomp
    exact IsIso.comp_isIso' hleft (IsIso.comp_isIso' hbc hright)
  let sourceComparison := (derivedPullbackComparison πᵣ).app
    (((modulePushforward πᵣ).mapHomotopyCategory c).obj U)
  have hfinal : IsIso (DerivedCategory.Qh.map (q.map M)) :=
    @isIso_middle_of_iso_pasting _ _ _ _ _ _
      sourceComparison
      (DerivedCategory.Qh.map (q.map M)) ((derivedPushforwardUnit p₁ᵣ).app U') rhs hc
      hsrc h₁ hrhs
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso (P).Modules M).1
    ((NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso (P).Modules) M).1 hfinal)

end AlgebraicGeometry.Scheme
