/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.PowerCutExteriorSupport
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Weighted
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor.Exterior
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor.SupportIso

/-!
# Power cuts commute with the inner exterior identity

The same native torus swaps move the old torus to the last factor.
On its actual support, both power sections are literal pullbacks.
Thus the two full zero-scheme cut cycles commute with the exterior
identity and preserve their signs.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme SmoothSite AffineLineFiber
open AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X T
local notation "F" => parameterProduct T
local notation "ξ" => multiplicativeGroupBaseChangeCoordinate Sₖ

private theorem sectionCut_congr {U V : SmoothSite Sₖ} {A : Scheme.{u}}
    {p₁ p₂ : A ⟶ U.left} {q₁ q₂ : A ⟶ V.left} {s₁ s₂ : Γ(A, ⊤)}
    (hp : p₁ = p₂) (hq : q₁ = q₂) (hs : s₁ = s₂)
    (h₁ : p₁ ≫ U.hom = q₁ ≫ V.hom) (h₂ : p₂ ≫ U.hom = q₂ ≫ V.hom)
    [hf₁ : IsFinite (inclusion (sectionToAffineLine (p₁ ≫ U.hom) s₁) 0 ≫ p₁)]
    [hf₂ : IsFinite (inclusion (sectionToAffineLine (p₂ ≫ U.hom) s₂) 0 ≫ p₂)]
    (g₁ : ∀ z : genericPoints (fiber (sectionToAffineLine (p₁ ≫ U.hom) s₁) 0),
      (inclusion (sectionToAffineLine (p₁ ≫ U.hom) s₁) 0 ≫ p₁) z.val ∈ genericPoints U.left)
    (g₂ : ∀ z : genericPoints (fiber (sectionToAffineLine (p₂ ≫ U.hom) s₂) 0),
      (inclusion (sectionToAffineLine (p₂ ≫ U.hom) s₂) 0 ≫ p₂) z.val ∈ genericPoints U.left) :
    @sectionCutCorrespondence k _ U V A p₁ q₁ h₁ s₁ hf₁ g₁ =
      @sectionCutCorrespondence k _ U V A p₂ q₂ h₂ s₂ hf₂ g₂ := by
  subst p₂
  subst q₂
  subst s₂
  rfl

variable (X Y : SmoothSite (Spec (.of k)))
  (w : pullback (C := Scheme)
    (product X (multiplicativeGroupObject (Spec (.of k)))).hom
    (product Y (multiplicativeGroupObject (Spec (.of k)))).hom)
  (hw : IsFiniteCorrespondencePoint
    (product X (multiplicativeGroupObject (Spec (.of k)))).hom
    (product Y (multiplicativeGroupObject (Spec (.of k)))).hom w)

local notation3 (prettyPrint := false) "w'" => torusInnerExtensionPrimePoint k X Y w hw
local notation3 (prettyPrint := false) "P" => (integralComponentAt w).subscheme
local notation3 (prettyPrint := false) "P'" => (integralComponentAt w').subscheme
local notation3 (prettyPrint := false) "p₀" => torusPowerCutSource k X Y w
local notation3 (prettyPrint := false) "q₀" => torusPowerCutTarget k X Y w
local notation3 (prettyPrint := false) "p₀'" => torusPowerCutSource k (G(X)) (G(Y)) w'
local notation3 (prettyPrint := false) "q₀'" => torusPowerCutTarget k (G(X)) (G(Y)) w'
local notation3 (prettyPrint := false) "p" => torusSupportBaseProjection k (X := X) p₀
local notation3 (prettyPrint := false) "q" => torusSupportBaseProjection k (X := Y) q₀
local notation3 (prettyPrint := false) "p'" => torusSupportBaseProjection k (X := G(X)) p₀'
local notation3 (prettyPrint := false) "q'" => torusSupportBaseProjection k (X := G(Y)) q₀'
local notation3 (prettyPrint := false) "e" => torusInnerExtensionSupportIso k X Y w hw
local notation3 (prettyPrint := false) "π" => pullback.fst (p ≫ X.hom) (T).hom
local notation3 (prettyPrint := false) "D₀" => pullback (p ≫ X.hom) (T).hom

set_option maxHeartbeats 800000 in
-- Both pulled section cuts retain the actual source and target maps of the exterior support.
private theorem innerSectionCut_eq_exterior
    (s : Γ(P, ⊤)) (s' : Γ(P', ⊤)) (he : (e).hom.appTop s' = (π).appTop s)
    (h : p ≫ X.hom = q ≫ Y.hom) (h' : p' ≫ (G(X)).hom = q' ≫ (G(Y)).hom)
    [hf : IsFinite (inclusion (sectionToAffineLine (p ≫ X.hom) s) 0 ≫ p)]
    [hf' : IsFinite (inclusion (sectionToAffineLine (p' ≫ (G(X)).hom) s') 0 ≫ p')]
    (hgen : ∀ z : genericPoints (fiber (sectionToAffineLine (p ≫ X.hom) s) 0),
      (inclusion (sectionToAffineLine (p ≫ X.hom) s) 0 ≫ p) z.val ∈ genericPoints X.left)
    (hgen' : ∀ z : genericPoints (fiber (sectionToAffineLine (p' ≫ (G(X)).hom) s') 0),
      (inclusion (sectionToAffineLine (p' ≫ (G(X)).hom) s') 0 ≫ p') z.val ∈
        genericPoints (G(X)).left) :
    @sectionCutCorrespondence k _ (G(X)) (G(Y)) P' p' q' h' s' hf' hgen' =
      nativeExterior X Y T (@sectionCutCorrespondence k _ X Y P p q h s hf hgen) := by
  let j := (integralComponentAt w).subschemeι
  let : IsNoetherian (pullback (C := Scheme) (G(X)).hom (G(Y)).hom) :=
    SmoothSite.isNoetherian_overField k (product (G(X)) (G(Y)))
  let : IsNoetherian P := isNoetherian_of_finiteType_of_isNoetherian j
  let pT : D₀ ⟶ (G(X)).left := pullbackParameterExtensionMap p X.hom (T).hom
  let qT : D₀ ⟶ (G(Y)).left := sectionCutExteriorTarget T p q h
  let p'₀ : D₀ ⟶ (G(X)).left := (e).hom ≫ p'
  let q'₀ : D₀ ⟶ (G(Y)).left := (e).hom ≫ q'
  let s'₀ : Γ(D₀, ⊤) := (e).hom.appTop s'
  let sT : Γ(D₀, ⊤) := (π).appTop s
  have hproj := torusInnerExtensionSupportIso_cut_projections k X Y w hw h
  have hp : p'₀ = pT := hproj.1
  have hq : q'₀ = qT := hproj.2
  have hsec : s'₀ = sT := he
  let i := inclusion (sectionToAffineLine (p'₀ ≫ (G(X)).hom) s'₀) 0
  let iT := inclusion (sectionToAffineLine (pT ≫ (G(X)).hom) sT) 0
  let hf₁ : IsFinite (i ≫ p'₀) :=
    (isFinite_sectionCut_supportIso_iff (X := G(X)) e s' p').mpr hf'
  let : IsFinite (i ≫ p'₀) := hf₁
  have hg : ∀ z : genericPoints (fiber (sectionToAffineLine (p'₀ ≫ (G(X)).hom) s'₀) 0),
      (i ≫ p'₀) z.val ∈ genericPoints (G(X)).left :=
    (sectionCut_generic_supportIso_iff (X := G(X)) e s' p').mpr hgen'
  let hf₂ : IsFinite (iT ≫ pT) := by
    dsimp only [iT]
    rw [← hp, ← hsec]
    exact hf₁
  let : IsFinite (iT ≫ pT) := hf₂
  have hgT : ∀ z : genericPoints (fiber (sectionToAffineLine (pT ≫ (G(X)).hom) sT) 0),
      (iT ≫ pT) z.val ∈ genericPoints (G(X)).left := by
    dsimp only [iT]
    rw [← hp, ← hsec]
    exact hg
  have h₁ : p'₀ ≫ (G(X)).hom = q'₀ ≫ (G(Y)).hom :=
    (Category.assoc _ _ _).trans ((congrArg ((e).hom ≫ ·) h').trans (Category.assoc _ _ _).symm)
  have h₂ : pT ≫ (G(X)).hom = qT ≫ (G(Y)).hom := sectionCutExterior_base T p q h
  calc
    _ = @sectionCutCorrespondence k _ (G(X)) (G(Y)) D₀ p'₀ q'₀ h₁ s'₀ hf₁ hg :=
      (sectionCutCorrespondence_supportIso (X := G(X)) (Y := G(Y)) e s' p' q' h' hgen' hg).symm
    _ = @sectionCutCorrespondence k _ (G(X)) (G(Y)) D₀ pT qT h₂ sT hf₂ hgT :=
      sectionCut_congr k hp hq hsec h₁ h₂ hg hgT
    _ = _ := sectionCutCorrespondence_exterior T p q h s hgen hgT

set_option maxHeartbeats 800000 in
-- Both polynomial expressions use the pulled section on the actual permuted support.
/-- Each actual inner exterior prime cut is the exterior identity of the
original cut, with the two original signs. -/
theorem torusPowerCutPrime_innerExtension
    (n : ℕ) (ha : TorusPowerCutAdmissibleAt k X Y w n)
    (ha' : TorusPowerCutAdmissibleAt k (G(X)) (G(Y)) w' n) :
    torusPowerCutPrime k (G(X)) (G(Y)) w' n ha' =
      (F).map (torusPowerCutPrime k X Y w n ha) := by
  obtain ⟨ht₁, ht₂⟩ := torusInnerExtensionSupportIso_torus_projections k X Y w hw
  let t₁ : (Γ(P, ⊤))ˣ := torusSupportCoordinate k (X := X) p₀
  let t₂ : (Γ(P, ⊤))ˣ := torusSupportCoordinate k (X := Y) q₀
  let t₁' : (Γ(P', ⊤))ˣ := torusSupportCoordinate k (X := G(X)) p₀'
  let t₂' : (Γ(P', ⊤))ˣ := torusSupportCoordinate k (X := G(Y)) q₀'
  let ev (m : D₀ ⟶ (T).left) : Γ(D₀, ⊤) := m.appTop (ξ).val
  have h₁ : (e).hom.appTop t₁'.val = (π).appTop t₁.val := by
    change (e).hom.appTop ((p₀' ≫ pullback.snd (G(X)).hom (T).hom).appTop (ξ).val) =
      (π).appTop ((p₀ ≫ pullback.snd X.hom (T).hom).appTop (ξ).val)
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    exact congrArg ev ht₁
  have h₂ : (e).hom.appTop t₂'.val = (π).appTop t₂.val := by
    change (e).hom.appTop ((q₀' ≫ pullback.snd (G(Y)).hom (T).hom).appTop (ξ).val) =
      (π).appTop ((q₀ ≫ pullback.snd Y.hom (T).hom).appTop (ξ).val)
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
    exact congrArg ev ht₂
  let s := torusPowerCutNumerator t₁ n
  let t := torusPowerCutDenominator t₁ t₂ n
  let s' := torusPowerCutNumerator t₁' n
  let t' := torusPowerCutDenominator t₁' t₂' n
  have hs : (e).hom.appTop s' = (π).appTop s := by
    simp only [s, s', torusPowerCutNumerator, map_sub, map_pow, map_one, h₁]
  have ht : (e).hom.appTop t' = (π).appTop t := by
    simp only [t, t', torusPowerCutDenominator, map_sub, map_pow, h₁, h₂]
  have h : p ≫ X.hom = q ≫ Y.hom := by
    have hs := exteriorSupport_projection_base (G(X)) (G(Y)) (integralComponentAt w)
    have hfst : (productFst X T).left ≫ X.hom = (G(X)).hom :=
      MorphismProperty.Over.w (productFst X T)
    have hsnd : (productFst Y T).left ≫ Y.hom = (G(Y)).hom :=
      MorphismProperty.Over.w (productFst Y T)
    change (p₀ ≫ (productFst X T).left) ≫ X.hom =
      (q₀ ≫ (productFst Y T).left) ≫ Y.hom
    calc
      _ = p₀ ≫ ((productFst X T).left ≫ X.hom) := Category.assoc _ _ _
      _ = p₀ ≫ (G(X)).hom := congrArg (p₀ ≫ ·) hfst
      _ = q₀ ≫ (G(Y)).hom := hs
      _ = q₀ ≫ ((productFst Y T).left ≫ Y.hom) := congrArg (q₀ ≫ ·) hsnd.symm
      _ = _ := (Category.assoc _ _ _).symm
  have h' : p' ≫ (G(X)).hom = q' ≫ (G(Y)).hom := by
    have hs := exteriorSupport_projection_base (G(G(X))) (G(G(Y))) (integralComponentAt w')
    have hfst : (productFst (G(X)) T).left ≫ (G(X)).hom = (G(G(X))).hom :=
      MorphismProperty.Over.w (productFst (G(X)) T)
    have hsnd : (productFst (G(Y)) T).left ≫ (G(Y)).hom = (G(G(Y))).hom :=
      MorphismProperty.Over.w (productFst (G(Y)) T)
    change (p₀' ≫ (productFst (G(X)) T).left) ≫ (G(X)).hom =
      (q₀' ≫ (productFst (G(Y)) T).left) ≫ (G(Y)).hom
    calc
      _ = p₀' ≫ ((productFst (G(X)) T).left ≫ (G(X)).hom) := Category.assoc _ _ _
      _ = p₀' ≫ (G(G(X))).hom := congrArg (p₀' ≫ ·) hfst
      _ = q₀' ≫ (G(G(Y))).hom := hs
      _ = q₀' ≫ ((productFst (G(Y)) T).left ≫ (G(Y)).hom) := congrArg (q₀' ≫ ·) hsnd.symm
      _ = _ := (Category.assoc _ _ _).symm
  let : IsFinite (inclusion (sectionToAffineLine (p ≫ X.hom) s) 0 ≫ p) := ha.numerator_finite
  let : IsFinite (inclusion (sectionToAffineLine (p ≫ X.hom) t) 0 ≫ p) := ha.denominator_finite
  let : IsFinite (inclusion (sectionToAffineLine (p' ≫ (G(X)).hom) s') 0 ≫ p') :=
    ha'.numerator_finite
  let : IsFinite (inclusion (sectionToAffineLine (p' ≫ (G(X)).hom) t') 0 ≫ p') :=
    ha'.denominator_finite
  change sectionCutCorrespondence p' q' h' s' ha'.numerator_generic -
      sectionCutCorrespondence p' q' h' t' ha'.denominator_generic =
    nativeExterior X Y T (sectionCutCorrespondence p q h s ha.numerator_generic -
      sectionCutCorrespondence p q h t ha.denominator_generic)
  rw [innerSectionCut_eq_exterior k X Y w hw s s' hs h h' ha.numerator_generic
      ha'.numerator_generic,
    innerSectionCut_eq_exterior k X Y w hw t t' ht h h' ha.denominator_generic
      ha'.denominator_generic, map_sub]

end AlgebraicGeometry.PresheafWithTransfers
