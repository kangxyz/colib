/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.UnitCut
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.WeightedGraph
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCut.Weighted
import Colib.AlgebraicGeometry.Correspondences.Additive.Ext

/-!
# The two power cuts as the difference of unit graph operations

The numerator and denominator are actual unit precompositions of their
retained parameter graphs. The native cut on signed correspondences is
their difference with the original prime coefficients.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction AffineLineFiber

variable (k : Type u) [Field k] (X Y : SmoothSite (Spec (.of k)))

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X T
local notation "V(" Y ")" => torusPowerCutRetainedTarget k Y
set_option quotPrecheck false in
local notation "g" => (G(X)).hom
set_option quotPrecheck false in
local notation "h" => (G(Y)).hom
set_option quotPrecheck false in
local notation "h'" => (V(Y)).hom

/-- The unit precomposition and projection on the actual retained graph. -/
def torusPowerParameterUnitCut : finiteCorrespondences g h' →+
    (Cor.mk X ⟶ Cor.mk Y) :=
  (Preadditive.rightComp (Cor.mk X) ((graphFunctor k).map (torusPowerParameterForget k Y))).comp
    (Preadditive.leftComp (Cor.mk (V(Y))) ((graphFunctor k).map (unitSection.app X)))

theorem torusPowerParameterUnitCut_apply (a : finiteCorrespondences g h') :
    torusPowerParameterUnitCut k X Y a =
      (graphFunctor k).map (unitSection.app X) ≫ a ≫
        (graphFunctor k).map (torusPowerParameterForget k Y) := by
  change ((graphFunctor k).map (unitSection.app X) ≫ a) ≫
    (graphFunctor k).map (torusPowerParameterForget k Y) = _
  rw [Category.assoc]

/-- The original forward unit on the old target torus product. -/
def torusPowerParameterTargetUnit : (Γ((G(Y)).left, ⊤))ˣ :=
  Units.map (productSnd Y T).left.appTop.hom.toMonoidHom
    (multiplicativeGroupBaseChangeCoordinate Sₖ)

local notation "uᵧ" => torusPowerParameterTargetUnit k Y

variable (w : pullback (C := Scheme)
    (product X (multiplicativeGroupObject (Spec (.of k)))).hom
    (product Y (multiplicativeGroupObject (Spec (.of k)))).hom)
  (n : ℕ)

set_option quotPrecheck false in
local notation "P" => (integralComponentAt w).subscheme
set_option quotPrecheck false in
local notation "j" => (integralComponentAt w).subschemeι
local notation "t₁" => torusSupportCoordinate k (X := X) (j ≫ pullback.fst g h)
local notation "t₂" => torusSupportCoordinate k (X := Y) (j ≫ pullback.snd g h)
local notation "p" => torusSupportBaseProjection k (X := X) (j ≫ pullback.fst g h)
local notation "q" => torusSupportBaseProjection k (X := Y) (j ≫ pullback.snd g h)
local notation "N" => torusPowerCutNumerator t₁ n
local notation "D" => torusPowerCutDenominator t₁ t₂ n
local notation "J₁" => torusPowerParameterAmbientGraph k (X := X) (Y := Y) (n + 1) 1
local notation "J₂" => torusPowerParameterAmbientGraph k (X := X) (Y := Y) (n + 1) uᵧ

private theorem torusPowerParameterTargetUnit_pullback :
    Units.map ((j ≫ pullback.snd g h).appTop.hom.toMonoidHom) uᵧ = t₂ := by
  let f := j ≫ pullback.snd g h
  let e := (productSnd Y T).left
  let t := (multiplicativeGroupBaseChangeCoordinate Sₖ).val
  apply Units.ext
  change f.appTop (e.appTop t) = (f ≫ e).appTop t
  exact ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop f e).symm t

private theorem cut_section_congr {P' : Scheme.{u}} (p' : P' ⟶ X.left) (q' : P' ⟶ Y.left)
    (hp : p' ≫ X.hom = q' ≫ Y.hom) {s t : Γ(P', ⊤)} (hst : s = t)
    [IsFinite (inclusion (sectionToAffineLine (p' ≫ X.hom) s) 0 ≫ p')]
    [IsFinite (inclusion (sectionToAffineLine (p' ≫ X.hom) t) 0 ≫ p')]
    (hs : ∀ z : genericPoints (fiber (sectionToAffineLine (p' ≫ X.hom) s) 0),
      (inclusion (sectionToAffineLine (p' ≫ X.hom) s) 0 ≫ p') z.val ∈ genericPoints X.left)
    (ht : ∀ z : genericPoints (fiber (sectionToAffineLine (p' ≫ X.hom) t) 0),
      (inclusion (sectionToAffineLine (p' ≫ X.hom) t) 0 ≫ p') z.val ∈ genericPoints X.left) :
    sectionCutCorrespondence (X := X) (Y := Y) («P» := P') p' q' hp s hs =
      sectionCutCorrespondence (X := X) (Y := Y) («P» := P') p' q' hp t ht := by
  subst t
  rfl

set_option maxHeartbeats 600000 in
-- The prime's actual support appears in all four section-cut hypotheses.
/-- The two literal cuts of a prime are the signed difference of its two
unit graph operations. -/
theorem torusPowerCutPrime_eq_parameterUnitCut_sub
    (ha : TorusPowerCutAdmissibleAt k X Y w n)
    (h₁ : IsFiniteCorrespondencePoint g h' (J₁ w))
    (h₂ : IsFiniteCorrespondencePoint g h' (J₂ w)) :
    torusPowerCutPrime k X Y w n ha =
      torusPowerParameterUnitCut k X Y (singleFiniteCorrespondence g h' (J₁ w) h₁ 1) -
      torusPowerParameterUnitCut k X Y (singleFiniteCorrespondence g h' (J₂ w) h₂ 1) := by
  let s₁ := torusPowerParameterSection k X Y w (n + 1) 1
  let s₂ := torusPowerParameterSection k X Y w (n + 1) uᵧ
  have hs₁ : s₁ = N := by
    simp [s₁, torusPowerParameterSection, torusPowerCutNumerator, Units.val_pow_eq_pow_val]
  have hs₂ : s₂ = D := by
    simp only [s₂, torusPowerParameterSection, torusPowerParameterTargetUnit_pullback,
      torusPowerCutDenominator, Units.val_pow_eq_pow_val]
  let : IsFinite (inclusion (sectionToAffineLine (p ≫ X.hom) N) 0 ≫ p) := ha.numerator_finite
  let : IsFinite (inclusion (sectionToAffineLine (p ≫ X.hom) D) 0 ≫ p) := ha.denominator_finite
  let : IsFinite (inclusion (sectionToAffineLine (p ≫ X.hom) s₁) 0 ≫ p) := by
    rw [hs₁]
    infer_instance
  let : IsFinite (inclusion (sectionToAffineLine (p ≫ X.hom) s₂) 0 ≫ p) := by
    rw [hs₂]
    infer_instance
  have hgen₁ : ∀ z : genericPoints (fiber (sectionToAffineLine (p ≫ X.hom) s₁) 0),
      (inclusion (sectionToAffineLine (p ≫ X.hom) s₁) 0 ≫ p) z.val ∈ genericPoints X.left := by
    rw [hs₁]
    exact ha.numerator_generic
  have hgen₂ : ∀ z : genericPoints (fiber (sectionToAffineLine (p ≫ X.hom) s₂) 0),
      (inclusion (sectionToAffineLine (p ≫ X.hom) s₂) 0 ≫ p) z.val ∈ genericPoints X.left := by
    rw [hs₂]
    exact ha.denominator_generic
  let hp : p ≫ X.hom = q ≫ Y.hom := torusPowerParameterBase_eq k X Y w
  have hN :
      torusPowerParameterUnitCut k X Y (singleFiniteCorrespondence g h' (J₁ w) h₁ 1) =
        sectionCutCorrespondence (X := X) (Y := Y) («P» := P) p q hp N
          ha.numerator_generic := by
    rw [torusPowerParameterUnitCut_apply]
    have he := torusPowerParameterUnitPrime_cut k X Y w (n + 1) 1 h₁ hgen₁
    have hc := cut_section_congr k X Y (P' := P) p q hp hs₁ hgen₁ ha.numerator_generic
    exact he.trans hc
  have hD :
      torusPowerParameterUnitCut k X Y (singleFiniteCorrespondence g h' (J₂ w) h₂ 1) =
        sectionCutCorrespondence (X := X) (Y := Y) («P» := P) p q hp D
          ha.denominator_generic := by
    rw [torusPowerParameterUnitCut_apply]
    have he := torusPowerParameterUnitPrime_cut k X Y w (n + 1) uᵧ h₂ hgen₂
    have hc := cut_section_congr k X Y (P' := P) p q hp hs₂ hgen₂ ha.denominator_generic
    exact he.trans hc
  rw [hN, hD]
  rfl

/-- The weighted cut uses the same two graph operations on every signed
prime of the actual support. -/
theorem torusPowerCut_eq_parameterUnitCut_sub
    (a : torusPowerCutDomain k X Y n)
    (h₁ : a.val ∈ torusPowerParameterGraphDomain k X Y (n + 1) 1)
    (h₂ : a.val ∈ torusPowerParameterGraphDomain k X Y (n + 1) uᵧ) :
    torusPowerCut k X Y n a =
      torusPowerParameterUnitCut k X Y (torusPowerParameterGraph k X Y (n + 1) 1 ⟨a.val, h₁⟩) -
      torusPowerParameterUnitCut k X Y (torusPowerParameterGraph k X Y (n + 1) uᵧ ⟨a.val, h₂⟩) := by
  classical
  let S := a.val.property.1.toFinset
  let hne (w : S) : a.val.val w.val ≠ 0 := a.val.property.1.mem_toFinset.mp w.property
  let hw (w : S) := a.val.property.2 w.val (hne w)
  let ha (w : S) := (mem_torusPowerCutDomain_iff k X Y n a.val).mp a.property w.val (hne w)
  let hb (w : S) := (mem_torusPowerParameterGraphDomain_iff k X Y (n + 1) 1 a.val).mp
    h₁ w.val (hne w)
  let hc (w : S) := (mem_torusPowerParameterGraphDomain_iff k X Y (n + 1) uᵧ a.val).mp
    h₂ w.val (hne w)
  let b (w : S) := singleFiniteCorrespondence g h w.val (hw w) (a.val.val w.val)
  let d (w : S) : torusPowerCutDomain k X Y n :=
    ⟨b w, single_mem_torusPowerCutDomain k X Y w.val n (hw w) (ha w) _⟩
  let d₁ (w : S) : torusPowerParameterGraphDomain k X Y (n + 1) 1 :=
    ⟨b w, single_mem_torusPowerParameterGraphDomain k X Y (n + 1) 1 w.val (hw w) (hb w) _⟩
  let d₂ (w : S) : torusPowerParameterGraphDomain k X Y (n + 1) uᵧ :=
    ⟨b w, single_mem_torusPowerParameterGraphDomain k X Y (n + 1) uᵧ w.val (hw w) (hc w) _⟩
  have hsum : a.val = ∑ w : S, b w := finiteCorrespondence_eq_sum_signedSingles g h a.val
  have hsum₀ : a = ∑ w : S, d w := by
    apply Subtype.ext
    change a.val = (torusPowerCutDomain k X Y n).subtype (∑ w : S, d w)
    rw [map_sum]
    exact hsum
  have hsum₁ : (⟨a.val, h₁⟩ : torusPowerParameterGraphDomain k X Y (n + 1) 1) =
      ∑ w : S, d₁ w := by
    apply Subtype.ext
    change a.val = (torusPowerParameterGraphDomain k X Y (n + 1) 1).subtype (∑ w : S, d₁ w)
    rw [map_sum]
    exact hsum
  have hsum₂ : (⟨a.val, h₂⟩ : torusPowerParameterGraphDomain k X Y (n + 1) uᵧ) =
      ∑ w : S, d₂ w := by
    apply Subtype.ext
    change a.val = (torusPowerParameterGraphDomain k X Y (n + 1) uᵧ).subtype (∑ w : S, d₂ w)
    rw [map_sum]
    exact hsum
  rw [hsum₁, hsum₂, hsum₀]
  simp only [map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro w _
  let r : ℤ := a.val.val w.val
  let Jnum := torusPowerParameterAmbientGraph k (X := X) (Y := Y) (n + 1) 1
  let Jden := torusPowerParameterAmbientGraph k (X := X) (Y := Y) (n + 1) uᵧ
  have h₀ : torusPowerCut k X Y n (d w) = r • torusPowerCutPrime k X Y w.val n (ha w) :=
    torusPowerCut_single k X Y w.val n (hw w) (ha w) r
  have h₁' : torusPowerParameterGraph k X Y (n + 1) 1 (d₁ w) =
      singleFiniteCorrespondence g h' (Jnum w.val) (hb w) r :=
    torusPowerParameterGraph_single k X Y (n + 1) 1 w.val (hw w) (hb w) r
  have h₂' : torusPowerParameterGraph k X Y (n + 1) uᵧ (d₂ w) =
      singleFiniteCorrespondence g h' (Jden w.val) (hc w) r :=
    torusPowerParameterGraph_single k X Y (n + 1) uᵧ w.val (hw w) (hc w) r
  have h₁'' := singleFiniteCorrespondence_eq_zsmul g h' (Jnum w.val) (hb w) r
  have h₂'' := singleFiniteCorrespondence_eq_zsmul g h' (Jden w.val) (hc w) r
  let cut := torusPowerParameterUnitCut k X Y
  let p₁ := singleFiniteCorrespondence g h' (Jnum w.val) (hb w) 1
  let p₂ := singleFiniteCorrespondence g h' (Jden w.val) (hc w) 1
  rw [h₀, h₁', h₂']
  calc
    _ = r • (cut p₁ - cut p₂) :=
      congrArg (r • ·)
        (torusPowerCutPrime_eq_parameterUnitCut_sub k X Y w.val n (ha w) (hb w) (hc w))
    _ = _ := (smul_sub _ _ _).trans (congrArg₂ (· - ·)
      ((map_zsmul cut r p₁).symm.trans (congrArg cut h₁''.symm))
      ((map_zsmul cut r p₂).symm.trans (congrArg cut h₂''.symm)))

end AlgebraicGeometry.Cor
