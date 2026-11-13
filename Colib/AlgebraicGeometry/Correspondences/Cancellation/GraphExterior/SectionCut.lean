/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.GraphExterior
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.RelativeDivisor.SupportIso
public import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian
import Colib.AlgebraicGeometry.Chow.IntegralFundamental

/-!
# The signed section cut of an exterior identity support

The two cuts retain the original exterior support and its maps to both factors.
The signed whole quotient cycle pushes to the original prime with coefficient
one. This is the diagonal graph calculation of Voevodsky's Lemma 4.3.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NativeTorusPolynomial Stacks.Chow
open AlgebraicGeometry.Scheme TopologicalSpace Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
set_option quotPrecheck false in
local notation "gₖ" => (multiplicativeGroupBaseChange Sₖ ↘ Sₖ)

private theorem isNoetherian_of_finite_map {A B : Scheme.{u}} [IsNoetherian B]
    (f : A ⟶ B) [IsFinite f] : IsNoetherian A :=
  Scheme.isNoetherian_of_finiteType_of_isNoetherian f

section Base

variable {A : Scheme.{u}} [IsNoetherian A] (q : A ⟶ Spec (CommRingCat.of k))

set_option quotPrecheck false in
local notation "πq" => (pullback.fst q gₖ)

variable (b : pullback (C := Scheme) q
  (multiplicativeGroupBaseChange (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))
  ⟶ Spec (CommRingCat.of k))

set_option quotPrecheck false in
local notation "i₀(" s ")" => (AffineLineFiber.inclusion (sectionToAffineLine b s) (0 : k))
set_option quotPrecheck false in
local notation "Z₀(" s ")" => (AffineLineFiber.fiber (sectionToAffineLine b s) (0 : k))

private theorem torusIdentityGraph_powerCut_sub_of_base
    {Z : Scheme.{u}} (j : A ⟶ Z) [IsFinite j] (hb : b = πq ≫ q)
    (n : ℕ) (hn : n ≠ 0) :
    let s := torusGraphCoordinate q ^ (n + 1) - 1
    let t := torusGraphCoordinate q ^ (n + 1) - torusGraphCoordinate q
    ∀ [IsFinite (i₀(s) ≫ πq)] [IsFinite (i₀(t) ≫ πq)],
    letI : IsNoetherian Z₀(s) := isNoetherian_of_finite_map (i₀(s) ≫ πq)
    letI : IsNoetherian Z₀(t) := isNoetherian_of_finite_map (i₀(t) ≫ πq)
    finiteCyclePushforward ((i₀(s) ≫ πq) ≫ j) (AlgebraicCycle.fundamentalCycle Z₀(s)) -
        finiteCyclePushforward ((i₀(t) ≫ πq) ≫ j) (AlgebraicCycle.fundamentalCycle Z₀(t)) =
      finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle A) := by
  subst b
  intros
  exact torusIdentityGraph_powerCut_sub q j n hn

end Base

variable (X Y : SmoothSite (Spec (CommRingCat.of k))) (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)

local notation "W" => integralComponentAt z
local notation "pW" => exteriorSupportSourceProjection X Y W
local notation "qW" => exteriorSupportTargetProjection X Y W
set_option quotPrecheck false in
local notation "bW" => (pW ≫ X.hom)
set_option quotPrecheck false in
local notation "D" => pullback (C := Scheme) bW gₖ
set_option quotPrecheck false in
local notation "π" => pullback.fst bW gₖ

set_option quotPrecheck false in
local notation "i₀(" p "," u₀ ")" =>
  (AffineLineFiber.inclusion (sectionToAffineLine (p ≫ X.hom) u₀) (0 : k))
set_option quotPrecheck false in
local notation "Z₀(" p "," u₀ ")" =>
  (AffineLineFiber.fiber (sectionToAffineLine (p ≫ X.hom) u₀) (0 : k))

/-- The signed section cut on the literal exterior identity support recovers the original prime. -/
theorem signedSectionCutCorrespondence_exteriorIdentity
    (p : D ⟶ X.left) (g : D ⟶ Y.left) (s t : Γ(D, ⊤))
    (hp : p = π ≫ pW) (hg : g = π ≫ qW) (h : p ≫ X.hom = g ≫ Y.hom)
    (n : ℕ) (hn : n ≠ 0)
    (hs : s = torusGraphCoordinate bW ^ (n + 1) - 1)
    (ht : t = torusGraphCoordinate bW ^ (n + 1) - torusGraphCoordinate bW)
    [IsFinite (i₀(p,s) ≫ p)] [IsFinite (i₀(p,t) ≫ p)]
    (hₛ : ∀ a : genericPoints Z₀(p,s), (i₀(p,s) ≫ p) a.val ∈ genericPoints X.left)
    (hₜ : ∀ a : genericPoints Z₀(p,t), (i₀(p,t) ≫ p) a.val ∈ genericPoints X.left) :
    signedSectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := D) p g h s t hₛ hₜ =
      singleFiniteCorrespondence X.hom Y.hom z hz 1 := by
  classical
  have hbase : p ≫ X.hom = π ≫ bW :=
    (congrArg (fun f : D ⟶ X.left => f ≫ X.hom) hp).trans (Category.assoc π pW X.hom)
  let : IsFinite (i₀(p,s) ≫ π) := by
    rw [hbase, hs]
    exact torusGraphNumerator_isFinite bW n
  let : IsFinite (i₀(p,t) ≫ π) := by
    rw [hbase, ht]
    exact torusGraphDenominator_isFinite bW n hn
  let : IsFinite pW := hz.1
  let : IsNoetherian (W).subscheme := isNoetherian_of_finiteType_of_isNoetherian pW
  let : IsIntegral (W).subscheme := isIntegral_integralComponentAt z
  let : IsNoetherian Z₀(p,s) := isNoetherian_of_finite_map (i₀(p,s) ≫ π)
  let : IsNoetherian Z₀(p,t) := isNoetherian_of_finite_map (i₀(p,t) ≫ π)
  have hm (u₀ : Γ(D, ⊤)) :
      sectionCutSupportMap (k := k) (X := X) (Y := Y) (P := D) p g h u₀ =
        (i₀(p,u₀) ≫ π) ≫ (W).subschemeι := by
    apply pullback.hom_ext
    · simp only [Category.assoc, sectionCutSupportMap_fst, exteriorSupportSourceProjection, hp]
    · simp only [Category.assoc, sectionCutSupportMap_snd, exteriorSupportTargetProjection, hg]
  have hdegree :
      finiteCyclePushforward ((i₀(p,s) ≫ π) ≫ (W).subschemeι)
          (AlgebraicCycle.fundamentalCycle Z₀(p,s)) -
        finiteCyclePushforward ((i₀(p,t) ≫ π) ≫ (W).subschemeι)
          (AlgebraicCycle.fundamentalCycle Z₀(p,t)) =
        finiteCyclePushforward (W).subschemeι (AlgebraicCycle.fundamentalCycle (W).subscheme) := by
    subst s
    subst t
    exact torusIdentityGraph_powerCut_sub_of_base bW (p ≫ X.hom) (W).subschemeι hbase n hn
  apply Subtype.ext
  change (sectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := D) p g h s hₛ).val -
    (sectionCutCorrespondence (k := k) (X := X) (Y := Y) (P := D) p g h t hₜ).val = _
  rw [sectionCutCorrespondence_val, sectionCutCorrespondence_val,
    finiteCyclePushforward_congr _ _ (hm s), finiteCyclePushforward_congr _ _ (hm t), hdegree,
    finiteCyclePushforward_fundamentalCycle_integral]
  change single ((W).subschemeι (genericPoint (W).subscheme)) (1 : ℤ) = single z 1
  rw [show (W).subschemeι (genericPoint (W).subscheme) = z from
    genericPointOf_integralComponentAt z]

end AlgebraicGeometry.Cor
