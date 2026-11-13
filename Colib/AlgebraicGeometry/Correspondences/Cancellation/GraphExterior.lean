/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.GraphFiber
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.TorusChart
public import Colib.AlgebraicGeometry.Correspondences.Exterior.Support

/-!
# The identity-graph power cuts on an original correspondence support

Pull back the forward torus coordinate to the exterior support. The actual
numerator and denominator zero fibers have ranks `n+1` and `n` over the
original support. Their signed finite pushforward has coefficient `+1`.
The ranks use the unreduced zero fibers in every characteristic.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.NativeTorusPolynomial

variable {k : Type u} [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Gₖ" => SmoothSite.multiplicativeGroupObject Sₖ
set_option quotPrecheck false in
local notation "gₖ" => (multiplicativeGroupBaseChange Sₖ ↘ Sₖ)

variable {P : Scheme.{u}}

/-- The actual forward coordinate on the identity graph over the original support. -/
def torusGraphCoordinate (q : P ⟶ Sₖ) : Γ(pullback (C := Scheme) q gₖ, ⊤) :=
  (pullback.snd q gₖ).appTop (multiplicativeGroupBaseChangeCoordinate Sₖ).val

variable (q : P ⟶ Spec (CommRingCat.of k))

set_option quotPrecheck false in
local notation "Dq" => (pullback (C := Scheme) q gₖ)
set_option quotPrecheck false in
local notation "πq" => (pullback.fst q gₖ)
set_option quotPrecheck false in
local notation "τq" => (pullback.snd q gₖ)
set_option quotPrecheck false in
local notation "vq" => (τq ≫ (torusFieldChart (k := k)).inv)

private theorem torusGraphCoordinate_eq_chart :
    torusGraphCoordinate q = (vq).appTop (chartCutSection (LaurentPolynomial.T 1)) := by
  change (τq).appTop (multiplicativeGroupBaseChangeCoordinate Sₖ).val = _
  rw [chartCutSection, ← torusFieldChart_appTop, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private theorem torusGraphNumerator_eq_chart (n : ℕ) :
    torusGraphCoordinate q ^ (n + 1) - 1 =
      (vq).appTop (chartCutSection
        (1 * toLaurent (powerSubOneDenominator (R := k) (n + 1) (Nat.succ_ne_zero _)).val)) := by
  simp only [torusGraphCoordinate_eq_chart, chartCutSection, one_mul,
    powerSubOneDenominator, map_sub, map_pow, map_one, toLaurent_X]

private theorem torusGraphDenominator_eq_chart (n : ℕ) (hn : n ≠ 0) :
    torusGraphCoordinate q ^ (n + 1) - torusGraphCoordinate q =
      (vq).appTop (chartCutSection
        (LaurentPolynomial.T 1 * toLaurent (powerSubOneDenominator (R := k) n hn).val)) := by
  rw [← identityGraphDenominator_toLaurent n hn, torusGraphCoordinate_eq_chart]
  simp only [chartCutSection, map_sub, map_pow, toLaurent_X]

set_option quotPrecheck false in
local notation "Z₀(" s ")" =>
  (AffineLineFiber.fiber (sectionToAffineLine (πq ≫ q) s) (0 : k))
set_option quotPrecheck false in
local notation "p₀(" s ")" =>
  (AffineLineFiber.inclusion (sectionToAffineLine (πq ≫ q) s) (0 : k) ≫ πq)

private theorem torusGraphCut_isFinite_and_flat (s : Γ(Dq, ⊤))
    (p : k[X]) (hp : p.Monic) (h₀ : IsUnit (p.coeff 0))
    (a : LaurentPolynomial k) (ha : IsUnit a)
    (hs : s = (vq).appTop (chartCutSection (a * toLaurent p))) :
    IsFinite (p₀(s)) ∧ Flat (p₀(s)) := by
  rw [hs, chartCutParameter_baseChange (torusFieldChart_isPullback q)]
  exact ⟨chartCutBaseChange_isFinite (torusFieldChart_isPullback q) p hp h₀ a ha,
    MorphismProperty.of_isPullback (chartCutBaseChange_isPullback
      (torusFieldChart_isPullback q) p h₀ a ha) (projection_flat p hp)⟩

/-- The original numerator zero fiber is finite flat over the exterior support's base. -/
theorem torusGraphNumerator_isFinite_and_flat (n : ℕ) :
    let s := torusGraphCoordinate q ^ (n + 1) - 1
    IsFinite (p₀(s)) ∧ Flat (p₀(s)) :=
  let p := powerSubOneDenominator (R := k) (n + 1) (Nat.succ_ne_zero n)
  torusGraphCut_isFinite_and_flat q _ p.val p.property.1 p.property.2 1 isUnit_one
    (torusGraphNumerator_eq_chart q n)

/-- The original denominator zero fiber is finite flat over the exterior support's base. -/
theorem torusGraphDenominator_isFinite_and_flat (n : ℕ) (hn : n ≠ 0) :
    let t := torusGraphCoordinate q ^ (n + 1) - torusGraphCoordinate q
    IsFinite (p₀(t)) ∧ Flat (p₀(t)) :=
  let p := powerSubOneDenominator (R := k) n hn
  torusGraphCut_isFinite_and_flat q _ p.val p.property.1 p.property.2
    _ (LaurentPolynomial.isUnit_T 1) (torusGraphDenominator_eq_chart q n hn)

theorem torusGraphNumerator_isFinite (n : ℕ) :
    IsFinite (p₀(torusGraphCoordinate q ^ (n + 1) - 1)) :=
  (torusGraphNumerator_isFinite_and_flat q n).1

theorem torusGraphDenominator_isFinite (n : ℕ) (hn : n ≠ 0) :
    IsFinite (p₀(torusGraphCoordinate q ^ (n + 1) - torusGraphCoordinate q)) :=
  (torusGraphDenominator_isFinite_and_flat q n hn).1

variable [IsNoetherian P]

private theorem finiteCyclePushforward_chartCut_of_eq {Z : Scheme.{u}}
    (j : P ⟶ Z) [IsFinite j] {f : Dq ⟶ Spec (.of k[X])}
    (p : k[X]) (hp : p.Monic) (h₀ : IsUnit (p.coeff 0))
    (a : LaurentPolynomial k) (ha : IsUnit a)
    (hf : f = vq ≫ chartCutParameter (a * toLaurent p))
    [IsFinite (AffineLineFiber.inclusion f 0 ≫ πq)] [IsNoetherian (AffineLineFiber.fiber f 0)] :
    finiteCyclePushforward ((AffineLineFiber.inclusion f 0 ≫ πq) ≫ j)
        (AlgebraicCycle.fundamentalCycle (AffineLineFiber.fiber f 0)) =
      (p.natDegree : ℤ) • finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle P) := by
  subst f
  exact finiteCyclePushforward_chartCutBaseChange j (torusFieldChart_isPullback q) p hp h₀ a ha

set_option maxHeartbeats 800000 in
-- The original section is compared with the chart cut in the dependent fiber type.
private theorem finiteCyclePushforward_torusGraphCut {Z : Scheme.{u}}
    (j : P ⟶ Z) [IsFinite j] (s : Γ(Dq, ⊤)) [IsFinite (p₀(s))]
    (p : k[X]) (hp : p.Monic) (h₀ : IsUnit (p.coeff 0))
    (a : LaurentPolynomial k) (ha : IsUnit a)
    (hs : s = (vq).appTop (chartCutSection (a * toLaurent p))) :
    letI : IsNoetherian Z₀(s) := isNoetherian_of_finiteType (p₀(s))
    finiteCyclePushforward (p₀(s) ≫ j) (AlgebraicCycle.fundamentalCycle Z₀(s)) =
      (p.natDegree : ℤ) • finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle P) := by
  let : IsNoetherian Z₀(s) := isNoetherian_of_finiteType (p₀(s))
  apply finiteCyclePushforward_chartCut_of_eq q j p hp h₀ a ha
  rw [hs, chartCutParameter_baseChange (torusFieldChart_isPullback q)]

set_option maxHeartbeats 800000 in
-- Both original whole zero fibers retain their finiteness and Noetherian instances.
/-- The actual signed power cuts on the identity graph push to the original support cycle. -/
theorem torusIdentityGraph_powerCut_sub {Z : Scheme.{u}} (j : P ⟶ Z) [IsFinite j]
    (n : ℕ) (hn : n ≠ 0) :
    let s := torusGraphCoordinate q ^ (n + 1) - 1
    let t := torusGraphCoordinate q ^ (n + 1) - torusGraphCoordinate q
    letI : IsFinite (p₀(s)) := torusGraphNumerator_isFinite q n
    letI : IsFinite (p₀(t)) := torusGraphDenominator_isFinite q n hn
    letI : IsNoetherian Z₀(s) := isNoetherian_of_finiteType (p₀(s))
    letI : IsNoetherian Z₀(t) := isNoetherian_of_finiteType (p₀(t))
    finiteCyclePushforward (p₀(s) ≫ j) (AlgebraicCycle.fundamentalCycle Z₀(s)) -
        finiteCyclePushforward (p₀(t) ≫ j) (AlgebraicCycle.fundamentalCycle Z₀(t)) =
      finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle P) := by
  let : IsFinite (p₀(torusGraphCoordinate q ^ (n + 1) - 1)) := torusGraphNumerator_isFinite q n
  let : IsFinite (p₀(torusGraphCoordinate q ^ (n + 1) - torusGraphCoordinate q)) :=
    torusGraphDenominator_isFinite q n hn
  let p := powerSubOneDenominator (R := k) (n + 1) (Nat.succ_ne_zero n)
  let d := powerSubOneDenominator (R := k) n hn
  have hs := finiteCyclePushforward_torusGraphCut q j _ p.val p.property.1 p.property.2
    1 isUnit_one (torusGraphNumerator_eq_chart q n)
  have ht := finiteCyclePushforward_torusGraphCut q j _ d.val d.property.1 d.property.2
    _ (LaurentPolynomial.isUnit_T 1) (torusGraphDenominator_eq_chart q n hn)
  have hpn : p.val.natDegree = n + 1 := powerSubOneDenominator_natDegree _ _
  have hdn : d.val.natDegree = n := powerSubOneDenominator_natDegree _ _
  change _ - _ = _
  rw [hs, ht, hpn, hdn, sub_eq_add_neg, ← sub_zsmul, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_left, one_zsmul]

/-- Both actual torus coordinate pullbacks on the exterior identity support agree with its
forward coordinate. -/
theorem exteriorIdentity_coordinates (X Y : SmoothSite Sₖ)
    (W : (pullback X.hom Y.hom).IdealSheafData) :
    let q := exteriorSupportSourceProjection X Y W ≫ X.hom
    let t := torusGraphCoordinate q
    ((exteriorIdentitySource X Y Gₖ W ≫ pullback.snd X.hom (Gₖ).hom).appTop
      (multiplicativeGroupBaseChangeCoordinate Sₖ).val = t) ∧
    ((exteriorIdentityTarget X Y Gₖ W ≫ pullback.snd Y.hom (Gₖ).hom).appTop
      (multiplicativeGroupBaseChangeCoordinate Sₖ).val = t) := by
  let evaluate (f : exteriorIdentitySupport X Y Gₖ W ⟶ (Gₖ).left) :
      Γ(exteriorIdentitySupport X Y Gₖ W, ⊤) :=
    f.appTop (multiplicativeGroupBaseChangeCoordinate Sₖ).val
  exact ⟨congrArg evaluate (exteriorIdentitySource_snd X Y Gₖ W),
    congrArg evaluate (exteriorIdentityTarget_snd X Y Gₖ W)⟩

end AlgebraicGeometry.NativeTorusPolynomial
