/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.ComponentProduct
public import Colib.Topology.Homotopy.Equiv.HomotopySquare

/-!
# Exact identity-slice normalization of the loop-component product

When the neutral representative is the constant loop, replace right
concatenation on that one slice by the exact component inclusion. The explicit
constant-suffix removal homotopy preserves the genuine homotopy equivalence.
Representative independence has a homotopy constant on the entire neutral
slice. Labels remain those of the supplied classifier.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/NormalizedComponentProduct.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section

open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Topology

attribute [local instance] Classical.propDecidable

variable {X A : Type u} [TopologicalSpace X] [TopologicalSpace A]
  [DiscreteTopology A] {x : X}

/-- The neutral slice is exactly the original inclusion of the identity component. -/
def normalizedLoopComponentProductMap (a₀ : A) (r : A → Path x x) :
    C(A × pathComponent (Path.refl x), Path x x) where
  toFun z := if z.1 = a₀ then z.2.val else z.2.val.trans (r z.1)
  continuous_toFun := continuous_prod_of_discrete_left.mpr fun a ↦ by
    by_cases ha : a = a₀
    · simpa only [ha, ite_true, Function.comp_def] using
        (continuous_subtype_val : Continuous (fun z : pathComponent (Path.refl x) ↦ z.val))
    · simpa only [ha, ite_false, Function.comp_def] using
        Path.continuous_trans.comp
          (continuous_subtype_val.prodMk (continuous_const (y := r a)))

@[simp]
theorem normalizedLoopComponentProductMap_zero (a₀ : A) (r : A → Path x x)
    (z : pathComponent (Path.refl x)) :
    normalizedLoopComponentProductMap a₀ r (a₀, z) = z.val := by
  change (if a₀ = a₀ then z.val else z.val.trans (r a₀)) = z.val
  exact ite_eq_left rfl

/-- Constant-suffix removal modifies only the neutral slice. -/
def loopComponentProductNormalization (a₀ : A) (r : A → Path x x)
    (hr : r a₀ = Path.refl x) :
    (loopComponentProductMap r).Homotopy (normalizedLoopComponentProductMap a₀ r) where
  toFun z := if z.2.1 = a₀ then Path.delayReflRight z.1 z.2.2.val
    else z.2.2.val.trans (r z.2.1)
  continuous_toFun := by
    have hc : Continuous (fun z : A × (unitInterval × pathComponent (Path.refl x)) ↦
        if z.1 = a₀ then Path.delayReflRight z.2.1 z.2.2.val
          else z.2.2.val.trans (r z.1)) := by
      apply continuous_prod_of_discrete_left.mpr
      intro a
      by_cases ha : a = a₀
      · simpa only [ha, ite_true, Function.comp_def] using Path.continuous_delayReflRight.comp
          (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      · simpa only [ha, ite_false, Function.comp_def] using Path.continuous_trans.comp
          ((continuous_subtype_val.comp continuous_snd).prodMk
            (continuous_const (y := r a)))
    exact hc.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left z := by
    by_cases hz : z.1 = a₀
    · simp only [hz, ite_true, Path.delayReflRight_zero, loopComponentProductMap,
        ContinuousMap.coe_mk, hr]
    · simp only [hz, ite_false, loopComponentProductMap, ContinuousMap.coe_mk]
  map_one_left z := by
    by_cases hz : z.1 = a₀ <;>
      simp only [hz, ite_true, ite_false, Path.delayReflRight_one,
        normalizedLoopComponentProductMap, ContinuousMap.coe_mk]

/-- Exact normalization retains the inverse and both genuine inverse homotopies. -/
def normalizedLoopComponentProductEquiv (label : C(Path x x, A))
    (a₀ : A) (r : A → Path x x)
    (h : ∀ a γ, label γ = a ↔ Joined (r a) γ) (hr : r a₀ = Path.refl x) :
    ContinuousMap.HomotopyEquiv (A × pathComponent (Path.refl x)) (Path x x) :=
  (loopComponentProductEquiv label r h).ofHomotopic
    (normalizedLoopComponentProductMap a₀ r) (by
      rw [loopComponentProductEquiv_toFun]
      exact ⟨(loopComponentProductNormalization a₀ r hr).symm⟩)

@[simp]
theorem normalizedLoopComponentProductEquiv_toFun (label : C(Path x x, A))
    (a₀ : A) (r : A → Path x x)
    (h : ∀ a γ, label γ = a ↔ Joined (r a) γ) (hr : r a₀ = Path.refl x) :
    (normalizedLoopComponentProductEquiv label a₀ r h hr).toFun =
      normalizedLoopComponentProductMap a₀ r := rfl

/-- Exact neutral normalization preserves the supplied original component label. -/
@[simp]
theorem normalizedLoopComponentProductMap_label (label : C(Path x x, A))
    (a₀ : A) (r : A → Path x x)
    (h : ∀ a γ, label γ = a ↔ Joined (r a) γ) (hr : r a₀ = Path.refl x)
    (z : A × pathComponent (Path.refl x)) :
    label (normalizedLoopComponentProductMap a₀ r z) = z.1 := by
  by_cases hz : z.1 = a₀
  · change label (if z.1 = a₀ then z.2.val else z.2.val.trans (r z.1)) = z.1
    rw [ite_eq_left hz, hz]
    apply (h a₀ z.2.val).mpr
    rw [hr]
    exact z.2.property
  · change label (if z.1 = a₀ then z.2.val else z.2.val.trans (r z.1)) = z.1
    rw [ite_eq_right hz]
    exact loopComponentProductMap_label label r h z

/-- Representative changes are constant on the entire exactly normalized neutral slice. -/
def normalizedLoopComponentProductHomotopy (a₀ : A) {r s : A → Path x x}
    (β : ∀ a, Path (r a) (s a)) :
    (normalizedLoopComponentProductMap a₀ r).Homotopy
      (normalizedLoopComponentProductMap a₀ s) where
  toFun z := if z.2.1 = a₀ then z.2.2.val else z.2.2.val.trans (β z.2.1 z.1)
  continuous_toFun := by
    have hc : Continuous (fun z : A × (unitInterval × pathComponent (Path.refl x)) ↦
        if z.1 = a₀ then z.2.2.val else z.2.2.val.trans (β z.1 z.2.1)) := by
      apply continuous_prod_of_discrete_left.mpr
      intro a
      by_cases ha : a = a₀
      · simpa only [ha, ite_true, Function.comp_def] using
          (continuous_subtype_val.comp continuous_snd : Continuous
            (fun z : unitInterval × pathComponent (Path.refl x) ↦ z.2.val))
      · simpa only [ha, ite_false, Function.comp_def] using Path.continuous_trans.comp
          ((continuous_subtype_val.comp continuous_snd).prodMk
            ((β a).continuous.comp continuous_fst))
    exact hc.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left z := by
    by_cases hz : z.1 = a₀ <;>
      simp only [hz, ite_true, ite_false, Path.source,
        normalizedLoopComponentProductMap, ContinuousMap.coe_mk]
  map_one_left z := by
    by_cases hz : z.1 = a₀ <;>
      simp only [hz, ite_true, ite_false, Path.target,
        normalizedLoopComponentProductMap, ContinuousMap.coe_mk]

@[simp]
theorem normalizedLoopComponentProductHomotopy_zero (a₀ : A) {r s : A → Path x x}
    (β : ∀ a, Path (r a) (s a)) (t : unitInterval)
    (z : pathComponent (Path.refl x)) :
    normalizedLoopComponentProductHomotopy a₀ β (t, (a₀, z)) = z.val := by
  change (if a₀ = a₀ then z.val else z.val.trans (β a₀ t)) = z.val
  exact ite_eq_left rfl

/-- The genuine inverse recovers exactly the same label, rather than an arbitrary permutation. -/
theorem normalizedLoopComponentProductEquiv_inverse_label (label : C(Path x x, A))
    (a₀ : A) (r : A → Path x x)
    (h : ∀ a γ, label γ = a ↔ Joined (r a) γ) (hr : r a₀ = Path.refl x)
    (γ : Path x x) :
    ((normalizedLoopComponentProductEquiv label a₀ r h hr).invFun γ).1 = label γ := by
  let e := normalizedLoopComponentProductEquiv label a₀ r h hr
  have hp : Joined (r (e.invFun γ).1) (e (e.invFun γ)) :=
    (h _ _).mp (normalizedLoopComponentProductMap_label label a₀ r h hr (e.invFun γ))
  exact ((h _ γ).mpr (hp.trans ⟨e.right_inv.some.evalAt γ⟩)).symm

variable {Y B : Type u} [TopologicalSpace Y] [TopologicalSpace B]
  [DiscreteTopology B] {y : Y}

/-- The exactly normalized equivalences are natural in the ordinary homotopy category.
The three homotopies are actual source normalization, representative transport, and target
normalization. This statement makes no claim of a multiplicative or higher-coherent splitting. -/
theorem normalizedLoopComponentProductMap_naturality
    (f : C(X, Y)) (h : f x = y) (k : A → B) (a₀ : A) (b₀ : B)
    (r : A → Path x x) (s : B → Path y y)
    (hr : r a₀ = Path.refl x) (hs : s b₀ = Path.refl y)
    (β : ∀ a, Path (basedLoopMap f h (r a)) (s (k a))) :
    ((basedLoopMap f h).comp (normalizedLoopComponentProductMap a₀ r)).Homotopic
      ((normalizedLoopComponentProductMap b₀ s).comp (loopComponentProductChange f h k)) :=
  ((ContinuousMap.Homotopic.refl (basedLoopMap f h)).comp
    ⟨(loopComponentProductNormalization a₀ r hr).symm⟩).trans
      ((show ((basedLoopMap f h).comp (loopComponentProductMap r)).Homotopic
        ((loopComponentProductMap s).comp (loopComponentProductChange f h k)) from
          ⟨loopComponentProductNaturality f h k r s β⟩).trans
            ((show (loopComponentProductMap s).Homotopic
              (normalizedLoopComponentProductMap b₀ s) from
                ⟨loopComponentProductNormalization b₀ s hs⟩).comp
                  (ContinuousMap.Homotopic.refl (loopComponentProductChange f h k))))

end Topology
