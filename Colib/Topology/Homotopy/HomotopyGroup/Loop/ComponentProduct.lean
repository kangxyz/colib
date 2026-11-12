/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Homotopy.HomotopyGroup.Loop.ComponentTranslation
public import Colib.Topology.Homotopy.Equiv.PathComponent
public import Colib.Topology.Homotopy.Equiv.ComponentSigma
public import Colib.Topology.Homotopy.HomotopyGroup.PathComponentWeakEquivalence
public import Colib.Topology.Homotopy.Equiv.Sigma

/-!
# Whole-loop-space products from actual discrete component labels

Right concatenation assembles to a genuine homotopy equivalence from the
product of discrete labels with the constant-loop component to the whole loop
space. Its forward map is exactly concatenation by the displayed representative.
The component classifier must be continuous, and its fibers must be the actual
path components. These are explicit topological hypotheses, not conclusions
about arbitrary loop spaces or about the original Q-space.

Changing representatives and mapping based spaces give actual ordinary
homotopies, constructed pointwise from paths of representative loops. No
strictly natural section, multiplicative splitting, or higher coherence is
asserted.
-/

open Topology CategoryTheory

/-! Implementation source: `Quillen/Topology/HomotopyGroups/Loop/ComponentProduct.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. Actual maps and original proofs are retained. -/

@[expose] public section
noncomputable section

open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Topology

variable {X Y A B : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace A] [DiscreteTopology A] [TopologicalSpace B] [DiscreteTopology B]
  {x : X} {y : Y}

/-- Literal right translation restricts to an actual equivalence of the indicated components. -/
def loopRightTranslationComponentEquiv (γ : Path x x) :
    ContinuousMap.HomotopyEquiv (pathComponent (Path.refl x)) (pathComponent γ) :=
  pathComponentHomotopyEquiv (loopRightTranslationEquiv γ) (Path.refl x) γ
    (by rw [loopRightTranslationEquiv_apply]; exact ⟨loopLeftUnitPath γ⟩)

/-- Component restriction leaves the original concatenated path unchanged. -/
@[simp]
theorem loopRightTranslationComponentEquiv_val (γ : Path x x)
    (z : pathComponent (Path.refl x)) :
    (loopRightTranslationComponentEquiv γ z).val = z.val.trans γ :=
  loopRightTranslationEquiv_apply γ z.val

/-- The actual product map, with no topology assumption hidden in a choice of representatives. -/
def loopComponentProductMap (r : A → Path x x) :
    C(A × pathComponent (Path.refl x), Path x x) where
  toFun z := z.2.val.trans (r z.1)
  continuous_toFun := continuous_prod_of_discrete_left.mpr fun a ↦ by
    change Continuous (fun z : pathComponent (Path.refl x) ↦ z.val.trans (r a))
    exact Path.continuous_trans.comp
      (continuous_subtype_val.prodMk (continuous_const (y := r a)))

/-- The actual whole-space homotopy equivalence, assembled through the open component sum. -/
def loopComponentProductEquiv (label : C(Path x x, A)) (r : A → Path x x)
    (h : ∀ a γ, label γ = a ↔ Joined (r a) γ) :
    ContinuousMap.HomotopyEquiv (A × pathComponent (Path.refl x)) (Path x x) :=
  ((discreteProductSigmaHomeomorph A (pathComponent (Path.refl x))).toHomotopyEquiv.trans
    (ContinuousMap.sigmaHomotopyEquiv fun a ↦ loopRightTranslationComponentEquiv (r a))).trans
      (componentSigmaHomeomorph label r h).toHomotopyEquiv

/-- The forward map is precisely the displayed representative concatenation. -/
@[simp]
theorem loopComponentProductEquiv_toFun (label : C(Path x x, A)) (r : A → Path x x)
    (h : ∀ a γ, label γ = a ↔ Joined (r a) γ) :
    (loopComponentProductEquiv label r h).toFun = loopComponentProductMap r := by
  apply ContinuousMap.ext
  intro z
  exact loopRightTranslationEquiv_apply (r z.1) z.2.val

/-- The label is the original supplied classifier, with no reindexing or sign change. -/
@[simp]
theorem loopComponentProductMap_label (label : C(Path x x, A)) (r : A → Path x x)
    (h : ∀ a γ, label γ = a ↔ Joined (r a) γ)
    (z : A × pathComponent (Path.refl x)) :
    label (loopComponentProductMap r z) = z.1 := by
  apply (h z.1 _).mpr
  change Joined (r z.1) (z.2.val.trans (r z.1))
  simpa only [mem_pathComponent_iff, loopRightTranslationComponentEquiv_val] using
    (loopRightTranslationComponentEquiv (r z.1) z.2).property

/-- A path of representatives gives a displayed homotopy of the actual whole product maps. -/
def loopComponentProductMapHomotopy {r s : A → Path x x}
    (β : ∀ a, Path (r a) (s a)) :
    (loopComponentProductMap r).Homotopy (loopComponentProductMap s) where
  toFun z := z.2.2.val.trans (β z.2.1 z.1)
  continuous_toFun := by
    have hc : Continuous (fun z : A × (unitInterval × pathComponent (Path.refl x)) ↦
        z.2.2.val.trans (β z.1 z.2.1)) :=
      continuous_prod_of_discrete_left.mpr fun a ↦ Path.continuous_trans.comp
        ((continuous_subtype_val.comp continuous_snd).prodMk
          ((β a).continuous.comp continuous_fst))
    exact hc.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left z := congrArg (fun γ ↦ z.2.val.trans γ) (β z.1).source
  map_one_left z := congrArg (fun γ ↦ z.2.val.trans γ) (β z.1).target

/-- Independence of representative choices uses actual joining paths, not agreement on π-groups. -/
theorem loopComponentProductMap_homotopic_of_labels (label : C(Path x x, A))
    (r s : A → Path x x) (hr : ∀ a γ, label γ = a ↔ Joined (r a) γ)
    (hs : ∀ a, label (s a) = a) :
    (loopComponentProductMap r).Homotopic (loopComponentProductMap s) :=
  ⟨loopComponentProductMapHomotopy fun a ↦ ((hr a (s a)).mp (hs a)).somePath⟩

/-- The original based loop map restricted to the constant-loop component. -/
def basedLoopIdentityComponentMap (f : C(X, Y)) (h : f x = y) :
    C(pathComponent (Path.refl x), pathComponent (Path.refl y)) :=
  pathComponentMap (basedLoopMap f h) (Path.refl x) (Path.refl y)
    (by rw [basedLoopMap_refl])

/-- Original maps on the discrete label and identity component define the product-side map. -/
def loopComponentProductChange (f : C(X, Y)) (h : f x = y) (k : A → B) :
    C(A × pathComponent (Path.refl x), B × pathComponent (Path.refl y)) :=
  (⟨k, continuous_of_discreteTopology⟩ : C(A, B)).prodMap
    (basedLoopIdentityComponentMap f h)

set_option maxHeartbeats 800000 in
-- Elaborating the nested product/subtype continuity proof needs additional reduction steps.
/-- Ordinary naturality is given by a literal path of target representatives at every label. -/
def loopComponentProductNaturality (f : C(X, Y)) (h : f x = y) (k : A → B)
    (r : A → Path x x) (s : B → Path y y)
    (β : ∀ a, Path (basedLoopMap f h (r a)) (s (k a))) :
    ((basedLoopMap f h).comp (loopComponentProductMap r)).Homotopy
      ((loopComponentProductMap s).comp (loopComponentProductChange f h k)) where
  toFun z := (basedLoopMap f h z.2.2.val).trans (β z.2.1 z.1)
  continuous_toFun := by
    have hc : Continuous (fun z : A × (unitInterval × pathComponent (Path.refl x)) ↦
        (basedLoopMap f h z.2.2.val).trans (β z.1 z.2.1)) :=
      continuous_prod_of_discrete_left.mpr fun a ↦ Path.continuous_trans.comp
        (((basedLoopMap f h).continuous.comp
          (continuous_subtype_val.comp continuous_snd)).prodMk
            ((β a).continuous.comp continuous_fst))
    exact hc.comp ((continuous_fst.comp continuous_snd).prodMk
      (continuous_fst.prodMk (continuous_snd.comp continuous_snd)))
  map_zero_left z := by
    change (basedLoopMap f h z.2.val).trans (β z.1 0) =
      basedLoopMap f h (z.2.val.trans (r z.1))
    rw [(β z.1).source, basedLoopMap_trans]
  map_one_left z := by
    change (basedLoopMap f h z.2.val).trans (β z.1 1) =
      (basedLoopMap f h z.2.val).trans (s (k z.1))
    exact congrArg (fun γ ↦ (basedLoopMap f h z.2.val).trans γ) (β z.1).target

/-- A strict square of genuine component classifiers supplies the needed representative paths. -/
theorem loopComponentProductMap_naturality_of_labels
    (f : C(X, Y)) (h : f x = y) (k : A → B)
    (labelX : C(Path x x, A)) (labelY : C(Path y y, B))
    (r : A → Path x x) (s : B → Path y y)
    (hr : ∀ a, labelX (r a) = a)
    (hs : ∀ b γ, labelY γ = b ↔ Joined (s b) γ)
    (hk : ∀ γ, labelY (basedLoopMap f h γ) = k (labelX γ)) :
    ((basedLoopMap f h).comp (loopComponentProductMap r)).Homotopic
      ((loopComponentProductMap s).comp (loopComponentProductChange f h k)) := by
  refine ⟨loopComponentProductNaturality f h k r s fun a ↦ ?_⟩
  apply Joined.somePath
  apply Joined.symm
  apply (hs (k a) _).mp
  rw [hk, hr]

end Topology
