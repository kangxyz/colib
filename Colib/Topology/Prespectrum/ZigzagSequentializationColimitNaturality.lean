/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentializationColimit
public import Colib.Topology.Prespectrum.SequentialColimitNaturality
public import Colib.Topology.Prespectrum.ZigzagSequentializationMapLaws

/-!
# Actual ordinary-colimit naturality of the canonical zigzag construction

Original strict maps of the two vertex families induce actual maps on the canonical
ordinary colimits through the recursive positive-stage maps. The actual telescope bridge
is strictly natural, and the original initial solid arrow is retained by the same square.
-/
/-!
Implementation provenance: adapted from Quillen at
`ZigzagSequentializationColimitNaturality.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology
universe u
namespace Topology.LoopPrespectrum.ZigzagSequentialization
variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)
    (E' V' : ℕ → LoopPrespectrum.{u})
    (a' : ∀ n, E' n ⟶ V' n) (b' : ∀ n, E' (n + 1) ⟶ V' n)
    (d : ∀ n, E n ⟶ E' n) (v : ∀ n, V n ⟶ V' n)
    (ha : ∀ n, a n ≫ v n = d n ≫ a' n)
    (hb : ∀ n, b n ≫ v n = d (n + 1) ≫ b' n)

/-- The recursive original positive-stage maps induce an actual ordinary-colimit map. -/
def ordinaryColimitMap : ordinaryColimit E V a b ⟶ ordinaryColimit E' V' a' b' :=
  SequentialColimit.map (positiveStage E V a b) (positiveTransition E V a b)
    (positiveStage E' V' a' b') (positiveTransition E' V' a' b')
    (fun n ↦ stageMap E V a b E' V' a' b' d v ha hb (n + 1))
    (fun n ↦ (transition_naturality E V a b E' V' a' b' d v ha hb (n + 1)).symm)

/-- The actual telescope bridge commutes strictly with the original recursive maps. -/
theorem telescopeToOrdinaryColimit_naturality :
    inducedTelescopeMap E V a b E' V' a' b' d v ha hb ≫
        telescopeToOrdinaryColimit E' V' a' b' =
      telescopeToOrdinaryColimit E V a b ≫ ordinaryColimitMap E V a b E' V' a' b' d v ha hb := by
  unfold inducedTelescopeMap telescopeToOrdinaryColimit ordinaryColimitMap
  rw [← Category.assoc, Telescope.toTail_naturality, Category.assoc,
    SequentialColimit.collapse_naturality, ← Category.assoc]

/-- The original first solid arrow has exactly the same input-map naturality. -/
theorem initialColimitMap_naturality :
    initialColimitMap E V a b ≫ ordinaryColimitMap E V a b E' V' a' b' d v ha hb =
      d 0 ≫ initialColimitMap E' V' a' b' := by
  unfold initialColimitMap ordinaryColimitMap
  rw [Category.assoc, SequentialColimit.inclusion_map]
  change a 0 ≫ (v 0 ≫ SequentialColimit.inclusion
    (positiveStage E' V' a' b') (positiveTransition E' V' a' b') 0) =
      d 0 ≫ (a' 0 ≫ SequentialColimit.inclusion
        (positiveStage E' V' a' b') (positiveTransition E' V' a' b') 0)
  rw [← Category.assoc, ha, Category.assoc]

/-- Identity maps on both original vertex families induce the literal identity. -/
@[simp] theorem ordinaryColimitMap_id :
    ordinaryColimitMap E V a b E V a b (fun i ↦ 𝟙 (E i)) (fun i ↦ 𝟙 (V i))
      (fun i ↦ by simp) (fun i ↦ by simp) = 𝟙 (ordinaryColimit E V a b) := by
  unfold ordinaryColimitMap
  apply SequentialColimit.hom_ext
  intro i
  rw [SequentialColimit.inclusion_map, stageMap_id]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- Original zero vertex maps induce the literal zero ordinary-colimit map. -/
@[simp] theorem ordinaryColimitMap_zero :
    ordinaryColimitMap E V a b E' V' a' b' (fun i ↦ zeroHom (E i) (E' i))
      (fun i ↦ zeroHom (V i) (V' i))
      (fun i ↦ by apply Hom.ext; funext k; ext _x; exact (a' i).map_point k |>.symm)
      (fun i ↦ by apply Hom.ext; funext k; ext _x; exact (b' i).map_point k |>.symm) =
        zeroHom (ordinaryColimit E V a b) (ordinaryColimit E' V' a' b') := by
  unfold ordinaryColimitMap
  apply SequentialColimit.hom_ext
  intro i
  rw [SequentialColimit.inclusion_map, stageMap_zero]
  apply Hom.ext
  funext k
  ext _x
  exact (SequentialColimit.inclusion _ _ i).map_point k

variable (E'' V'' : ℕ → LoopPrespectrum.{u})
    (a'' : ∀ n, E'' n ⟶ V'' n) (b'' : ∀ n, E'' (n + 1) ⟶ V'' n)
    (d' : ∀ n, E' n ⟶ E'' n) (v' : ∀ n, V' n ⟶ V'' n)
    (ha' : ∀ n, a' n ≫ v' n = d' n ≫ a'' n)
    (hb' : ∀ n, b' n ≫ v' n = d' (n + 1) ≫ b'' n)

/-- Composition is the exact original composite on both vertex families. -/
@[simp] theorem ordinaryColimitMap_comp :
    ordinaryColimitMap E V a b E' V' a' b' d v ha hb ≫
      ordinaryColimitMap E' V' a' b' E'' V'' a'' b'' d' v' ha' hb' =
        ordinaryColimitMap E V a b E'' V'' a'' b'' (fun i ↦ d i ≫ d' i)
          (fun i ↦ v i ≫ v' i)
          (fun i ↦ by rw [← Category.assoc, ha, Category.assoc, ha', Category.assoc])
          (fun i ↦ by rw [← Category.assoc, hb, Category.assoc, hb', Category.assoc]) := by
  unfold ordinaryColimitMap
  apply SequentialColimit.hom_ext
  intro i
  rw [← Category.assoc, SequentialColimit.inclusion_map, Category.assoc,
    SequentialColimit.inclusion_map, SequentialColimit.inclusion_map,
    ← Category.assoc, stageMap_comp]

end Topology.LoopPrespectrum.ZigzagSequentialization
