/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentializationStable
public import Colib.Topology.Prespectrum.HomotopyPushoutEmbedding
public import Colib.Topology.Prespectrum.SequentialColimitStable
public import Colib.Topology.Prespectrum.TelescopeTail
public import Colib.CategoryTheory.Limits.Shapes.SequentialSystem.TailColimit

/-!
# The actual ordinary colimit of the canonical homotopy-pushout stages

The positive-stage transitions are the original left reduced-pushout inclusions and hence
closed embeddings for T1 original vertices. Their actual ordinary sequential colimit is
also the ordinary colimit of the full sequence, by finality of the successor indexing
functor. The first arrow is retained as its original initial cocone leg; it is not assumed
injective or closed.

The original telescope maps stably to this genuine colimit by its existing forward tail
map and the actual constant-cylinder collapse. This supplies the ordinary-colimit bridge
for the canonical sequentialization displayed in Thomason--Trobaugh 6.4, without a general
higher-categorical homotopy-colimit framework.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Topology
universe u
namespace Topology.LoopPrespectrum.ZigzagSequentialization
variable (E V : ℕ → LoopPrespectrum.{u})
    (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)

/-- The actual positive tail of the canonical pushout sequentialization. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:39"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
abbrev positiveStage (n : ℕ) : LoopPrespectrum.{u} := stage E V a b (n + 1)

/-- Its original successor arrows, which are literal reduced-pushout left inclusions. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:42"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
abbrev positiveTransition (n : ℕ) :
    positiveStage E V a b n ⟶ positiveStage E V a b (n + 1) := transition E V a b (n + 1)

/-- The actual levelwise ordinary colimit of the positive canonical stages. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:46"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
def ordinaryColimit : LoopPrespectrum.{u} :=
  SequentialColimit.prespectrum (positiveStage E V a b) (positiveTransition E V a b)

/-- The original initial vertex enters through the original first solid forward arrow. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:50"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
def initialColimitMap : E 0 ⟶ ordinaryColimit E V a b :=
  a 0 ≫ SequentialColimit.inclusion (positiveStage E V a b) (positiveTransition E V a b) 0

/-- The ordinary tail colimit retains a cocone on the entire original canonical sequence. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:54"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
def ordinaryCocone : Cocone (Functor.ofSequence (transition E V a b)) where
  pt := ordinaryColimit E V a b
  ι := NatTrans.ofSequence
    (fun n ↦ match n with
      | 0 => initialColimitMap E V a b
      | n + 1 => SequentialColimit.inclusion
          (positiveStage E V a b) (positiveTransition E V a b) n)
    (fun n ↦ by
      cases n with
      | zero =>
        change a 0 ≫ SequentialColimit.inclusion
          (positiveStage E V a b) (positiveTransition E V a b) 0 =
            (a 0 ≫ SequentialColimit.inclusion
              (positiveStage E V a b) (positiveTransition E V a b) 0) ≫ 𝟙 _
        exact (Category.comp_id _).symm
      | succ n =>
        rw [Functor.ofSequence_map_homOfLE_succ]
        change positiveTransition E V a b n ≫ SequentialColimit.inclusion
          (positiveStage E V a b) (positiveTransition E V a b) (n + 1) =
            SequentialColimit.inclusion
              (positiveStage E V a b) (positiveTransition E V a b) n ≫ 𝟙 _
        rw [Category.comp_id]
        exact SequentialColimit.successor_inclusion
          (positiveStage E V a b) (positiveTransition E V a b) n)


/-- Successor-index finality proves this is the genuine ordinary colimit of the full sequence. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:81"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
def ordinaryIsColimit : IsColimit (ordinaryCocone E V a b) := by
  let s : ℕ ⥤ ℕ :=
    (show Monotone (fun n : ℕ ↦ n + 1) from fun _ _ h ↦ Nat.add_le_add_right h 1).functor
  let : s.Final := (Monotone.final_functor_iff _).mpr (fun n ↦ ⟨n, Nat.le_succ n⟩)
  refine (Functor.Final.isColimitWhiskerEquiv s (ordinaryCocone E V a b)) ?_
  exact SequentialColimit.isColimit (positiveStage E V a b) (positiveTransition E V a b)

/-- The actual telescope first passes to its positive tail, then collapses cylinder height. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:89"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
def telescopeToOrdinaryColimit :
    Telescope.prespectrum (stage E V a b) (transition E V a b) ⟶ ordinaryColimit E V a b :=
  Telescope.toTail (stage E V a b) (transition E V a b) ≫
    SequentialColimit.collapse (positiveStage E V a b) (positiveTransition E V a b)

/-- The first solid forward arrow is exactly the initial stage face of the actual bridge. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:95"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem initial_inclusion_telescopeToOrdinaryColimit :
    Telescope.inclusion (stage E V a b) (transition E V a b) 0 ≫
      telescopeToOrdinaryColimit E V a b = initialColimitMap E V a b := by
  unfold telescopeToOrdinaryColimit
  rw [← Category.assoc, Telescope.inclusion_toTail, Category.assoc,
    SequentialColimit.inclusion_collapse]
  rfl

/-- Every positive original stage inclusion is its unchanged ordinary colimit cocone leg. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:104"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem positive_inclusion_telescopeToOrdinaryColimit (n : ℕ) :
    Telescope.inclusion (stage E V a b) (transition E V a b) (n + 1) ≫
      telescopeToOrdinaryColimit E V a b =
        SequentialColimit.inclusion (positiveStage E V a b) (positiveTransition E V a b) n := by
  unfold telescopeToOrdinaryColimit
  rw [← Category.assoc, Telescope.inclusion_toTail, Category.assoc,
    SequentialColimit.inclusion_collapse]
  exact SequentialColimit.successor_inclusion
    (positiveStage E V a b) (positiveTransition E V a b) n

variable [∀ n k, T1Space ((E n).space k)] [∀ n k, T1Space ((V n).space k)]

/-- All positive original sequentialization arrows are actual levelwise closed embeddings. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:117"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem positiveTransition_isClosedEmbedding (n k : ℕ) :
    IsClosedEmbedding ((positiveTransition E V a b n).map k) := by
  let : T1Space ((stage E V a b (n + 1)).space k) := stageSpaceT1Space E V a b (n + 1) k
  exact HomotopyPushout.isClosedEmbedding_inl
    (comparison E V a b (n + 1)) (a (n + 1)) k

/-- The exact canonical-stage telescope maps stably to its genuine ordinary direct colimit. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/ZigzagSequentializationColimit.lean:124"
  "adaptation" "Original finite-stage excision and actual telescope-to-ordinary-colimit bridge."]
theorem telescopeToOrdinaryColimit_isStableEquivalence :
    IsStableEquivalence (telescopeToOrdinaryColimit E V a b) := by
  let : ∀ n k, T1Space ((stage E V a b n).space k) := stageSpaceT1Space E V a b
  let : ∀ n k, T1Space ((positiveStage E V a b n).space k) :=
    fun n k ↦ stageSpaceT1Space E V a b (n + 1) k
  exact (Telescope.toTail_isStableEquivalence (stage E V a b) (transition E V a b)).comp
    (SequentialColimit.collapse_isStableEquivalence
      (positiveStage E V a b) (positiveTransition E V a b)
      (positiveTransition_isClosedEmbedding E V a b))

end Topology.LoopPrespectrum.ZigzagSequentialization

namespace Topology.LoopPrespectrum.ZigzagSequentialization

attribute [colib_tag "COL-0564"] telescopeToOrdinaryColimit_isStableEquivalence

end Topology.LoopPrespectrum.ZigzagSequentialization
