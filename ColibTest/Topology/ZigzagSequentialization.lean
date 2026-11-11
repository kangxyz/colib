/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.Topology.Prespectrum.ZigzagSequentializationNaturality
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped unitInterval
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.LoopPrespectrum.ZigzagSequentialization.Test
variable (E V : ℕ → LoopPrespectrum.{u})
  (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)

example (n : ℕ) : stage E V a b (n + 1 + 1) =
    HomotopyPushout.prespectrum (comparison E V a b (n + 1)) (a (n + 1)) :=
  stage_succ_succ E V a b n

example (n : ℕ) : comparison E V a b (n + 1 + 1) =
    b (n + 1) ≫ HomotopyPushout.inr (comparison E V a b (n + 1)) (a (n + 1)) :=
  comparison_succ_succ E V a b n

variable (f : ∀ n, E n ⟶ E (n + 1))
  (H : ∀ n, Homotopy (a n) (f n ≫ b n))

example (n : ℕ) :
    Telescope.inclusion E f n ≫ telescopeMap E V a b f H =
      comparison E V a b n ≫
        Telescope.inclusion (stage E V a b) (transition E V a b) n :=
  inclusion_telescopeMap E V a b f H n

example (k n : ℕ) (s : unitInterval) (x : (E n).space k) :
    (telescopeMap E V a b f H).map k (Telescope.cylinder E f k n (s, x)) =
      (Telescope.mapCoconeHomotopy E f (stage E V a b) (transition E V a b)
        (comparison E V a b) (comparisonTrack E V a b f H) n).level k (s, x) :=
  telescopeMap_cylinder E V a b f H k n s x

variable (E' V' : ℕ → LoopPrespectrum.{u})
  (a' : ∀ n, E' n ⟶ V' n) (b' : ∀ n, E' (n + 1) ⟶ V' n)
  (d : ∀ n, E n ⟶ E' n) (v : ∀ n, V n ⟶ V' n)
  (ha : ∀ n, a n ≫ v n = d n ≫ a' n)
  (hb : ∀ n, b n ≫ v n = d (n + 1) ≫ b' n)

example (n : ℕ) :
    comparison E V a b n ≫ stageMap E V a b E' V' a' b' d v ha hb n =
      d n ≫ comparison E' V' a' b' n :=
  comparison_naturality E V a b E' V' a' b' d v ha hb n

example (n : ℕ) :
    transition E V a b n ≫ stageMap E V a b E' V' a' b' d v ha hb (n + 1) =
      stageMap E V a b E' V' a' b' d v ha hb n ≫ transition E' V' a' b' n :=
  transition_naturality E V a b E' V' a' b' d v ha hb n

end Topology.LoopPrespectrum.ZigzagSequentialization.Test
