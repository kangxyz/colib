/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
import Colib.Topology.Prespectrum.ZigzagSequentializationLinearGrowth
import Colib.Topology.Prespectrum.ZigzagSequentializationColimit
open CategoryTheory CategoryTheory.Limits Topology Topology.LoopPrespectrum
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Topology.LoopPrespectrum.ZigzagSequentialization.StableBridgeTest
variable (E V : ℕ → LoopPrespectrum.{u})
  (a : ∀ n, E n ⟶ V n) (b : ∀ n, E (n + 1) ⟶ V n)

example : IsColimit (ordinaryCocone E V a b) := ordinaryIsColimit E V a b

example :
    Telescope.inclusion (stage E V a b) (transition E V a b) 0 ≫
      telescopeToOrdinaryColimit E V a b = initialColimitMap E V a b :=
  initial_inclusion_telescopeToOrdinaryColimit E V a b

variable [∀ n k, T1Space ((E n).space k)] [∀ n k, T1Space ((V n).space k)]

example (n k : ℕ) : IsClosedEmbedding ((positiveTransition E V a b n).map k) :=
  positiveTransition_isClosedEmbedding E V a b n k

example : IsStableEquivalence (telescopeToOrdinaryColimit E V a b) :=
  telescopeToOrdinaryColimit_isStableEquivalence E V a b

variable (c : ℕ → ℕ) (hc : Monotone c)
  (hE : ∀ n k, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((E n).point k))))
  (hV : ∀ n k, TopCat.HomotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} ((V n).point k))))
  (hπE : ∀ i n (x : (E i).space (n + c i + 2)) k, k < n + 2 →
    Subsingleton (HomotopyGroup.Pi k ((E i).space (n + c i + 2)) x))
  (hπV : ∀ i n (x : (V i).space (n + c (i + 1) + 2)) k, k < n + 2 →
    Subsingleton (HomotopyGroup.Pi k ((V i).space (n + c (i + 1) + 2)) x))
  (hb : ∀ n, IsStableEquivalence (b n))
  (f : ∀ n, E n ⟶ E (n + 1)) (H : ∀ n, Homotopy (a n) (f n ≫ b n))

example : IsStableEquivalence (telescopeMap E V a b f H) :=
  telescopeMap_isStableEquivalence_of_linearGrowth E V a b c hc hE hV hπE hπV hb f H

end Topology.LoopPrespectrum.ZigzagSequentialization.StableBridgeTest
