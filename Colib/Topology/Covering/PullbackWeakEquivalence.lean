/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Covering.HomotopyGroups
public import Colib.Topology.Covering.PullbackFiber

/-!
# Higher homotopy bijectivity descends along a literal covering pullback

The two actual covering projections give bijections in degrees at least two.
The existing naturality square for the literal matching-pair subtype then
cancels the first projection. The endpoint equation at the given matching
pair is retained in the resulting based map.

Implementation provenance: specialized from
`Quillen/Topology/Covering/HomotopyGroups.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using the native pullback square.
-/

@[expose] public section

universe u v w
open scoped Topology

namespace Topology.Covering.Pullback

variable {X : Type u} {Y : Type v} {E : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
  (f : C(X, Y)) (q : C(E, Y)) (hq : IsCoveringMap q) (z₀ : Space f q)

include hq in
/-- Higher-degree bijectivity of the actual second projection descends to the
original base map at the specified matching pair. -/
theorem piMap_base_bijective_of_lift (m : ℕ)
    (hk : Function.Bijective (HomotopyGroup.piMap (m + 1) (lift f q) (x := z₀) rfl)) :
    Function.Bijective (HomotopyGroup.piMap (m + 1) f z₀.property) := by
  let p := HomotopyGroup.piMap (m + 1) (projection f q) (x := z₀) rfl
  let l := HomotopyGroup.piMap (m + 1) (lift f q) (x := z₀) rfl
  let q' := HomotopyGroup.piMap (m + 1) q (x := z₀.val.2) rfl
  let f' := HomotopyGroup.piMap (m + 1) f z₀.property
  have hp : Function.Bijective p :=
    ((projection_isCoveringMap f q hq).piProjectionEquiv m z₀ rfl).bijective
  have hq' : Function.Bijective q' := (hq.piProjectionEquiv m z₀.val.2 rfl).bijective
  have hsq : (q' : _ → _) ∘ l = (f' : _ → _) ∘ p :=
    funext (piMap_square f q z₀ (m + 1))
  have hl : Function.Bijective ((q' : _ → _) ∘ l) := hq'.comp hk
  rw [hsq] at hl
  exact (Function.Bijective.of_comp_iff _ hp).mp hl

end Topology.Covering.Pullback
