module

public import Colib.Topology.HomotopyPullback.PiOneKernel

set_option autoImplicit false

open Topology
open scoped Topology unitInterval
universe u

variable {X A B : Type u} [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
  (f : C(X, B)) (g : C(A, B)) (z : HomotopyPullback f g)

-- The correction's two original coordinates are fixed pointwise for the whole track.
example (t : unitInterval) :
    HomotopyPullback.sourceProjection f g (HomotopyPullback.transportedFiberUnitPath f g z t) =
        HomotopyPullback.sourceProjection f g z ∧
      HomotopyPullback.baseProjection f g (HomotopyPullback.transportedFiberUnitPath f g z t) =
        HomotopyPullback.baseProjection f g z :=
  ⟨rfl, rfl⟩

-- At the specified original pullback point, recover the original class and parameter unit.
example (β : HomotopyGroup.Pi 1 X (HomotopyPullback.sourceProjection f g z))
    (hβ : HomotopyGroup.piMap 0 f rfl β = 1) :
    ∃ sP : HomotopyGroup.Pi 1 (HomotopyPullback f g) z,
      HomotopyGroup.piMap 0 (HomotopyPullback.sourceProjection f g) rfl sP = β ∧
        HomotopyGroup.piMap 0 (HomotopyPullback.baseProjection f g) rfl sP = 1 :=
  HomotopyPullback.exists_piOne_of_map_eq_one f g z β hβ

#print axioms HomotopyPullback.transportedFiberUnitPath
#print axioms HomotopyPullback.exists_piOne_of_map_eq_one
#print axioms HomotopyPullback.piOne_injective_of_gap_surjective
