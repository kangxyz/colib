module

public import Colib.Topology.HELP.CubeFaceFilling

open Topology.CubicalTests
open scoped Topology unitInterval

universe u

variable {Y : Type u} [TopologicalSpace Y]

-- A three-cube keeps each of the six distinct prescribed maps, not just the corners.
example [ContractibleSpace Y]
    (F : ∀ a : Fin 3 × Bool, C(coordinateFace a, Y))
    (hF : CoordinateFaceCompatible (fun a ↦ F a)) :
    ∃ E : C(Fin 3 → I, Y), ∀ (a : Fin 3 × Bool) (x : coordinateFace a),
      E x.val.val = F a x :=
  exists_fillCoordinateFaces F hF

#print axioms Topology.CubicalTests.exists_fillCoordinateFaces
