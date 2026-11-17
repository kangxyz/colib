module

public import Colib.Topology.CWComplex.SimplyConnectedCover

open Set Topology Topology.CWComplex
open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  (C : Set X) [CWComplex C]

example (x : C) :
    ∃ U : Set C, IsOpen U ∧ x ∈ U ∧
      Nonempty ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, C)).Homotopy
        (ContinuousMap.const U x)) :=
  exists_ambientContractionNeighborhood C x

example : PathThinNeighborhoods C :=
  pathThinNeighborhoods C

example [ConnectedSpace C] :
    ∃ (E : Type u) (_ : TopologicalSpace E) (p : C(E, C)),
      IsCoveringMap p ∧ Function.Surjective p ∧ SimplyConnectedSpace E :=
  exists_simplyConnected_cover C

#print axioms exists_open_ambientPathThin
#print axioms exists_simplyConnected_cover
