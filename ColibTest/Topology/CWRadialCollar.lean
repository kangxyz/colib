module

public import Colib.Topology.CWComplex.RadialCollar

open Set Topology Topology.CWComplex
open scoped unitInterval

example (n : ℕ) (V : Set (CharacteristicSphere n)) (hV : IsOpen V) :
    IsOpen (radialCollarSet n V) :=
  isOpen_radialCollarSet n hV

example (n : ℕ) (V : Set (CharacteristicSphere n)) (z : CharacteristicSphere n) :
    characteristicSphereInclusion n z ∈ radialCollarSet n V ↔ z ∈ V :=
  sphere_mem_radialCollarSet n V z

example (n : ℕ) (V : Set (CharacteristicSphere n)) (t : I) (z : RadialCollar n V) :
    radialDirection n (collarRadialMap n V (t, z)).val = radialDirection n z.val :=
  radialDirection_annulusRadialMap n t z.val

example (V : Set (CharacteristicSphere 0)) : radialCollarSet 0 V = ∅ :=
  radialCollarSet_zero V

#print axioms collarRadialMap
#print axioms sphere_mem_radialCollarSet
