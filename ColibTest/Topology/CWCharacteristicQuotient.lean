module

public import Colib.Topology.CWComplex.CharacteristicQuotient

open Set Topology
open scoped Topology unitInterval

namespace Topology.CWComplex

universe u v

variable {X : Type u} [TopologicalSpace X] (C : Set X) [CWComplex C]

example (n : ℕ) (i : RelCWComplex.cell C n) (z : CharacteristicDisk n) :
    (characteristicQuotient C ⟨n, i, z⟩).val = RelCWComplex.map n i z := rfl

example [T2Space X] : IsQuotientMap (characteristicQuotient C) :=
  isQuotientMap_characteristicQuotient C

example [T2Space X] {Y : Type v} [TopologicalSpace Y] (f : C → Y) :
    Continuous f ↔ ∀ n (i : RelCWComplex.cell C n),
      Continuous fun z : CharacteristicDisk n ↦ f (characteristicQuotient C ⟨n, i, z⟩) :=
  continuous_iff_characteristic C f

example [T2Space X] {Y : Type v} [TopologicalSpace Y] (H : I × C → Y)
    (hH : Continuous (fun z : I × CharacteristicDomain C ↦
      H (z.1, characteristicQuotient C z.2))) : Continuous H :=
  continuous_homotopy_of_characteristic C H hH

#print axioms isQuotientMap_characteristicQuotient
#print axioms continuous_homotopy_of_characteristic

end Topology.CWComplex
