module

import Colib.AlgebraicGeometry.CoherentCycle.GenericSupportLength

/-! Newly reconstructed regression examples, 2026-11-08. Not compiled in this recovery. -/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

section

variable {P W : Scheme.{u}} [IsLocallyNoetherian P]
    (F : P.Modules) [F.IsCoherent] (j : W ⟶ P) [IsClosedImmersion j]
    (hsupp : (SheafOfModules.supp F : Set P) ⊆ Set.range j)

example (w : W) (hw : w ∈ genericPoints W) :
    Module.length (P.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) ≠ ⊤ :=
  Stacks.Chow.length_stalk_ne_top_of_supp_subset_range_of_mem_genericPoints F j hsupp w hw

example (w : genericPoints W) :
    IsFiniteLength (P.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) :=
  Stacks.Chow.isFiniteLength_stalk_of_supp_subset_range_of_mem_genericPoints F j hsupp w w.2

example (w : W) (hw : j w ∉ SheafOfModules.supp F) :
    Module.length (P.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) = 0 := by
  have : Subsingleton (F.presheaf.stalk (j w)) :=
    not_nontrivial_iff_subsingleton.mp fun hn ↦
      hw ((SheafOfModules.mem_supp_iff_nontrivial_stalk F (j w)).mpr hn)
  exact Module.length_eq_zero

end
