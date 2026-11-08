module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.SupportGenericPointLength

/-!
# Finite stalk length along a closed support

For a coherent module on a locally Noetherian scheme, a generic point of any closed subscheme
containing its support has a stalk of finite length. This includes a zero stalk when that point
is not in the support. At a point in the support, a closed immersion reflects specialization,
so maximality of the source component makes the image a generic point of a support component.

The proof uses the native support and generic-point criterion of Stacks 00L5, 02QW and 0EE4 in
`Stacks.Chow.exists_isGenericPoint_component_supp_iff_length`. That criterion uses the actual
scheme stalk and `Scheme.range_fromSpecStalk`.

Recovery status: newly reconstructed on 2026-11-08 from the pinned native sources. This file has
not been compiled or otherwise validated in the current recovery. It is not an exact-byte
recovery of the historical file, and no historical successful check is inherited.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {P W : Scheme.{u}} [IsLocallyNoetherian P]

/-- A coherent module supported on a closed subscheme has finite stalk length at the image of
any generic point of that subscheme. The generic point need not belong to the module's support.
-/
theorem length_stalk_ne_top_of_supp_subset_range_of_mem_genericPoints
    (F : P.Modules) [F.IsCoherent] (j : W ⟶ P) [IsClosedImmersion j]
    (hsupp : (SheafOfModules.supp F : Set P) ⊆ Set.range j)
    (w : W) (hw : w ∈ genericPoints W) :
    Module.length (P.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) ≠ ⊤ := by
  have : F.IsFiniteType := isFiniteType_of_isCoherent F
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  by_cases hmem : j w ∈ SheafOfModules.supp F
  · apply ((exists_isGenericPoint_component_supp_iff_length F (j w)).mp ?_).1
    apply (TopologicalSpace.exists_isGenericPoint_irreducibleComponents_iff
      (SheafOfModules.isClosed_supp F) (j w)).mpr
    refine ⟨hmem, ?_⟩
    intro y hy hyw
    obtain ⟨v, rfl⟩ := hsupp hy
    have hvw : v ⤳ w := j.isClosedEmbedding.isInducing.specializes_iff.mp hyw
    exact congrArg j (TopologicalSpace.forall_specializes_eq_of_mem_genericPoints hw v hvw)
  · have : Subsingleton (F.presheaf.stalk (j w)) :=
      not_nontrivial_iff_subsingleton.mp fun hn ↦
        hmem ((SheafOfModules.mem_supp_iff_nontrivial_stalk F (j w)).mpr hn)
    simp only [Module.length_eq_zero, ne_eq, ENat.zero_ne_top, not_false_eq_true]

/-- The finite-length formulation of
`length_stalk_ne_top_of_supp_subset_range_of_mem_genericPoints`. -/
theorem isFiniteLength_stalk_of_supp_subset_range_of_mem_genericPoints
    (F : P.Modules) [F.IsCoherent] (j : W ⟶ P) [IsClosedImmersion j]
    (hsupp : (SheafOfModules.supp F : Set P) ⊆ Set.range j)
    (w : W) (hw : w ∈ genericPoints W) :
    IsFiniteLength (P.presheaf.stalk (j w)) (F.presheaf.stalk (j w)) :=
  Module.length_ne_top_iff.mp
    (length_stalk_ne_top_of_supp_subset_range_of_mem_genericPoints F j hsupp w hw)

end Stacks.Chow

end
