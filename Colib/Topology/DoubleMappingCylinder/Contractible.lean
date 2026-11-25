/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Colib.Topology.DoubleMappingCylinder.Invariance
public import Mathlib.Topology.Homotopy.Contractible
public import Colib.Topology.Homotopy.HomotopyGroup.Contractible
public import Colib.Topology.HELP.WeakCubeFilling

/-!
# Contractible double mapping cylinders and exact finite cube extensions

An actual double mapping cylinder of three contractible spaces is contractible.
Their contractions need not be compatible with the attaching maps. Every map
from a finite cube boundary into such a cylinder therefore extends with
literal boundary equality.

Implementation provenance: adapted from
`Quillen/Topology/DoubleMappingCylinder/Contractible.lean` at commit
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits MonoidalCategory Topology
open scoped Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace TopCat.DoubleCylinder

variable {A B C D : TopCat.{u}}
  [hA : ContractibleSpace A] [hB : ContractibleSpace B] [hC : ContractibleSpace C]
  (f : A ⟶ B) (g : A ⟶ C)
  {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
  (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e)

include hA hB hC f g sq in
/-- An actual double mapping cylinder of three contractible spaces is
contractible, with no compatibility assumptions on their contractions. -/
theorem contractibleSpace_of_contractible : ContractibleSpace D := by
  let P : TopCat.{u} := TopCat.of PUnit.{u + 1}
  have hend : endMap (𝟙 P) (𝟙 P) = 𝟙 (TopCat.of (P ⊕ P)) := by
    ext z
    cases z <;> rfl
  have sqP : IsPushout (TopCat.intervalEndpoints P) (endMap (𝟙 P) (𝟙 P))
      (𝟙 (P ⊗ TopCat.I)) (TopCat.intervalEndpoints P) := by
    rw [hend]
    exact IsPushout.of_vert_isIso ⟨by simp⟩
  let a : A ⟶ P := TopCat.ofHom (ContinuousMap.const A PUnit.unit)
  let b : B ⟶ P := TopCat.ofHom (ContinuousMap.const B PUnit.unit)
  let c : C ⟶ P := TopCat.ofHom (ContinuousMap.const C PUnit.unit)
  have wf : f ≫ b = a ≫ 𝟙 P := by ext x
  have wg : g ≫ c = a ≫ 𝟙 P := by ext x
  let ea : ContinuousMap.HomotopyEquiv A P :=
    Classical.choice (ContractibleSpace.hequiv A P)
  let eb : ContinuousMap.HomotopyEquiv B P :=
    Classical.choice (ContractibleSpace.hequiv B P)
  let ec : ContinuousMap.HomotopyEquiv C P :=
    Classical.choice (ContractibleSpace.hequiv C P)
  have ha : ea.toFun = a.hom := by ext x
  have hb : eb.toFun = b.hom := by ext x
  have hc : ec.toFun = c.hom := by ext x
  let E := mapHomotopyEquiv sq sqP a b c wf wg ea ha eb hb ec hc
  let : ContractibleSpace ((P ⊗ TopCat.I : TopCat.{u}) : Type u) := by
    change ContractibleSpace (P × TopCat.I)
    apply (contractible_iff_id_nullhomotopic _).mpr
    refine ⟨(PUnit.unit, (0 : TopCat.I)), ⟨{
      toFun := fun z ↦ (z.2.1, ULift.up (unitInterval.symm z.1 * z.2.2.down))
      continuous_toFun := by fun_prop
      map_zero_left := ?_
      map_one_left := ?_ }⟩⟩
    · intro z
      apply Prod.ext
      · rfl
      · change ULift.up (unitInterval.symm (0 : unitInterval) * z.2.down) = z.2
        simp only [unitInterval.symm_zero, one_mul]
        rfl
    · intro z
      apply Prod.ext (Subsingleton.elim _ _)
      change ULift.up (unitInterval.symm (1 : unitInterval) * z.2.down) = (0 : TopCat.I)
      simp only [unitInterval.symm_one, zero_mul]
      rfl
  exact E.contractibleSpace

include hA hB hC f g sq in
/-- Every map from the original finite cube boundary extends with literal
boundary equality. In particular, any specified constant tip faces are retained. -/
theorem exists_extend_boundary_of_contractible (n : ℕ)
    (a : C(CubicalTests.boundary.{u} n, D)) :
    ∃ c : C(CubicalTests.cube.{u} n, D),
      c.comp (CubicalTests.boundaryInclusion n).hom = a := by
  let : ContractibleSpace D := contractibleSpace_of_contractible f g sq
  exact CubicalTests.exists_extend_boundary
    (fun x k ↦ subsingleton_pi_of_contractible k D x) n a

end TopCat.DoubleCylinder
