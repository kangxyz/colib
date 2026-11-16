/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.RootsOfUnityFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible

/-! # The roots-of-unity module sheaf is locally finite free -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Stacks.Kummer

variable {X : Scheme.{u}} {k : Type u} [Field k]
  (f : X ⟶ Spec (.of k)) (N : ℕ) [NeZero N] [NeZero (N : k)]

local instance (V : X.Etale) : HasSheafify (X.smallEtaleTopology.over V)
    (ModuleCat.{u + 1} (ZMod N)) :=
  Stacks.ConstantSheaf.hasSheafify_over_moduleCat.{u + 1, u, 0, 0}
    X.smallEtaleTopology (ZMod N) V

include f in
/-- The actual rank-one cyclotomic trivialization witnesses local finite freeness of μ_N. -/
theorem locallyFiniteFree_rootsOfUnityModule :
    Stacks.ConstantSheaf.IsLocallyConstantWith (ZMod N) X.smallEtaleTopology
      (fun E : ModuleCat.{u + 1} (ZMod N) => Module.Free (ZMod N) E ∧ Module.Finite (ZMod N) E)
      (rootsOfUnityModule.{u, 0} X N) := by
  intro U
  refine ⟨PUnit, fun _ => cyclotomicBaseChange f N U,
    fun _ => cyclotomicBaseChangeπ f N U, ?_, fun _ => ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨PUnit.unit, by
      rw [range_cyclotomicBaseChangeπ]; trivial⟩
  · refine ⟨ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)),
      ⟨inferInstance, inferInstance⟩, ?_⟩
    exact ⟨sliceRootSheafIso.{u, 0} (cyclotomicBaseChange f N U)
      (cyclotomicBaseChangeStructMap f N U) (IsCyclotomicExtension.zeta_spec N k _)⟩

end Stacks.Kummer
