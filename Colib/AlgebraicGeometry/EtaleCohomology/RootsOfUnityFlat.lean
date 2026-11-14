/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleFlatTensorExact
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.PointFiber

/-!
# Flatness of the roots-of-unity module sheaf

On the small étale site of a scheme over a field in which `N` is nonzero,
`μ_N` has flat `ℤ/N`-module fibers. The proof uses the explicit cyclotomic
rank-one trivialization, lifts every site point through that cover, and applies
conservativity of enough points. Consequently, tensoring with `μ_N` is exact.

This supplies coefficient exactness for cup products. It does not assert a
higher-weight motivic comparison or the norm-residue isomorphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
universe u
namespace Stacks.Kummer

attribute [local instance] Stacks.EtaleCohomology.etaleModules_AB5OfSize
  Stacks.EtaleCohomology.etaleModules_preservesFilteredColimits_forget

variable {X : Scheme.{u}} {k : Type u} [Field k]
  (f : X ⟶ Spec (.of k)) (N : ℕ) [NeZero N] [NeZero (N : k)]

/-- Every site point has a lift to a cyclotomic base change of some étale object. -/
theorem exists_cyclotomicBaseChange_fiber
    (Φ : X.smallEtaleTopology.Point.{u + 1}) :
    ∃ U : X.Etale, Nonempty (Φ.fiber.obj (cyclotomicBaseChange f N U)) := by
  classical
  let e : Φ.fiber.Elements := Classical.choice (IsCofiltered.nonempty (C := Φ.fiber.Elements))
  let V : PUnit.{1} → X.Etale := fun _ => cyclotomicBaseChange f N e.obj
  let π : ∀ i, V i ⟶ e.obj := fun _ => cyclotomicBaseChangeπ f N e.obj
  have hc : Sieve.ofArrows V π ∈ X.smallEtaleTopology e.obj := by
    rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    exact Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨PUnit.unit, by
      rw [range_cyclotomicBaseChangeπ]; trivial⟩
  obtain ⟨W, g, hg, y, _⟩ := Φ.jointly_surjective (Sieve.ofArrows V π) hc e.val
  obtain ⟨i, a, _⟩ := (Sieve.mem_ofArrows_iff V π g).mp hg
  exact ⟨e.obj, ⟨Φ.fiber.map a y⟩⟩

include f in
/-- Actual μ_N fibers are flat, using their explicit rank-one trivialization. -/
@[colib_tag "COL-1227"]
theorem flat_sheafFiber_rootsOfUnityModule
    (Φ : X.smallEtaleTopology.Point.{u + 1}) :
    Module.Flat (ZMod N)
      ((Φ.sheafFiber (A := ModuleCat.{u + 1} (ZMod N))).obj
        (rootsOfUnityModule.{u, 0} X N)) := by
  classical
  obtain ⟨U, hx⟩ := exists_cyclotomicBaseChange_fiber f N Φ
  let x := Classical.choice hx
  have : ∀ U : X.Etale, HasSheafify (X.smallEtaleTopology.over U)
      (ModuleCat.{u + 1} (ZMod N)) := fun U =>
    Stacks.ConstantSheaf.hasSheafify_over_moduleCat.{u + 1, u, 0, 0}
      X.smallEtaleTopology (ZMod N) U
  have : ∀ U : X.Etale, (X.smallEtaleTopology.over U).WEqualsLocallyBijective
      (ModuleCat.{u + 1} (ZMod N)) := fun U =>
    Stacks.ConstantSheaf.wEqualsLocallyBijective_moduleCat.{u, u + 1, 0, 0}
      (X.smallEtaleTopology.over U) (ZMod N)
  let e := Stacks.ConstantSheaf.sheafFiberIsoOfConstantOver Φ x
    (rootsOfUnityModule.{u, 0} X N)
    (ModuleCat.of (ZMod N) (ULift.{u + 1} (ZMod N)))
    (sliceRootSheafIso.{u, 0} (cyclotomicBaseChange f N U)
      (cyclotomicBaseChangeStructMap f N U) (IsCyclotomicExtension.zeta_spec N k _))
  exact Module.Flat.of_linearEquiv e.toLinearEquiv

attribute [local instance] Sheaf.monoidalCategory
  Stacks.EtaleCohomology.isMonoidal_W_etaleModules

include f in
/-- Tensoring with `μ_N` is additive and preserves finite limits and finite colimits. -/
@[colib_tag "COL-1227",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/AlgebraicGeometry/EtaleCohomology/\
      KummerTheory/RootsOfUnityModuleSliceConstant.lean:315"
    "ingredient" "Explicit rank-one cyclotomic trivialization of roots of unity",
  colib_ref "axiom_stacks_5ed82d14"
    "StacksFrontier/CategoryTheory/Sites/Point/FlatFiberTensorExact.lean:105"
    "ingredient" "Exactness detected by flat module fibers at a conservative family of points"]
theorem exact_tensorRight_rootsOfUnityModule :
    (MonoidalCategory.tensorRight (rootsOfUnityModule.{u, 0} X N)).Additive ∧
    PreservesFiniteLimits (MonoidalCategory.tensorRight (rootsOfUnityModule.{u, 0} X N)) ∧
    PreservesFiniteColimits (MonoidalCategory.tensorRight (rootsOfUnityModule.{u, 0} X N)) := by
  have : GrothendieckTopology.HasEnoughPoints.{u + 1} X.smallEtaleTopology :=
    Scheme.hasEnoughPoints_smallEtaleTopology.{0, u} X
  obtain ⟨P, _, hP⟩ :=
    GrothendieckTopology.HasEnoughPoints.exists_objectProperty X.smallEtaleTopology
  exact hP.preservesFiniteLimits_tensorRight_of_flat (ZMod N)
    (rootsOfUnityModule.{u, 0} X N)
    (fun Φ => flat_sheafFiber_rootsOfUnityModule f N Φ.obj)

end Stacks.Kummer
end
