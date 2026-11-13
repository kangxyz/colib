/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Original.FirstObstruction
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Persistent.MarkedSection
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.FirstObstructionNaturality

/-! # First obstruction for the original big-site neighborhood restriction -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Cohomology/Original/FirstObstructionNaturality.lean
Source blob `fb6c3761c967aa6defe300bbbd1a51eee48b4a00`.
Actual native objects, original ordinary Ext, and displayed maps are retained.
The degree window is strictly lower where specified. No current-degree HI is
added to a final strict-invariance statement.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
variable {B : Scheme.{u}} {X Y : SmoothSite B} (h : Y ⟶ X)
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology Y.left) AddCommGrpCat.{u + 1})]
  (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})

omit [HasExt.{u + 1} (Sheaf (nisnevichTopology X.left) AddCommGrpCat.{u + 1})] in
/-- Original big-site restrictions commute with the actual higher-image obstruction. -/
theorem originalFirstObstruction_naturality (N : ℕ) {V W : EtaleSeparatedFiniteType X.left}
    (a : V ⟶ W)
    (α : (cohomologyPresheaf.{u + 1, u + 1} F N).obj
      (op ((toSmoothSite Y).obj ((baseChange h.left).obj W)))) :
    originalFirstObstruction h F N V
      ((cohomologyPresheaf.{u + 1, u + 1} F N).map
        ((toSmoothSite Y).map ((baseChange h.left).map a)).op α) =
      (((directImage h.left).rightDerived N).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F)).obj.map a.op
          (originalFirstObstruction h F N W α) := by
  rw [originalFirstObstruction, originalFirstObstruction,
    cohomologyRestrictionEquiv_restriction, ordinaryFirstObstruction_naturality]

/-- Persistent obstruction germs supply an original big-site restriction lift after shrinking. -/
theorem exists_open_originalRestriction_lift_of_persistent_obstruction_germs
    [IsIso (restrictionToDirectImage F h)]
    (N : ℕ) (hN : 0 < N) (V : EtaleSeparatedFiniteType X.left) [IsNoetherian V.left]
    {Z : Scheme.{u}} (g : V.left ⟶ Z) (z : Z)
    (hR : ∀ q : ℕ, 0 < q → q < N →
      IsZero (((directImage h.left).rightDerived q).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F)))
    (α : (cohomologyPresheaf.{u + 1, u + 1} F N).obj
      (op ((toSmoothSite Y).obj ((baseChange h.left).obj V))))
    (hα : ∀ y : V.left, g y ⤳ z →
      markedSectionGerm (((directImage h.left).rightDerived N).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F)).obj V y
          (originalFirstObstruction h F N V α) = 0) :
    ∃ O : Z.Opens, z ∈ O ∧ ∃ β,
      (cohomologyPresheaf.{u + 1, u + 1} F N).map
        ((restrictionProjection h).app (testOpenObject V (g ⁻¹ᵁ O))).op β =
      (cohomologyPresheaf.{u + 1, u + 1} F N).map
        ((toSmoothSite Y).map ((baseChange h.left).map
          (testOpenInclusion V (g ⁻¹ᵁ O)))).op α := by
  obtain ⟨O, hz, hO⟩ :=
    exists_open_test_restriction_eq_zero_of_persistent_marked_germs
      (((directImage h.left).rightDerived N).obj
        ((restrict Y AddCommGrpCat.{u + 1}).obj F)) V g z
          (originalFirstObstruction h F N V α) hα
  refine ⟨O, hz, ?_⟩
  apply (originalFirstObstruction_eq_zero_iff h F N hN _ hR _).mp
  rw [originalFirstObstruction_naturality]
  exact hO

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
