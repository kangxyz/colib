/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.FirstObstruction
public import Colib.Algebra.Homology.DerivedCategory.AdjunctionExtFirstObstructionNaturality
public import Colib.CategoryTheory.Sites.Cohomology.RestrictionSourceNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

/-! # Actual ordinary cohomology and the first right-direct-image obstruction -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Cohomology/Ordinary/FirstObstructionNaturality.lean
Source blob `9ff52fac33a452ae7966a65a5fd2e7cf5408a094`.
Actual native objects, original ordinary Ext, and displayed maps are retained.
The degree window is strictly lower where specified. No current-degree HI is
added to a final strict-invariance statement.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
variable {S T : Scheme.{u}} (b : T ⟶ S)
  [HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]

omit [HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})] in
/-- The constructed section obstruction commutes with the original restriction map. -/
theorem ordinaryFirstObstruction_naturality {V W : EtaleSeparatedFiniteType S} (a : V ⟶ W)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ)
    (x : (cohomologyPresheaf.{u + 1, u + 1} F N).obj (Opposite.op ((baseChange b).obj W))) :
    ordinaryFirstObstruction b V F N
        ((cohomologyPresheaf.{u + 1, u + 1} F N).map
          ((baseChange b).map a).op x) =
      (((directImage b).rightDerived N).obj F).obj.map a.op
        (ordinaryFirstObstruction b W F N x) := by
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
  simp only [ordinaryFirstObstruction, sectionsAddEquiv_apply]
  rw [← sectionsEquiv_naturality_left]
  congr 1
  rw [← (imageAdjunction b).extFirstObstruction_naturality]
  congr 1
  change (Ext.mk₀ (inverseImageSourceIso b V).hom).comp
    ((Ext.mk₀ ((freeYoneda.{u + 1} (nisnevichTopology T)).map
      ((baseChange b).map a))).comp x (zero_add N)) (zero_add N) =
    (Ext.mk₀ ((inverseImage b).map
      ((freeYoneda.{u + 1} (nisnevichTopology S)).map a))).comp
        ((Ext.mk₀ (inverseImageSourceIso b W).hom).comp x (zero_add N)) (zero_add N)
  rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add N) (by omega), Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add N) (by omega), Ext.mk₀_comp_mk₀]
  congr 2
  exact (restrictionSourceIso_naturality.{u + 1}
    (nisnevichTopology S) (nisnevichTopology T) (baseChange b) a).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
