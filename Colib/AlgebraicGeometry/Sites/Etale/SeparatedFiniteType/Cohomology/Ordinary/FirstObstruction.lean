/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.EdgeMap
public import Colib.Algebra.Homology.DerivedCategory.AdjunctionExtFirstObstruction

/-! # Actual ordinary cohomology and the first right-direct-image obstruction -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Cohomology/Ordinary/FirstObstruction.lean
Source blob `f488b921a4684349fecf4aa01a893f8cfeab7e5a`.
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

/-- The obstruction is a section of the actual right-direct-image sheaf on the actual test. -/
def ordinaryFirstObstruction (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ)
    (x : (cohomologyPresheaf.{u + 1, u + 1} F N).obj (Opposite.op ((baseChange b).obj V))) :
    (((directImage b).rightDerived N).obj F).obj.obj (Opposite.op V) := by
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
  let e := (((extFunctor N).mapIso (inverseImageSourceIso b V).symm.op).app F)
  exact sectionsAddEquiv.{u + 1} V _
    ((imageAdjunction b).extFirstObstruction (injectiveResolution F) _ N (e.inv x))

/-- Exactness at ordinary degree N under only the lower positive vanishing window. -/
theorem ordinaryFirstObstruction_eq_zero_iff (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ) (hN : 0 < N)
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero (((directImage b).rightDerived q).obj F))
    (x : (cohomologyPresheaf.{u + 1, u + 1} F N).obj (Opposite.op ((baseChange b).obj V))) :
    ordinaryFirstObstruction b V F N x = 0 ↔
      ∃ z, ordinaryEdgeMap b V F N z = x := by
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
  let e := (((extFunctor N).mapIso (inverseImageSourceIso b V).symm.op).app F)
  change sectionsAddEquiv.{u + 1} V _
    ((imageAdjunction b).extFirstObstruction (injectiveResolution F) _ N (e.inv x)) = 0 ↔ _
  rw [AddEquiv.map_eq_zero_iff,
    (imageAdjunction b).extFirstObstruction_eq_zero_iff _ _ N hN hR]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change e.hom ((imageAdjunction b).extEdge N z) = x
    rw [hz]
    exact ConcreteCategory.congr_hom e.inv_hom_id x
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso e.hom).1
    change e.hom ((imageAdjunction b).extEdge N z) = e.hom (e.inv x)
    exact hz.trans (ConcreteCategory.congr_hom e.inv_hom_id x).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
