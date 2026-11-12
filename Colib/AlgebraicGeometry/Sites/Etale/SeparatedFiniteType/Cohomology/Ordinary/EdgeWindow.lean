/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.EdgeMap
public import Colib.Algebra.Homology.DerivedCategory.AdjunctionExtEdgeInjective

/-! # Actual ordinary edge isomorphisms from finite right-direct-image vanishing -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Cohomology/Ordinary/EdgeWindow.lean
Source blob `43552f7e369acd10ec0ed9eee7a788e3d89ae44c`.
The canonical native objects and displayed maps are retained. Source candidate only.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {S T : Scheme.{u}} (b : T ⟶ S)
  [HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]

/-- The map is the original exact inverse-image/counit edge, not an assumed comparison. -/
theorem ordinaryEdgeMap_bijective_of_rightDerived_window (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q ≤ N → IsZero (((directImage b).rightDerived q).obj F)) :
    Function.Bijective (ordinaryEdgeMap b V F N) := by
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
  let e := (((extFunctor N).mapIso (inverseImageSourceIso b V).symm.op).app F)
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  exact he.comp ((imageAdjunction b).extEdge_bijective_of_rightDerived_window
    N (injectiveResolution F) hR)

/-- Omitting the endpoint from the finite vanishing window still gives injectivity. -/
theorem ordinaryEdgeMap_injective_of_rightDerived_window (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (N : ℕ)
    (hR : ∀ q : ℕ, 0 < q → q < N → IsZero (((directImage b).rightDerived q).obj F)) :
    Function.Injective (ordinaryEdgeMap b V F N) := by
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
  let := HasDerivedCategory.standard (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
  let e := (((extFunctor N).mapIso (inverseImageSourceIso b V).symm.op).app F)
  have he : Function.Injective e.hom := (ConcreteCategory.bijective_of_isIso e.hom).1
  exact he.comp ((imageAdjunction b).extEdge_injective_of_rightDerived_window
    N (injectiveResolution F) hR)

/-- Degree one has an empty positive lower-degree window. The actual inverse-image
and counit edge is injective without any higher-image or homotopy-invariance premise. -/
theorem ordinaryEdgeMap_one_injective (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    Function.Injective (ordinaryEdgeMap b V F 1) :=
  ordinaryEdgeMap_injective_of_rightDerived_window b V F 1
    (by intro q hq hq1; omega)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
