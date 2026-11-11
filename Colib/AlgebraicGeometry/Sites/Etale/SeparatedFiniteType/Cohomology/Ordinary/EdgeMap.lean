/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Injectives
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.ImageExact
public import Colib.CategoryTheory.Sites.Cohomology.RestrictionSource
public import Colib.Algebra.Homology.DerivedCategory.AdjunctionEdgeMap

/-! # The actual ordinary cohomology edge map of geometric base change -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Cohomology/Ordinary/EdgeMap.lean`, blob `dedbdef60cb56af8a9652506bcafe1459e2e5570`.
The canonical native objects and displayed maps are retained. Source candidate only.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
open Opposite
variable {S T : Scheme.{u}} (b : T ⟶ S)

/-- The genuine inverse image carries the original free source to the pulled-back free source. -/
def inverseImageSourceIso (V : EtaleSeparatedFiniteType S) :
    (inverseImage b).obj (((freeYoneda.{u + 1} (nisnevichTopology S)).obj V)) ≅
      ((freeYoneda.{u + 1} (nisnevichTopology T)).obj ((baseChange b).obj V)) :=
  restrictionSourceIso.{u + 1}
    (nisnevichTopology S) (nisnevichTopology T) (baseChange b) V

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]

/-- Apply the actual exact inverse image, then the actual counit, with original free sources. -/
def ordinaryEdgeMap (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) (n : ℕ) :
    (cohomologyPresheaf.{u + 1, u + 1} ((directImage b).obj F) n).obj (op V) →+
      (cohomologyPresheaf.{u + 1, u + 1} F n).obj (op ((baseChange b).obj V)) where
  toFun x := (Ext.mk₀ (inverseImageSourceIso b V).inv).comp
    ((imageAdjunction b).extEdge n x) (zero_add n)
  map_zero' := by simp
  map_add' x y := by simp

/-- The ordinary edge in degree zero is an isomorphism, without higher acyclicity inputs. -/
theorem ordinaryEdgeMap_zero_bijective (V : EtaleSeparatedFiniteType S)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}) :
    Function.Bijective (ordinaryEdgeMap b V F 0) := by
  let e := (((extFunctor 0).mapIso (inverseImageSourceIso b V).symm.op).app F)
  have he : Function.Bijective e.hom := ConcreteCategory.bijective_of_isIso e.hom
  exact he.comp ((imageAdjunction b).extEdge_zero_bijective _ F)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
