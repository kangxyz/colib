/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightTExactCohomologyClass
import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# Lower truncation under an exact functor

The actual image of the lower truncation projection is again a lower
truncation projection. Its comparison is determined by the universal
property and tested by the cohomology of the original projection.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe w w' v v' u u'

namespace CategoryTheory.Functor

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The canonical map from truncating the image to the image of the
truncation. -/
def mapDerivedCategoryTruncGEHom (X : DerivedCategory A) (a : ℤ) :
    (DerivedCategory.TStructure.t.truncGE a).obj (F.mapDerivedCategory.obj X) ⟶
      F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncGE a).obj X) := by
  let : (F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncGE a).obj X)).IsGE a :=
    DerivedCategory.isGE_mapDerivedCategory_obj F _ a
  exact DerivedCategory.TStructure.t.descTruncGE
    (F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ a).app X)) a

/-- The canonical map carries the truncation projection to its actual image. -/
@[reassoc]
theorem truncGEπ_app_comp_mapDerivedCategoryTruncGEHom (X : DerivedCategory A) (a : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ a).app (F.mapDerivedCategory.obj X) ≫
        F.mapDerivedCategoryTruncGEHom X a =
      F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ a).app X) := by
  let : (F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncGE a).obj X)).IsGE a :=
    DerivedCategory.isGE_mapDerivedCategory_obj F _ a
  exact DerivedCategory.TStructure.t.π_descTruncGE
    (F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ a).app X)) a

instance (X : DerivedCategory A) (a : ℤ) :
    IsIso (F.mapDerivedCategoryTruncGEHom X a) := by
  refine (DerivedCategory.isIso_iff _ _).2 fun i => ?_
  let H := DerivedCategory.homologyFunctor B i
  let X' := F.mapDerivedCategory.obj X
  let L := (DerivedCategory.TStructure.t.truncGE a).obj X'
  let L' := F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncGE a).obj X)
  let π := (DerivedCategory.TStructure.t.truncGEπ a).app X'
  let π' := (DerivedCategory.TStructure.t.truncGEπ a).app X
  let : L.IsGE a := inferInstanceAs
    (((DerivedCategory.TStructure.t.truncGE a).obj X').IsGE a)
  let : L'.IsGE a := DerivedCategory.isGE_mapDerivedCategory_obj F _ a
  by_cases hi : i < a
  · exact (DerivedCategory.isZero_of_isGE L a i hi).isIso
      (DerivedCategory.isZero_of_isGE L' a i hi) _
  · let : IsIso (H.map π) :=
      DerivedCategory.isIso_homologyFunctor_map_truncGEπ a i (by omega) X'
    let : IsIso ((DerivedCategory.homologyFunctor A i).map π') :=
      DerivedCategory.isIso_homologyFunctor_map_truncGEπ a i (by omega) X
    let : IsIso (H.map (F.mapDerivedCategory.map π')) :=
      (F.isIso_homologyFunctor_map_mapDerivedCategory_map_iff π' i).2 inferInstance
    let : IsIso (H.map π ≫ H.map (F.mapDerivedCategoryTruncGEHom X a)) := by
      rw [← Functor.map_comp]
      change IsIso (H.map (_ ≫ F.mapDerivedCategoryTruncGEHom X a))
      rw [F.truncGEπ_app_comp_mapDerivedCategoryTruncGEHom]
      infer_instance
    exact IsIso.of_isIso_comp_left (H.map π) _

/-- The canonical comparison between the two actual truncations. -/
def mapDerivedCategoryTruncGEIso (X : DerivedCategory A) (a : ℤ) :
    (DerivedCategory.TStructure.t.truncGE a).obj (F.mapDerivedCategory.obj X) ≅
      F.mapDerivedCategory.obj ((DerivedCategory.TStructure.t.truncGE a).obj X) :=
  asIso (F.mapDerivedCategoryTruncGEHom X a)

/-- The comparison isomorphism has the original projection as its
precomposition. -/
@[reassoc]
theorem truncGEπ_app_comp_mapDerivedCategoryTruncGEIso_hom (X : DerivedCategory A) (a : ℤ) :
    (DerivedCategory.TStructure.t.truncGEπ a).app (F.mapDerivedCategory.obj X) ≫
        (F.mapDerivedCategoryTruncGEIso X a).hom =
      F.mapDerivedCategory.map ((DerivedCategory.TStructure.t.truncGEπ a).app X) :=
  F.truncGEπ_app_comp_mapDerivedCategoryTruncGEHom X a

end CategoryTheory.Functor
