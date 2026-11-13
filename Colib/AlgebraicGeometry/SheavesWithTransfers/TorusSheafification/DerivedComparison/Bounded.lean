/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.Single
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
import StacksFrontier.Algebra.Homology.DerivedCategory.LeftDerivedOfExactFunctor
import StacksFrontier.Algebra.Homology.DerivedCategory.RightTExactCohomologyClass
import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds

/-!
# The derived torus comparison on bounded-below inputs

In each degree the comparison can be tested on one cohomology coefficient.
The two truncation triangles give these tests using the lower bound for the
total derived functor and the upper bound on a finite A¹-invariant interval.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers

variable (k : Type u) [Field k]

variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

/-- Canonical truncation from below preserves A¹-invariance of the
cohomology presheaves. -/
theorem isA1Invariant_derivedHomology_truncGE
    (E : DerivedCategory (PresheafWithTransfers.{u + 1} k))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E).IsA1Invariant) (a i : ℤ) :
    ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.TStructure.t.truncGE a).obj E)).IsA1Invariant :=
  Stacks.SmallDerivedCategory.prop_homologyFunctor_truncGE_obj
    (a1InvariantProperty k) E hE a i

variable [PerfectField k]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

set_option maxHeartbeats 600000 in
-- Both triangles are mapped through the exact and the total derived functors.
/-- The original derived comparison is an isomorphism on every bounded-below
complex with A¹-invariant cohomology presheaves. -/
theorem isIso_torusSectionsDerivedSheafificationComparison_app_of_isGE
    (E : DerivedCategory (PresheafWithTransfers.{u + 1} k))
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj E).IsA1Invariant)
    (a : ℤ) [E.IsGE a] :
    IsIso ((torusSectionsDerivedSheafificationComparison k).app E) := by
  let T := torusSectionsPresheafFunctor k
  let A := nisnevichSheafify k
  let R := torusSectionsDerivedFunctor k
  let F₁ := T.mapDerivedCategory ⋙ A.mapDerivedCategory
  let F₂ := A.mapDerivedCategory ⋙ R
  let η := torusSectionsDerivedSheafificationComparison k
  let t : Triangulated.TStructure (DerivedCategory (PresheafWithTransfers.{u + 1} k)) :=
    DerivedCategory.TStructure.t
  change IsIso (η.app E)
  apply (DerivedCategory.isIso_iff _ _).2
  intro i
  let H := DerivedCategory.homologyFunctor (SheafWithTransfers.{u + 1} k) i
  let L := (t.truncLE i).obj E
  let V := (t.truncGE (i + 1)).obj E
  let W := (t.truncLE (i - 1)).obj L
  let S := (t.truncGE i).obj L
  let ι : L ⟶ E := (t.truncLEι i).app E
  let π : L ⟶ S := (t.truncGEπ i).app L
  have hFirst := t.triangleLEGE_distinguished i (i + 1) rfl E
  have hSecond := t.triangleLEGE_distinguished (i - 1) i (by omega) L
  let : L.IsGE a := inferInstanceAs (((t.truncLT (i + 1)).obj E).IsGE a)
  let : V.IsGE (i + 1) := inferInstanceAs (((t.truncGE (i + 1)).obj E).IsGE (i + 1))
  let : W.IsGE a := inferInstanceAs (((t.truncLT (i - 1 + 1)).obj L).IsGE a)
  let : W.IsLE (i - 1) := inferInstanceAs (((t.truncLE (i - 1)).obj L).IsLE (i - 1))
  let : (T.mapDerivedCategory.obj V).IsGE (i + 1) :=
    DerivedCategory.isGE_mapDerivedCategory_obj T V _
  let : (A.mapDerivedCategory.obj V).IsGE (i + 1) :=
    DerivedCategory.isGE_mapDerivedCategory_obj A V _
  have hF₁V : (F₁.obj V).IsGE (i + 1) := DerivedCategory.isGE_mapDerivedCategory_obj A _ _
  have hF₂V : (F₂.obj V).IsGE (i + 1) := torusSectionsDerived_isGE k _ _
  let : IsIso (H.map (F₁.map ι)) := DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _
    (F₁.map_distinguished _ hFirst) i (i + 1) hF₁V (by omega)
  let : IsIso (H.map (F₂.map ι)) := DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _
    (F₂.map_distinguished _ hFirst) i (i + 1) hF₂V (by omega)
  let : (T.mapDerivedCategory.obj W).IsLE (i - 1) :=
    Stacks.Homology.isLE_mapDerivedCategory_obj T W _
  let : (A.mapDerivedCategory.obj W).IsLE (i - 1) :=
    Stacks.Homology.isLE_mapDerivedCategory_obj A W _
  let : (A.mapDerivedCategory.obj W).IsGE a :=
    DerivedCategory.isGE_mapDerivedCategory_obj A W a
  have hF₁W : (F₁.obj W).IsLE (i - 1) :=
    Stacks.Homology.isLE_mapDerivedCategory_obj A _ _
  have hF₂W : (F₂.obj W).IsLE (i - 1) :=
    torusSectionsDerived_isLE_of_isGE_of_isLE k (A.mapDerivedCategory.obj W) a (i - 1) (by
      intro j
      let P := a1InvariantProperty k
      have hL : ∀ n : ℤ, P ((DerivedCategory.homologyFunctor _ n).obj L) :=
        Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj P E hE i
      have hW := Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj P L hL (i - 1) j
      let e := (SheafWithTransfers.forget k).mapIso ((A.mapDerivedCategoryHomologyIso j).app W)
      exact P.prop_of_iso e.symm (nisnevichSheafify_isA1Invariant _ hW))
  let : IsIso (H.map (F₁.map π)) := DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _
    (F₁.map_distinguished _ hSecond) i (i - 1) hF₁W (by omega)
  let : IsIso (H.map (F₂.map π)) := DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _
    (F₂.map_distinguished _ hSecond) i (i - 1) hF₂W (by omega)
  let eS : S ≅ (DerivedCategory.singleFunctor _ i).obj
      ((DerivedCategory.homologyFunctor _ i).obj E) :=
    (DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor i).app E
  let : IsIso (η.app S) := (NatTrans.isIso_app_iff_of_iso η eS).2
    (isIso_torusSectionsDerivedSheafificationComparison_app_single k _ (hE i) i)
  let : IsIso (H.map (η.app L) ≫ H.map (F₂.map π)) := by
    rw [← Functor.map_comp, ← η.naturality π, Functor.map_comp]
    infer_instance
  let : IsIso (H.map (η.app L)) := IsIso.of_isIso_comp_right _ (H.map (F₂.map π))
  let : IsIso (H.map (F₁.map ι) ≫ H.map (η.app E)) := by
    rw [← Functor.map_comp, η.naturality ι, Functor.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (H.map (F₁.map ι)) _

end AlgebraicGeometry.SheafWithTransfers
