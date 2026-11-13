/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsDerived.Effective
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle
import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds

/-!
# Natural cohomology comparison for effective torus sections

In degree `i`, the canonical maps of the two adjacent truncation
triangles identify cohomology of total derived torus sections with
ordinary torus sections of the original cohomology coefficient.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme

universe w w' u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

private abbrev invariantSheafProperty : ObjectProperty (SheafWithTransfers.{u + 1} k) :=
  (a1InvariantProperty k).inverseImage (SheafWithTransfers.forget k)

/-- Complexes with A¹-invariant actual transfer cohomology. -/
abbrev a1InvariantCohomology : ObjectProperty (DerivedCategory (SheafWithTransfers.{u + 1} k)) :=
  fun K => ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj K).obj.IsA1Invariant

/-- The cohomology comparison is natural on any diagram whose cohomology
sheaves are A¹-invariant. Only the lower of the two adjacent truncation
terms needs a cohomological upper bound. -/
@[no_expose]
def torusSectionsDerivedHomologyNatIso
    (i : ℤ) :
    (a1InvariantCohomology k).ι ⋙
        (torusSectionsDerivedFunctor k ⋙ DerivedCategory.homologyFunctor _ i) ≅
      (a1InvariantCohomology k).ι ⋙
        (DerivedCategory.homologyFunctor _ i ⋙ torusSectionsFunctor k) := by
  let A := SheafWithTransfers.{u + 1} k
  let t : Triangulated.TStructure (DerivedCategory A) := DerivedCategory.TStructure.t
  let R := torusSectionsDerivedFunctor k
  let B : A ⥤ A := torusSectionsFunctor k
  let H := DerivedCategory.homologyFunctor A i
  let F := (a1InvariantCohomology k).ι
  let E := R ⋙ H
  let L := t.truncLE i
  let P := t.truncGE i
  let ι : F ⋙ (L ⋙ E) ⟶ F ⋙ E :=
    Functor.whiskerLeft F (Functor.whiskerRight (t.truncLEι i) E) ≫
      Functor.whiskerLeft F E.leftUnitor.hom
  let π : F ⋙ (L ⋙ E) ⟶ F ⋙ ((L ⋙ P) ⋙ E) :=
    (Functor.isoWhiskerLeft F (Functor.isoWhiskerRight L.rightUnitor E)).inv ≫
      Functor.whiskerLeft F (Functor.whiskerRight
        (Functor.whiskerLeft L (t.truncGEπ i)) E)
  let : IsIso ι := (NatTrans.isIso_iff_isIso_app ι).2 (fun X => by
    let K := F.obj X
    let V := (t.truncGE (i + 1)).obj K
    let : V.IsGE (i + 1) := inferInstanceAs (((t.truncGE (i + 1)).obj K).IsGE (i + 1))
    have hV : (R.obj V).IsGE (i + 1) := torusSectionsDerived_isGE k V _
    change IsIso (H.map (R.map ((t.truncLEι i).app K)) ≫ 𝟙 _)
    rw [Category.comp_id]
    exact DerivedCategory.isIso_homologyMap_mor₁_of_isGE₃ _
      (R.map_distinguished _ (t.triangleLEGE_distinguished i (i + 1) rfl K))
      i (i + 1) hV (by omega))
  let : IsIso π := (NatTrans.isIso_iff_isIso_app π).2 (fun X => by
    let K := F.obj X
    let K₁ := L.obj K
    let W := (t.truncLE (i - 1)).obj K₁
    let : W.IsLE (i - 1) := inferInstanceAs (((t.truncLE (i - 1)).obj K₁).IsLE (i - 1))
    let I := invariantSheafProperty k
    have h₁ : ∀ j, I ((DerivedCategory.homologyFunctor A j).obj K₁) :=
      Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj I K X.property i
    have hW : ∀ j, I ((DerivedCategory.homologyFunctor A j).obj W) :=
      Stacks.SmallDerivedCategory.prop_homologyFunctor_truncLE_obj I K₁ h₁ (i - 1)
    have hW' := torusSectionsDerived_isLE_of_isLE_of_isA1Invariant k W (i - 1) hW
    change IsIso (E.map (𝟙 K₁) ≫ H.map (R.map ((t.truncGEπ i).app K₁)))
    rw [E.map_id, Category.id_comp]
    exact DerivedCategory.isIso_homologyMap_mor₂_of_isLE₁ _
      (R.map_distinguished _ (t.triangleLEGE_distinguished (i - 1) i (by omega) K₁))
      i (i - 1) hW' (by omega))
  let e : L ⋙ P ≅ H ⋙ DerivedCategory.singleFunctor A i :=
    DerivedCategory.truncGELTIsoHomologyFunctorCompSingleFunctor i
  let α := Stacks.Injectives.homotopyUnitOfComplexUnit B R (torusSectionsDerivedUnit k)
  let e₀ : DerivedCategory.singleFunctor A i ⋙ R ⋙ H ≅ B :=
    Stacks.DerivedFunctor.singleShiftCompDerivedCompHomologyIsoRightDerived B R α
      (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A) i i 0
      (by omega) ≪≫ B.rightDerivedZeroIsoSelf
  exact (asIso ι).symm ≪≫ asIso π ≪≫
    Functor.isoWhiskerLeft F (Functor.isoWhiskerRight e E) ≪≫
    Functor.isoWhiskerLeft F
      (Functor.associator H (DerivedCategory.singleFunctor A i) E ≪≫
        Functor.isoWhiskerLeft H e₀)

end AlgebraicGeometry.SheafWithTransfers
