/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.FilteredHomology
public import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE

/-! # Original ordinary Ext and actual right-derived neighborhood sections -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Cohomology/Ordinary/DerivedSections.lean
Source blob `171b95a65abaf5be9f0e9f4289436a0161750f04`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE
variable {S T : Scheme.{u}} (b : T ⟶ S) (V : EtaleSeparatedFiniteType S)

/-- The original free abelian sheaf represents actual pulled-back neighborhood sections. -/
def pulledBackNeighborhoodSectionsRepresented :
    preadditiveCoyoneda.obj (Opposite.op
      (((freeYoneda.{u + 1} (nisnevichTopology T)).obj ((baseChange b).obj V)))) ≅
      pulledBackNeighborhoodSections b V :=
  NatIso.ofComponents (fun F =>
    (sectionsAddEquiv
      ((baseChange b).obj V) F).toAddCommGrpIso) (by
    intro F G f
    ext h
    exact sectionsEquiv_naturality ((baseChange b).obj V) h f)

/-- The explicit representing equivalence induces an isomorphism of derived section functors. -/
def pulledBackNeighborhoodDerivedSectionsRepresented (n : ℕ) :
    (preadditiveCoyoneda.obj (Opposite.op
      (((freeYoneda.{u + 1} (nisnevichTopology T)).obj ((baseChange b).obj V))))).rightDerived n ≅
      (pulledBackNeighborhoodSections b V).rightDerived n where
  hom := NatTrans.rightDerived (pulledBackNeighborhoodSectionsRepresented b V).hom n
  inv := NatTrans.rightDerived (pulledBackNeighborhoodSectionsRepresented b V).inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, Iso.hom_inv_id,
    NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, Iso.inv_hom_id,
    NatTrans.rightDerived_id]

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]
  {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)

/-- Original ordinary cohomology, not a replacement theory, computes actual derived sections. -/
def ordinaryNeighborhoodDerivedSections (n : ℕ) :
    Abelian.Ext.{u + 1}
      ((freeYoneda.{u + 1} (nisnevichTopology T)).obj ((baseChange b).obj V)) F n ≃+
        (((pulledBackNeighborhoodSections b V).rightDerived n).obj F) :=
  (I.extRightDerivedAddEquiv
    (((freeYoneda.{u + 1} (nisnevichTopology T)).obj ((baseChange b).obj V))) n).trans
    ((pulledBackNeighborhoodDerivedSectionsRepresented b V n).app F).addCommGroupIsoToAddEquiv

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
