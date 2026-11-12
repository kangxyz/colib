/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Ordinary.DerivedSections
public import Colib.Algebra.Homology.DerivedCategory.Ext.RightDerivedSourceNaturality

/-! # Original restriction maps in the ordinary derived-section comparison -/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
https://github.com/kangxyz/motivic/blob/a6805c4a87cdfd7717dd7a94039246a167f15380/Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Cohomology/Ordinary/DerivedSectionsNaturality.lean
Source blob `b04cae0f933d61c6c09ac9ae8490bbb747c42a19`.
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
variable {S T : Scheme.{u}} (b : T ⟶ S) {V W : EtaleSeparatedFiniteType S} (f : V ⟶ W)

/-- Restriction uses the original geometric base-change morphism. -/
def pulledBackNeighborhoodSectionsMap :
    pulledBackNeighborhoodSections b W ⟶ pulledBackNeighborhoodSections b V :=
  Functor.whiskerLeft (sheafToPresheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    ((CategoryTheory.evaluation _ _).map ((baseChange b).map f).op)

/-- The explicit representing equivalences respect the original restriction maps. -/
@[reassoc]
theorem pulledBackNeighborhoodSectionsRepresented_naturality :
    preadditiveCoyoneda.map
        (((freeYoneda.{u + 1} (nisnevichTopology T)).map
          ((baseChange b).map f)).op) ≫ (pulledBackNeighborhoodSectionsRepresented b V).hom =
      (pulledBackNeighborhoodSectionsRepresented b W).hom ≫
        pulledBackNeighborhoodSectionsMap b f := by
  ext F h
  exact sectionsEquiv_naturality_left
    ((baseChange b).map f) F h

/-- Taking right derived functors preserves the actual section-representation square. -/
@[reassoc]
theorem pulledBackNeighborhoodDerivedSectionsRepresented_naturality (n : ℕ) :
    NatTrans.rightDerived (preadditiveCoyoneda.map
        (((freeYoneda.{u + 1} (nisnevichTopology T)).map
          ((baseChange b).map f)).op)) n ≫
        (pulledBackNeighborhoodDerivedSectionsRepresented b V n).hom =
      (pulledBackNeighborhoodDerivedSectionsRepresented b W n).hom ≫
        NatTrans.rightDerived (pulledBackNeighborhoodSectionsMap b f) n := by
  dsimp only [pulledBackNeighborhoodDerivedSectionsRepresented]
  rw [← NatTrans.rightDerived_comp, pulledBackNeighborhoodSectionsRepresented_naturality,
    NatTrans.rightDerived_comp]

/-- Elementwise form with no Ext expression exposed during elaboration. -/
theorem pulledBackNeighborhoodDerivedSectionsRepresented_naturality_apply (n : ℕ)
    (F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})
    (y : ((preadditiveCoyoneda.obj
      (Opposite.op ((freeYoneda.{u + 1} (nisnevichTopology T)).obj
        ((baseChange b).obj W)))).rightDerived n).obj F) :
    ((pulledBackNeighborhoodDerivedSectionsRepresented b V n).app F).addCommGroupIsoToAddEquiv
      ((NatTrans.rightDerived (preadditiveCoyoneda.map
        (((freeYoneda.{u + 1} (nisnevichTopology T)).map
          ((baseChange b).map f)).op)) n).app F y) =
      (NatTrans.rightDerived (pulledBackNeighborhoodSectionsMap b f) n).app F
        (((pulledBackNeighborhoodDerivedSectionsRepresented b W n).app
          F).addCommGroupIsoToAddEquiv y) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (pulledBackNeighborhoodDerivedSectionsRepresented_naturality b f n) F) y

attribute [local irreducible] InjectiveResolution.extRightDerivedAddEquiv

variable [HasExt.{u + 1} (Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1})]
  {F : Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1}} (I : InjectiveResolution F)

/-- Original ordinary cohomology restriction matches the actual derived section map. -/
theorem ordinaryNeighborhoodDerivedSections_naturality_left (n : ℕ)
    (x : Abelian.Ext.{u + 1}
      ((freeYoneda.{u + 1} (nisnevichTopology T)).obj ((baseChange b).obj W)) F n) :
    ordinaryNeighborhoodDerivedSections b V I n
      ((cohomologyPresheaf.{u + 1, u + 1} F n).map
        ((baseChange b).map f).op x) =
      (NatTrans.rightDerived (pulledBackNeighborhoodSectionsMap b f) n).app F
        (ordinaryNeighborhoodDerivedSections b W I n x) := by
  dsimp only [ordinaryNeighborhoodDerivedSections, AddEquiv.trans_apply]
  rw [cohomologyPresheaf_map_apply]
  erw [InjectiveResolution.extRightDerivedAddEquiv_naturality_left
    (X := ((freeYoneda.{u + 1} (nisnevichTopology T)).obj ((baseChange b).obj W))) (I := I) (n := n)
    ((freeYoneda.{u + 1} (nisnevichTopology T)).map
      ((baseChange b).map f)) x]
  convert! pulledBackNeighborhoodDerivedSectionsRepresented_naturality_apply b f n F
    (I.extRightDerivedAddEquiv
      (((freeYoneda.{u + 1} (nisnevichTopology T)).obj ((baseChange b).obj W))) n x) using 1

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
