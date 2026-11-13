/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Point.Marked.NeighborhoodSlice
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Cohomology.Cylinder.FiberComparison

/-! # Marked higher-image fibers are cylinder germs on the actual test object -/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/A1/LocalVanishing/Cylinder/MarkedComparison.lean`, blob
`c8b7a667ce17c4f8cea2b548e1d3628e9aab507b`.
Native mathematical objects, original coefficient universes, and actual displayed maps are retained.

-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
open Stacks.Cohomology.FreeYonedaUnivLE

/-- Composition into the original smooth site preserves the underlying schemes
and arrows; only associativity of their structure maps is transported. -/
def composeObjectToSmoothIso {B : Scheme.{u}} (X : SmoothSite B)
    (V : EtaleSeparatedFiniteType X.left) :
    composeObjectFunctor V ⋙ toSmoothSite X ≅ toSmoothSite ((toSmoothSite X).obj V) :=
  NatIso.ofComponents (fun W => MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ (W.hom ≫ (V.hom ≫ X.hom)) = (W.hom ≫ V.hom) ≫ X.hom
    simp only [Category.id_comp, Category.assoc])) (fun f => by
      apply MorphismProperty.Over.Hom.ext
      exact (Category.comp_id f.left).trans (Category.id_comp f.left).symm)

variable (R : CommRingCat.{u}) (X : SmoothSite (Spec R))
  (V : EtaleSeparatedFiniteType X.left) (z : V.left)

/-- Every actual marked test point is computed by its own original smooth
neighborhood cylinders, with its entire residue field retained. -/
def markedCylinderColimitIso
    (P : (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    colimit (pointedCylinderValues R (X := (toSmoothSite X).obj V) (residuePoint V.left z) P
      (pointedBase R (X := (toSmoothSite X).obj V) (residuePoint V.left z))) ≅
    colimit (pointedCylinderValues R (X := X) (markedResiduePoint V z) P
      (pointedBase R (X := X) (markedResiduePoint V z))) :=
  (residuePoint V.left z).presheafFiber.mapIso
    (Functor.isoWhiskerRight (NatIso.op (Functor.isoWhiskerRight
      (composeObjectToSmoothIso X V) (SmoothSite.Contraction.affineLineCylinder))) P) ≪≫
    markedResidueFiberIso V z
      ((toSmoothSite X ⋙ SmoothSite.Contraction.affineLineCylinder).op ⋙ P)

variable
  (F : Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec R)) AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1}
    (Sheaf (nisnevichTopology (SmoothSite.Contraction.affineLineCylinder.obj X).left)
      AddCommGrpCat.{u + 1})]

/-- The original higher direct image on the fixed base is detected at every
marked test point by cylinder cohomology over that very test object. -/
def markedCylinderColimitFiberIso (n : ℕ) :
    colimit (pointedCylinderValues R (X := (toSmoothSite X).obj V) (residuePoint V.left z)
      (cohomologyPresheaf.{u + 1, u + 1} F n)
      (pointedBase R (X := (toSmoothSite X).obj V) (residuePoint V.left z))) ≅
      (markedResiduePoint V z).sheafFiber.obj
        (((directImage (((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject
          (Spec R))).app X)).left).rightDerived n).obj
          ((restrict (SmoothSite.Contraction.affineLineCylinder.obj X) AddCommGrpCat).obj F)) :=
  markedCylinderColimitIso R X V z _ ≪≫
    pointedCylinderColimitFiberIso R X (markedResiduePoint V z) F n

/-- Zero cylinder germs on the original smooth test object kill its actual
marked higher-image fiber. This requires no derived étale base-change theorem. -/
theorem markedProjectionFiber_isZero_of_cylinderColimit (n : ℕ)
    (h : IsZero (colimit (pointedCylinderValues R
      (X := (toSmoothSite X).obj V) (residuePoint V.left z)
      (cohomologyPresheaf.{u + 1, u + 1} F n)
      (pointedBase R (X := (toSmoothSite X).obj V) (residuePoint V.left z))))) :
    IsZero ((markedResiduePoint V z).sheafFiber.obj
      (((directImage (((SmoothSite.Contraction.projection (SmoothSite.additiveGroupObject (Spec
        R))).app X)).left).rightDerived n).obj
        ((restrict (SmoothSite.Contraction.affineLineCylinder.obj X) AddCommGrpCat).obj F))) :=
  h.of_iso (markedCylinderColimitFiberIso R X V z F n).symm

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
