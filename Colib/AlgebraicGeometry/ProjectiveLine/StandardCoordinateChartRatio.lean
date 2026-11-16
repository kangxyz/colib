/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateSection
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCharts
public import Colib.AlgebraicGeometry.ProjectiveLine.StandardChartPolynomial

/-! # Homogeneous coordinate ratios on the relative standard opens -/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.TwistPullbackPinned
open Stacks.AmpleProjectiveImmersion Stacks.SectionsToProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual homogeneous coordinate in the native space of global sections. -/
def coordinateSectionTop (S : Scheme.{u}) (i : Fin 2) :
    Γ(twistOver 1 S 1, ⊤) :=
  pullbackCoordSection (projectiveSpaceOver.toIntegralAtUniverse 1 S) i

/-- The relative coordinate section is the original pulled back integral section. -/
theorem coordinateSection_eq_sectionsOfTop (S : Scheme.{u}) (i : Fin 2) :
    coordinateSection S i =
      Stacks.SheafOfModules.sectionsOfTop (twistOver 1 S 1) (coordinateSectionTop S i) := by
  unfold coordinateSection coordinateSectionTop pullbackCoordSection
  apply congrArg (Stacks.SheafOfModules.sectionsOfTop (twistOver 1 S 1))
  exact (pullbackSectionOn_top _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- On the relative chart `D₊(Tᵢ)`, the section `Tⱼ` is `Tⱼ/Tᵢ` times `Tᵢ`. -/
theorem coordinateSectionTop_res_eq (S : Scheme.{u}) (i j : Fin 2) :
    let f := projectiveSpaceOver.toIntegralAtUniverse 1 S
    let D := Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i)
    let U := f ⁻¹ᵁ D
    (twistOver 1 S 1).presheaf.map (homOfLE (le_top (a := U))).op
        (coordinateSectionTop S j) =
      f.app D ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X i)).hom
          (coordFrac.{u} i j)) •
        (twistOver 1 S 1).presheaf.map (homOfLE (le_top (a := U))).op
          (coordinateSectionTop S i) := by
  let f := projectiveSpaceOver.toIntegralAtUniverse 1 S
  let D := Proj.basicOpen (coordGrading.{u} 1) (MvPolynomial.X i)
  have h := congrArg (pullbackSectionOn f (twistingSheafAtUniverse.{u} 1) D)
    (coordGlobalSection_res_eq.{u} 1 i j)
  let z := (Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X i)).hom
    (coordFrac.{u} i j)
  let s (k : Fin 2) := (twistingSheafAtUniverse.{u} 1).presheaf.map
    (homOfLE (le_top (a := D))).op (coordGlobalSection.{u} 1 k)
  have hh := h.trans (pullbackSectionOn_smul f (twistingSheafAtUniverse.{u} 1) D z (s i))
  exact (pullbackGlobalSections_res f (twistingSheafAtUniverse.{u} 1) D
    (coordGlobalSection.{u} 1 j)).symm.trans (hh.trans (congrArg (f.app D z • ·)
      (pullbackGlobalSections_res f (twistingSheafAtUniverse.{u} 1) D
        (coordGlobalSection.{u} 1 i))))

/-- The coordinate defining a relative standard open is a basis at every point of that open. -/
theorem mem_nonvanishingLocus_coordinateSectionTop (S : Scheme.{u}) (i : Fin 2)
    {x : projectiveSpaceOver 1 S} (hx : x ∈ standardChart S i) :
    x ∈ Stacks.Ample.nonvanishingLocus (twistOver 1 S 1) (coordinateSectionTop S i) := by
  let f := projectiveSpaceOver.toIntegralAtUniverse 1 S
  exact mem_nonvanishingLocus_pullbackGlobalSections f (twistingSheafAtUniverse.{u} 1)
    (coordGlobalSection.{u} 1 i) (mem_nonvanishingLocus_coordGlobalSection i hx)

end AlgebraicGeometry.Scheme.ProjectiveLine
