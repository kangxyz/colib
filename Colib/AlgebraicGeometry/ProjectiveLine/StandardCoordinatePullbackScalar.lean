/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardCoordinateChartScalar
public import StacksFrontier.AlgebraicGeometry.SectionProduct.PullbackUnitComparisonSection
public import Colib.AlgebraicGeometry.Modules.PerfectGlobalScalar
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic

/-! # The homogeneous section after pullback to the negative chart -/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.SectionsToProjectiveSpace Stacks.TwistPullbackPinned
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.PullbackTensorCoherence

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- The pulled-back `T₀` is the polynomial coordinate times the pulled-back frame `T₁`. -/
theorem pullbackGlobalSections_coordinateSectionTop_zero (X : QuasiCompactSchemes.{u}) :
    let U := negativeChart X.obj
    let L := twistOver 1 X.obj 1
    pullbackGlobalSections U.ι L (coordinateSectionTop X.obj 0) =
      negativeChartCoordinate X • pullbackGlobalSections U.ι L (coordinateSectionTop X.obj 1) := by
  let U := negativeChart X.obj
  let L := twistOver 1 X.obj 1
  let f := projectiveSpaceOver.toIntegralAtUniverse 1 X.obj
  let D := integralChart.{u} 1
  let r : Γ(projectiveSpaceOver 1 X.obj, U) := f.app D
    ((Proj.awayToSection (coordGrading.{u} 1) (MvPolynomial.X 1)).hom (coordFrac.{u} 1 0))
  let h : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U :=
    (Stacks.AlgebraicGeometry.ProjTwistMono.preimage_self_eq_top U).ge
  let s (k : Fin 2) : Γ(L, U) := L.presheaf.map (homOfLE (le_top (a := U))).op
    (coordinateSectionTop X.obj k)
  have hratio : s 0 = r • s 1 := coordinateSectionTop_res_eq X.obj 1 0
  have hres (k : Fin 2) :
      Scheme.Modules.pullbackSection U.ι L U ⊤ h (s k) =
        pullbackGlobalSections U.ι L (coordinateSectionTop X.obj k) := by
    have hc := pullbackGlobalSections_res U.ι L U (coordinateSectionTop X.obj k)
    change ((Scheme.Modules.pullback U.ι).obj L).presheaf.map (homOfLE h).op
      (pullbackSectionOn U.ι L U (s k)) = _
    rw [hc, ← Functor.map_comp_apply]
    have hid : (homOfLE (le_top : U.ι ⁻¹ᵁ U ≤ ⊤)).op ≫ (homOfLE h).op =
        𝟙 (op (⊤ : U.toScheme.Opens)) := Subsingleton.elim _ _
    rw [hid]
    exact Functor.map_id_apply _ _ _
  have hsmul : Scheme.Modules.pullbackSection U.ι L U ⊤ h (r • s 1) =
      U.ι.appLE U ⊤ h r • Scheme.Modules.pullbackSection U.ι L U ⊤ h (s 1) := by
    change ((Scheme.Modules.pullback U.ι).obj L).presheaf.map (homOfLE h).op
      (pullbackSectionOn U.ι L U (r • s 1)) = _
    rw [pullbackSectionOn_smul U.ι L U r (s 1), Scheme.Modules.map_smul]
    rfl
  have hs := (congrArg (Scheme.Modules.pullbackSection U.ι L U ⊤ h) hratio).trans hsmul
  have hscalar : U.ι.appLE U ⊤ h r = negativeChartCoordinate X := by
    rw [Scheme.Opens.ι_appLE]
    exact (negativeChartCoordinate_eq_chartRatio X).symm
  rw [hres 0, hres 1, hscalar] at hs
  exact hs

/-- The pullback of a coordinate, expressed as a morphism from the unit on the negative chart. -/
def negativeChartCoordinateUnitHom (X : QuasiCompactSchemes.{u}) (k : Fin 2) :
    let U := negativeChart X.obj
    SheafOfModules.unit U.toScheme.ringCatSheaf ⟶
      (Scheme.Modules.pullback U.ι).obj (twistOver 1 X.obj 1) :=
  let U := negativeChart X.obj
  (Stacks.PullbackAlgebra.pullbackUnitIso U.ι.toLRSHom.toShHom).inv ≫
    (Scheme.Modules.pullback U.ι).map (sectionHom (twistOver 1 X.obj 1)
      (coordinateSection X.obj k))

set_option backward.isDefEq.respectTransparency false in
/-- As morphisms from the unit, the pulled-back coordinates differ by the polynomial scalar. -/
theorem negativeChartCoordinateUnitHom_zero (X : QuasiCompactSchemes.{u}) :
    let U := negativeChart X.obj
    let M := (Scheme.Modules.pullback U.ι).obj (twistOver 1 X.obj 1)
    negativeChartCoordinateUnitHom X 0 =
      negativeChartCoordinateUnitHom X 1 ≫
        (Stacks.RegularSequence.globalSmulCenter U.toScheme (negativeChartCoordinate X)).app M := by
  let U := negativeChart X.obj
  let L := twistOver 1 X.obj 1
  let M := (Scheme.Modules.pullback U.ι).obj L
  apply M.unitHomEquiv.injective
  apply Stacks.SheafOfModules.sections_ext_of_eval_top M
  have heval (k : Fin 2) :
      (M.unitHomEquiv (negativeChartCoordinateUnitHom X k)).eval (op ⊤) =
        pullbackGlobalSections U.ι L (coordinateSectionTop X.obj k) := by
    have he := (Stacks.PullbackUnitComparisonSection.pullbackGlobalSections_unitHomEquiv
      U.ι L (coordinateSection X.obj k)).symm
    refine he.trans ?_
    apply congrArg (fun z => pullbackGlobalSections U.ι L z)
    rw [coordinateSection_eq_sectionsOfTop, Stacks.SheafOfModules.sectionsOfTop_eval_top]
  have hcomp :
      (M.unitHomEquiv (negativeChartCoordinateUnitHom X 1 ≫
        (Stacks.RegularSequence.globalSmulCenter U.toScheme
          (negativeChartCoordinate X)).app M)).eval (op ⊤) =
          negativeChartCoordinate X •
            (M.unitHomEquiv (negativeChartCoordinateUnitHom X 1)).eval (op ⊤) := by
    rw [SheafOfModules.unitHomEquiv_comp_apply]
    let z : Γ(M, ⊤) := (M.unitHomEquiv (negativeChartCoordinateUnitHom X 1)).eval (op ⊤)
    change ((Stacks.RegularSequence.globalSmulCenter U.toScheme
      (negativeChartCoordinate X)).app M).app ⊤ z = negativeChartCoordinate X • z
    refine (Stacks.RegularSequence.globalSmulCenter_app_app
      U.toScheme (negativeChartCoordinate X) M ⊤ z).trans ?_
    have hid : (⊤ : U.toScheme.Opens).leTop.op = 𝟙 (op (⊤ : U.toScheme.Opens)) :=
      Subsingleton.elim _ _
    have he : U.toScheme.presheaf.map (⊤ : U.toScheme.Opens).leTop.op
        (negativeChartCoordinate X) = negativeChartCoordinate X :=
      (congrArg (fun k => U.toScheme.presheaf.map k (negativeChartCoordinate X)) hid).trans
        (Functor.map_id_apply _ _ _)
    exact congrArg (fun a : Γ(U.toScheme, ⊤) => a • z) he
  exact (heval 0).trans ((pullbackGlobalSections_coordinateSectionTop_zero X).trans
    ((congrArg (negativeChartCoordinate X • ·) (heval 1).symm).trans hcomp.symm))

end AlgebraicGeometry.Scheme.ProjectiveLine
