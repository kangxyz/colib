/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.StandardTwoOpenCover
public import Colib.AlgebraicGeometry.Scheme.QuasiCompactPolynomialLaurent

/-!
# Polynomial coordinates on the integral projective line

Each standard integral chart is the spectrum of a polynomial ring in one variable.
The two copies use the coordinate omitted by the corresponding homogeneous index.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.ProjectiveSpace

universe u

namespace AlgebraicGeometry.Scheme.ProjectiveLine
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The integral standard coordinate open on the canonical projective line. -/
def integralChart (i : Fin 2) : (projectiveSpaceAtUniverse.{u} 1).Opens :=
  Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) (ULift.{u} ℤ))
    (MvPolynomial.X i)

/-- Its coordinate ring is the ordinary one-variable polynomial ring over the integral base. -/
def integralChartPolynomialIso (i : Fin 2) :
    (integralChart.{u} i).toScheme ≅ Spec (.of (Polynomial (ULift.{u} ℤ))) :=
  basicOpenXIsoSpec (ULift.{u} ℤ) 1 i ≪≫
    Scheme.Spec.mapIso
      (MvPolynomial.uniqueAlgEquiv (ULift.{u} ℤ) (Fin 1)).toRingEquiv.toCommRingCatIso.symm.op

/-- The chosen standard chart, before identifying its coordinate with the polynomial factor. -/
def standardChart (S : Scheme.{u}) (i : Fin 2) : (projectiveSpaceOver 1 S).Opens :=
  AlgebraicGeometry.ProjectiveSpace.standardOpen 1 S i

/-- The native coordinate chart is the base change of its integral open. -/
def standardChartIntegralPullbackIso (S : Scheme.{u}) (i : Fin 2) :
    (standardChart S i).toScheme ≅
      pullback (terminal.from S) (terminal.from (integralChart.{u} i).toScheme) :=
  (pullbackRestrictIsoRestrict (projectiveSpaceOver.toIntegralAtUniverse 1 S)
    (integralChart i)).symm ≪≫
  pullbackLeftPullbackSndIso (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse 1)) (integralChart i).ι ≪≫
  pullback.congrHom rfl (terminal.comp_from (integralChart i).ι)


/-- The native relative chart is the same polynomial product used by Bass theory. -/
def standardChartPolynomialIso (S : QuasiCompactSchemes.{u}) (i : Fin 2) :
    (standardChart S.obj i).toScheme ≅ (Relative.polynomialFunctor.obj S).obj := by
  let e := integralChartPolynomialIso.{u} i
  let t := terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal.{u}
  letI : IsIso e.hom := inferInstance
  letI : IsIso t.hom := inferInstance
  let f := terminal.from S.obj
  let g := terminal.from (integralChart i).toScheme
  let f' := specULiftZIsTerminal.from S.obj
  let g' := PolynomialLaurent.polynomialProjection (.of (ULift.{u} ℤ))
  have h₁ : f ≫ t.hom = 𝟙 S.obj ≫ f' := specULiftZIsTerminal.hom_ext _ _
  have h₂ : g ≫ t.hom = e.hom ≫ g' := specULiftZIsTerminal.hom_ext _ _
  let m := pullback.map f g f' g' (𝟙 S.obj) e.hom t.hom h₁ h₂
  letI : IsIso m := by
    dsimp [m]
    infer_instance
  exact standardChartIntegralPullbackIso S.obj i ≪≫ @asIso _ _ _ _ m (inferInstanceAs (IsIso m))


end AlgebraicGeometry.Scheme.ProjectiveLine
