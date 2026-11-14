/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.Modules.TwoOpenDerivedCech
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.StandardAffineChart
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceProper
public import StacksFrontier.AlgebraicGeometry.RelativeCechComplex.Affine

/-!
# The relative derived Čech triangle on the projective line

The two standard affine charts compute the derived direct image of a
quasi-coherent module on `ℙ¹_R`. The triangle remembers both the signed
restriction difference and the original connecting morphism.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.projectiveSpaceOver TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

local instance (X : Scheme.{u}) : HasDerivedCategory.{u + 1} X.Modules :=
  HasDerivedCategory.standard _

variable (R : CommRingCat.{u})

abbrev line := projectiveSpaceOver 1 (Spec R)
abbrev lineChartZero := standardChart 1 (Spec R) (0 : Fin 2)
abbrev lineChartOne := standardChart 1 (Spec R) (1 : Fin 2)
abbrev lineProjection : line R ⟶ Spec R := line R ↘ Spec R

/-- The two standard charts of the projective line cover it. -/
theorem lineChart_cover : lineChartZero R ⊔ lineChartOne R = ⊤ := by
  rw [← iSup_standardChart 1 (Spec R)]
  apply le_antisymm
  · exact sup_le (le_iSup _ (0 : Fin 2)) (le_iSup _ (1 : Fin 2))
  · apply iSup_le
    intro k
    fin_cases k
    · exact le_sup_left
    · exact le_sup_right

/-- Each standard chart of the projective line over an affine base is affine. -/
theorem lineChart_affine (k : Fin 2) : IsAffineOpen (standardChart 1 (Spec R) k) := by
  let σ := ULift.{u} {j : Fin 2 // j ≠ k}
  let e := standardChartIso 1 k (Equiv.ulift : σ ≃ {j : Fin 2 // j ≠ k}) (Spec R)
  let : IsAffine (𝔸(σ; Spec R)) := isAffine_of_isAffineHom (𝔸(σ; Spec R) ↘ Spec R)
  exact IsAffine.of_isIso e.inv

instance lineChartZero_isAffine : IsAffine (lineChartZero R).toScheme := lineChart_affine R 0
instance lineChartOne_isAffine : IsAffine (lineChartOne R).toScheme := lineChart_affine R 1
instance lineChartIntersection_isAffine : IsAffine (lineChartZero R ⊓ lineChartOne R).toScheme :=
  (lineChart_affine R 0).inf (lineChart_affine R 1)

instance lineChartZero_isAffineHom : IsAffineHom (lineChartZero R).ι := by
  exact Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source _
instance lineChartOne_isAffineHom : IsAffineHom (lineChartOne R).ι := by
  exact Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source _
instance lineChartIntersection_isAffineHom :
    IsAffineHom (lineChartZero R ⊓ lineChartOne R).ι :=
  Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source _

instance lineChartZeroProjection_isAffineHom :
    IsAffineHom ((lineChartZero R).ι ≫ lineProjection R) :=
  Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source _
instance lineChartOneProjection_isAffineHom :
    IsAffineHom ((lineChartOne R).ι ≫ lineProjection R) :=
  Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source _
instance lineChartIntersectionProjection_isAffineHom :
    IsAffineHom ((lineChartZero R ⊓ lineChartOne R).ι ≫ lineProjection R) :=
  Stacks.AlgebraicGeometry.RelativeCechComplex.isAffineHom_of_isAffine_source _

variable (M : (line R).Modules) [M.IsQuasicoherent]
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Functor.commShiftRightDerivedFunctorPlus

/-- The native projective line's relative derived Čech triangle. -/
@[expose] def lineDerivedCechTriangle : Triangle (DerivedCategory.Plus (Spec R).Modules) :=
  Scheme.Modules.twoOpenDerivedCechTriangle (lineProjection R) (lineChartZero R) (lineChartOne R) M
    (lineChart_cover R)

/-- Its second map is the signed direct-image restriction difference. -/
theorem lineDerivedCechTriangle_mor₂ :
    (lineDerivedCechTriangle R M).mor₂ =
      (DerivedCategory.Plus.singleFunctor (Spec R).Modules 0).map
        ((Scheme.Modules.pushforward (lineProjection R)).map
          (Scheme.Modules.twoOpenCech (lineChartZero R) (lineChartOne R) M).g) := rfl

/-- The first vertex is the bounded-below derived direct image of the original module. -/
theorem lineDerivedCechTriangle_obj₁ :
    (lineDerivedCechTriangle R M).obj₁ =
      (Scheme.Modules.pushforward (lineProjection R)).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (line R).Modules 0).obj M) := rfl

set_option maxHeartbeats 1200000 in
-- Specializing the two-open construction checks the bounded-derived shift instances.
/-- Its boundary is the original derived connecting morphism under the acyclic unit. -/
def lineDerivedCechTriangleIso :
    lineDerivedCechTriangle R M ≅
      (Scheme.Modules.pushforward (lineProjection R)).rightDerivedSingleTriangle
      (Scheme.Modules.twoOpenCech_shortExact (lineChartZero R) (lineChartOne R) M
        (lineChart_cover R)) := by
  unfold lineDerivedCechTriangle
  exact Scheme.Modules.twoOpenDerivedCechTriangleIso
    (lineProjection R) (lineChartZero R) (lineChartOne R) M (lineChart_cover R)

/-- The projective line's relative Čech triangle is distinguished over any commutative ring. -/
theorem lineDerivedCechTriangle_distinguished :
    lineDerivedCechTriangle R M ∈ distTriang (DerivedCategory.Plus (Spec R).Modules) :=
  Scheme.Modules.twoOpenDerivedCechTriangle_distinguished
    (lineProjection R) (lineChartZero R) (lineChartOne R) M (lineChart_cover R)

end AlgebraicGeometry.projectiveSpaceOver
