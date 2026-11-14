/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.CechGlobalSections
public import Colib.AlgebraicGeometry.ProjectiveLine.VectorBundleDirectImage
public import Colib.AlgebraicGeometry.ProjectiveLine.VectorBundleChartProjectivity
public import Colib.CategoryTheory.DerivedCategory.PerfectTwoTermModel
public import Colib.CategoryTheory.DerivedCategory.TwoTermConeProjective
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic

/-! # Finite projective models of projective-line Čech complexes

The ordinary signed two-open Čech complex of a vector bundle on the projective
line over a commutative ring is a complex of projective modules. Proper flat
direct image makes its image in the derived category perfect. Since the complex
is concentrated in degrees zero and one, the finite-projective model can be
chosen in the same degrees, up to chain homotopy equivalence.

## References

* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0658](https://stacks.math.columbia.edu/tag/0658)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] HasDerivedCategory.standard Abelian.hasFiniteBiproducts

variable (R : CommRingCat.{u}) (M : (line R).Modules)
  [M.IsQuasicoherent] [SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]

/-- Given projectivity of the actual two Čech terms over the coefficient ring, the signed
complex is chain-homotopy equivalent to a finite projective complex in the same degrees. -/
theorem exists_lineCechFiniteProjectiveModel_of_projective
    (h₂ : Module.Projective R ((globalSectionsOver (lineProjection R)).obj
      (Scheme.Modules.twoOpenCech (lineChartZero R) (lineChartOne R) M).X₂))
    (h₃ : Module.Projective R ((globalSectionsOver (lineProjection R)).obj
      (Scheme.Modules.twoOpenCech (lineChartZero R) (lineChartOne R) M).X₃)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      Nonempty (HomotopyEquiv (lineCechSectionsComplex R M) P) := by
  let S := Scheme.Modules.twoOpenCech (lineChartZero R) (lineChartOne R) M
  let F := globalSectionsOver (lineProjection R)
  let K := lineCechSectionsComplex R M
  let : Module.Projective R (F.obj S.X₂) := h₂
  let : Module.Projective R (F.obj S.X₃) := h₃
  let : K.IsStrictlyGE 0 := lineCechSectionsComplex_isStrictlyGE R M
  let : K.IsStrictlyLE 1 := lineCechSectionsComplex_isStrictlyLE R M
  let (n : ℤ) : Module.Projective R (K.X n) :=
    CochainComplex.projective_shiftedMappingCone_single (F.obj S.X₂) (F.obj S.X₃) (F.map S.g) n
  exact CochainComplex.exists_finiteProjectiveTwoTermModel K
    (StacksDraft.Perfect.isPerfect_of_iso (lineCechSectionsComplexIso R M).symm
      (isPerfect_lineDerivedSections R M))

omit [M.IsQuasicoherent] in
/-- Over an arbitrary commutative ring, the signed Čech complex of an actual vector bundle
on the projective line is chain-homotopy equivalent to a finite projective two-term complex. -/
theorem exists_lineCechFiniteProjectiveModel :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ k, k ≠ 0 → k ≠ 1 → IsZero (P.X k)) ∧
      (∀ k, Module.Finite R (P.X k) ∧ Module.Projective R (P.X k)) ∧
      Nonempty (HomotopyEquiv (lineCechSectionsComplex R M) P) := by
  let : M.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree M
  let F := globalSectionsOver (lineProjection R)
  let A := (restrictPushMod (lineChartZero R)).obj M
  let B := (restrictPushMod (lineChartOne R)).obj M
  let : F.Additive := AlgebraicGeometry.globalSectionsOver_additive (lineProjection R)
  let : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  let : Module.Projective R (F.obj A) := projective_standardChartSections R M 0
  let : Module.Projective R (F.obj B) := projective_standardChartSections R M 1
  have h₂ : Module.Projective R (F.obj (A ⊞ B)) :=
    Module.Projective.of_equiv
      (((F.mapBiprod A B) ≪≫ ModuleCat.biprodIsoProd (F.obj A) (F.obj B)).symm.toLinearEquiv)
  exact exists_lineCechFiniteProjectiveModel_of_projective R M h₂
    (projective_standardOverlapSections R M)

end AlgebraicGeometry.projectiveSpaceOver
