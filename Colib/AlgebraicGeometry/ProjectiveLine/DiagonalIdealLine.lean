/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalSequence
public import Colib.AlgebraicGeometry.ProjectiveLine.DiagonalZeroScheme
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafUniqueness
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeRegular
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Picard.DiagonalFibreDivisor
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic

/-! # The invertible ideal of the relative projective-line diagonal

The determinant cuts out the actual relative diagonal. Its line is
`p₁*𝒪(1) ⊗ p₂*𝒪(1)`, so evaluation of the determinant identifies the dual
line with the ideal sheaf. Cartier regularity comes from smoothness of
relative dimension one.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Divisors Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open MonoidalCategory
open Stacks.AlgebraicGeometry.ReflexiveModules

namespace AlgebraicGeometry.Scheme

universe u

variable (X : Scheme.{u})

local notation "P" => projectiveSpaceOver 1 X
local notation "π" => (P ↘ X)
local notation "Q" => pullback π π

/-- The actual diagonal ideal is Cartier. -/
theorem projectiveLineDiagonal_isEffectiveCartierDivisor :
    IsEffectiveCartierDivisor (pullback.diagonal π).ker := by
  let := isProper_projectiveSpaceOver 1 X
  have h : Stacks.Hilbert.diagonalIdeal π = (pullback.diagonal π).ker := by
    unfold Stacks.Hilbert.diagonalIdeal Stacks.Hilbert.pointIdeal
    congr 1
  rw [← h]
  exact Stacks.Hilbert.isEffectiveCartierDivisor_diagonalIdeal π

/-- The determinant is a regular section of the external positive line. -/
theorem projectiveLineDiagonalDeterminant_isRegularSection :
    IsRegularSection (Q).sheaf.obj (Q).ringCatSheaf.property
      (sectionsOfTop (projectiveLineDiagonalPositiveTwist X)
        (projectiveLineDiagonalDeterminant X)) := by
  let L := projectiveLineDiagonalPositiveTwist X
  let s := sectionsOfTop L (projectiveLineDiagonalDeterminant X)
  have hs : s.eval (op ⊤) = projectiveLineDiagonalDeterminant X :=
    sectionsOfTop_eval_top L _
  apply (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection Q L s).mp
  rw [hs]
  change IsEffectiveCartierDivisor (projectiveLineDeterminantIdeal X)
  rw [projectiveLineDeterminantIdeal_eq_diagonal]
  exact projectiveLineDiagonal_isEffectiveCartierDivisor X

/-- The actual ideal of the diagonal is the dual of the external positive line. -/
def projectiveLineDiagonalIdealDualIso :
    dualSheaf (projectiveLineDiagonalPositiveTwist X) ≅
      idealSheafModule (pullback.diagonal π).ker := by
  let L := projectiveLineDiagonalPositiveTwist X
  let a := projectiveLineDiagonalDeterminant X
  let s := sectionsOfTop L a
  letI := isIso_zeroSchemeIdealModuleHom L a (by
    simpa only [show s.eval (op ⊤) = a from sectionsOfTop_eval_top L a] using
      injective_smul_res_of_isRegularSection L s
        (projectiveLineDiagonalDeterminant_isRegularSection X))
  exact asIso (zeroSchemeIdealModuleHom L a) ≪≫
    eqToIso (congrArg (fun I : (Q).IdealSheafData => idealSheafModule I)
      (projectiveLineDeterminantIdeal_eq_diagonal X))

section TensorInverse

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory Stacks.SheafInternalHom.sheafifyMonoidal
  Stacks.SheafInternalHom.braidedCategory Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- The external product of the negative twists from the two factors. -/
abbrev projectiveLineDiagonalNegativeTwist : (Q).Modules :=
  tensorModules Q ((Modules.pullback (pullback.fst π π)).obj (twistOver 1 X (-1)))
    ((Modules.pullback (pullback.snd π π)).obj (twistOver 1 X (-1)))

/-- The positive and negative twists cancel after pullback along either projection. -/
def diagonalTensorTwistInverse (j : Q ⟶ P) :
    ((Modules.pullback j).obj (twistOver 1 X 1) ⊗
        (Modules.pullback j).obj (twistOver 1 X (-1)) : (Q).Modules) ≅ 𝟙_ (Q).Modules :=
  Stacks.AmplePullbackPart1.tensorIsoTensorModules Q _ _ ≪≫
    (pullbackTensorModulesIso j _ _).symm ≪≫
    (Modules.pullback j).mapIso (twistOverNegIsoUnit 1 X 1) ≪≫
    Stacks.RelativeAmple.pullbackUnitModuleIso j ≪≫ Stacks.Ample.unitModuleIsoTensorUnit Q

/-- The external negative twist is a tensor inverse of the external positive twist. -/
def projectiveLineDiagonalTensorUnitIso :
    tensorModules Q (projectiveLineDiagonalPositiveTwist X)
      (projectiveLineDiagonalNegativeTwist X) ≅ SheafOfModules.unit (Q).ringCatSheaf := by
  let A := projectiveLineFirstPositiveTwist X
  let B := projectiveLineSecondPositiveTwist X
  let C := (Modules.pullback (pullback.fst π π)).obj (twistOver 1 X (-1))
  let D := (Modules.pullback (pullback.snd π π)).obj (twistOver 1 X (-1))
  exact (Stacks.AmplePullbackPart1.tensorIsoTensorModules Q _ _).symm ≪≫
    ((Stacks.AmplePullbackPart1.tensorIsoTensorModules Q A B).symm ⊗ᵢ
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules Q C D).symm) ≪≫
    Stacks.AmplePullbackPart1.tensorMuIso A B C D ≪≫
    (diagonalTensorTwistInverse X (pullback.fst π π) ⊗ᵢ
      diagonalTensorTwistInverse X (pullback.snd π π)) ≪≫
    λ_ (𝟙_ (Q).Modules) ≪≫ (Stacks.Ample.unitModuleIsoTensorUnit Q).symm

/-- The actual ideal sheaf of the relative diagonal is the external product `𝒪(-1,-1)`. -/
def projectiveLineDiagonalIdealLineIso :
    projectiveLineDiagonalNegativeTwist X ≅ idealSheafModule (pullback.diagonal π).ker :=
  Stacks.SheafOfModules.Invertible.tensorInverseIsoDualSheaf (Q).sheaf.obj
      (Q).ringCatSheaf.property (projectiveLineDiagonalPositiveTwist X)
      (projectiveLineDiagonalNegativeTwist X) (projectiveLineDiagonalTensorUnitIso X) ≪≫
    projectiveLineDiagonalIdealDualIso X

end TensorInverse

/-- The sheaf of ideals presented by the closed subscheme of the kernel agrees with the
kernel of the comorphism of the actual diagonal. -/
def projectiveLineDiagonalIdealKernelIso :
    idealSheafModule (pullback.diagonal π).ker ≅ (projectiveLineDiagonalSequence X).X₁ := by
  letI := isProper_projectiveSpaceOver 1 X
  let Δ := pullback.diagonal π
  let e := asIso Δ.toImage
  let eLR := Scheme.forgetToLocallyRingedSpace.mapIso e
  let j := Δ.imageι.toLRSHom
  have h : (eLR.hom ≫ j).toShHom = Δ.toLRSHom.toShHom := by
    exact congrArg (fun f : P ⟶ Q => f.toLRSHom.toShHom) Δ.toImage_imageι
  exact (Stacks.ClosedImmersion.idealSheafCompIso eLR j).symm ≪≫
    Stacks.ClosedImmersion.idealSheafCongr h

/-- The actual first object in the diagonal short exact sequence is `𝒪(-1,-1)`. -/
def projectiveLineDiagonalSequenceFirstIso :
    projectiveLineDiagonalNegativeTwist X ≅ (projectiveLineDiagonalSequence X).X₁ :=
  projectiveLineDiagonalIdealLineIso X ≪≫ projectiveLineDiagonalIdealKernelIso X

end AlgebraicGeometry.Scheme
