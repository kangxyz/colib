/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedRangeFromAmbient
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedBassTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientSupportedNegativeBottomComparison
public import Colib.Topology.Prespectrum.TelescopeStableInclusion

/-!
# Original supported coefficient groups in the actual fine Bass telescope

Every original stage inclusion is invertible in its proved finite-stage degree range.
Composing that actual inclusion with the original finite-bottom comparison identifies the
supported pair Bass negative groups, including degree zero, with this same fine telescope. The
comparison is natural on the full coefficient category and retains the original quotient maps.
The ambient scheme is qcqs and the removed open is compact.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
CoefficientSupportedFineTelescopeComparison.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Topology Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

variable
  (hP : ∀ (a : Under R) (n : ℕ), IsIso ((stableHomotopyFunctor (n : ℤ)).map
    ((boundedAboveFlatCoefficientAmbientBassTransition P 0).app a)))
  (hQ : ∀ (a : Under R) (n : ℕ), IsIso ((stableHomotopyFunctor (n : ℤ)).map
    ((boundedAboveFlatCoefficientAmbientBassTransition Q 0).app a)))
  (hBottom : ∀ (a : Under R) (i : ℕ), CategoryTheory.Limits.IsZero
    (KTheory.Bass.TwoChartStable.bassRightGroup
      (modelDiagramTwoChartSquare (boundedAboveFlatCoefficientSupportedModelFunctor f) i a)
      (-(i : ℤ))))

include hP hQ hBottom in
/-- The unchanged finite-stage inclusion is invertible throughout the actual stable range. -/
theorem boundedAboveFlatCoefficientSupportedBassTelescopeInclusion_isIso_of_le_of_two_ambient
    (i : ℕ) (a : Under R) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f i).app a)) := by
  let : ∀ j k, T1Space (((boundedAboveFlatCoefficientSupportedBassDiagram f j).obj a).space k) :=
    fun j k => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) j
      (boundedAboveFlatCoefficientSupportedModelFunctor f) a k
  exact Telescope.inclusion_stableMap_isIso_of_tail
    (fun j => (boundedAboveFlatCoefficientSupportedBassDiagram f j).obj a)
    (fun j => (boundedAboveFlatCoefficientSupportedBassTransition f j).app a) d i
    (fun j hj => boundedAboveFlatCoefficientSupportedBassTransition_isIso_of_le_of_two_ambient
      f hP hQ hBottom j a d (by omega))

include hP hQ hBottom in
/-- At the original bottom degree the actual inclusion is an isomorphism of coefficient functors. -/
theorem boundedAboveFlatCoefficientSupportedBassTelescopeBottomInclusion_isIso_of_two_ambient
    (i : ℕ) :
    IsIso (Functor.whiskerRight (boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f i)
      (stableHomotopyFunctor (-(i : ℤ)))) := by
  let : ∀ a, IsIso ((Functor.whiskerRight
      (boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f i)
      (stableHomotopyFunctor (-(i : ℤ)))).app a) := fun a =>
    boundedAboveFlatCoefficientSupportedBassTelescopeInclusion_isIso_of_le_of_two_ambient
      f hP hQ hBottom i a (-(i : ℤ)) le_rfl
  exact NatIso.isIso_of_isIso_app _

include hP hQ hBottom in
/-- The original supported negative groups are naturally the groups of the actual fine completion.
-/
def boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_of_two_ambient (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ≅
      boundedAboveFlatCoefficientSupportedBassTelescopeFunctor f ⋙
        stableHomotopyFunctor (-(i : ℤ)) :=
  let := boundedAboveFlatCoefficientSupportedBassTelescopeBottomInclusion_isIso_of_two_ambient
    f hP hQ hBottom i
  boundedAboveFlatCoefficientSupportedNegativeKComparison f i ≪≫
    asIso (Functor.whiskerRight (boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f i)
      (stableHomotopyFunctor (-(i : ℤ))))

include hP hQ hBottom in
/-- The comparison is the original finite-bottom map followed by the actual stage inclusion. -/
theorem boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_of_two_ambient_hom_app
    (i : ℕ) (a : Under R) :
    (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_of_two_ambient
      f hP hQ hBottom i).hom.app a =
      (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f i).app a) := rfl

include hP hQ hBottom in
/-- The original Laurent quotient is retained after passage to the actual fine completion. -/
@[reassoc]
theorem boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_of_two_ambient_π
    (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
      ((boundedAboveFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ
        ((boundedAboveFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
        (boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_of_two_ambient
          f hP hQ hBottom (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientSupportedBassDiagram f i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedAboveFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a ≫
          (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
            ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f (i + 1)).app a) := by
  rw [boundedAboveFlatCoefficientSupportedNegativeKTelescopeComparison_of_two_ambient_hom_app]
  simpa only [Category.assoc] using
    (boundedAboveFlatCoefficientSupportedNegativeKComparison_π f i a) =≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientSupportedBassTelescopeInclusion f (i + 1)).app a)

end AlgebraicGeometry.Scheme.Modules
