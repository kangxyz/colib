/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientRange
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientBottomFromEmpty
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientAmbientNegativeMap
public import Colib.Topology.Prespectrum.TelescopeStableInclusion

/-!
# Original coefficient groups in the actual fine Bass telescope

Every original stage inclusion is invertible in its proved finite-stage degree range.
Composing that actual inclusion with the original finite-bottom comparison identifies the
scheme Bass negative groups, including degree zero, with this same fine telescope. The
comparison is natural on the full coefficient category and retains the original quotient maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left]

/-- The unchanged finite-stage inclusion is invertible throughout the actual stable range. -/
theorem boundedAboveFlatCoefficientAmbientBassTelescopeInclusion_isIso_of_le
    (i : ℕ) (a : Under R) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i).app a)) := by
  let : ∀ j k, T1Space (((boundedAboveFlatCoefficientAmbientBassDiagram P j).obj a).space k) :=
    fun j k => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) j
      (boundedAboveFlatCoefficientSectionModelRow P) a k
  exact Telescope.inclusion_stableMap_isIso_of_tail
    (fun j => (boundedAboveFlatCoefficientAmbientBassDiagram P j).obj a)
    (fun j => (boundedAboveFlatCoefficientAmbientBassTransition P j).app a) d i
    (fun j hj => boundedAboveFlatCoefficientAmbientBassTransition_isIso_of_le_of_bottom P
      (boundedAboveFlatCoefficientAmbientBottomBassRight_isZero P) j a d (by omega))

/-- At the original bottom degree the actual inclusion is an isomorphism of coefficient functors.
-/
instance boundedAboveFlatCoefficientAmbientBassTelescopeBottomInclusion_isIso (i : ℕ) :
    IsIso (Functor.whiskerRight (boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i)
      (stableHomotopyFunctor (-(i : ℤ)))) := by
  let : ∀ a, IsIso ((Functor.whiskerRight
      (boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i)
      (stableHomotopyFunctor (-(i : ℤ)))).app a) := fun a =>
    boundedAboveFlatCoefficientAmbientBassTelescopeInclusion_isIso_of_le P i a (-(i : ℤ)) le_rfl
  exact NatIso.isIso_of_isIso_app _

/-- The original scheme negative groups are naturally the groups of the actual fine completion.
-/
def boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison (i : ℕ) :
    boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i ≅
      boundedAboveFlatCoefficientAmbientBassTelescopeFunctor P ⋙
        stableHomotopyFunctor (-(i : ℤ)) :=
  boundedAboveFlatCoefficientAmbientNegativeKComparison P i ≪≫
    asIso (Functor.whiskerRight (boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i)
      (stableHomotopyFunctor (-(i : ℤ))))

/-- The ambient isomorphism has the same underlying original class map. -/
theorem boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison_hom (i : ℕ) :
    (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom =
      boundedAboveFlatCoefficientAmbientBassNegativeMap P i := rfl

/-- The comparison is the original finite-bottom map followed by the actual stage inclusion. -/
theorem boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison_hom_app
    (i : ℕ) (a : Under R) :
    (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a =
      (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P i).app a) := rfl

/-- The original Laurent quotient is retained after passage to the actual fine completion. -/
@[reassoc]
theorem boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison_π (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).map ((boundedAboveFlatCoefficientLaurentIso P).hom.app a) ≫
      Bass.negativeKπ ((boundedAboveFlatCoefficientQuasiCompactRow P).obj a).unop i ≫
        (boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison P (i + 1)).hom.app a =
    (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (KTheory.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedAboveFlatCoefficientAmbientBassDiagram P i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedAboveFlatCoefficientAmbientBassBottomContractionIso P i).hom.app a ≫
          (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
            ((boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P (i + 1)).app a) := by
  rw [boundedAboveFlatCoefficientAmbientNegativeKTelescopeComparison_hom_app]
  simpa only [Category.assoc] using
    (boundedAboveFlatCoefficientAmbientNegativeKComparison_π P i a) =≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedAboveFlatCoefficientAmbientBassTelescopeInclusion P (i + 1)).app a)

end AlgebraicGeometry.Scheme.Modules
