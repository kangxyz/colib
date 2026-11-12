/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterTelescopeNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterTelescopeForget
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFineRestrictionSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterIteratedOpenIdentification
public import Colib.Topology.Prespectrum.FiberLiftNaturality

/-!
# The original parameter seed-iterate full-open fiber lift is stable

The three actual Spec-row comparisons preserve support forgetting, full-open
restriction, and the entire originally selected null. The existing fine
localization theorem therefore transports to the original parameter
seed-iterate lift. This theorem concerns that actual iterated-seed model.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
open GlobalSectionChangeIndex GlobalParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The actual original full-open parameter map agrees through the two fine comparisons. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterIteratedFullFiber.lean:36"
  "adaptation" "Original actual full-open fiber lift through the same selected null."]
theorem iteratedOpen_fine_square :
    Functor.whiskerLeft specUnder (iteratedOpen f.left) ≫ fineTelescopeComparison P =
      fineTelescopeComparison Q ≫ boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f := by
  have h := fine_fullRestriction_square f
  rw [parameterTelescopeRestriction_eq_iteratedOpen] at h
  exact h

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- At every integral Spec-row coefficient, the original same-null iterated-seed lift is stable. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    ParameterIteratedFullFiber.lean:46"
  "adaptation" "Original actual full-open fiber lift through the same selected null."]
theorem iteratedLift_spec_isStableEquivalence
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (iteratedLift f.left (specUnder.obj a)) := by
  have hf := congrArg (fun k => k.app a)
    (GlobalSupportedParameterCoefficient.fineTelescope_forget_square f)
  have hr := congrArg (fun k => k.app a) (iteratedOpen_fine_square f)
  have hiff := homotopyFiberLift_isStableEquivalence_iff
    ((iteratedForget f.left).app (specUnder.obj a))
    ((iteratedOpen f.left).app (specUnder.obj a))
    ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
    ((boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    ((iteratedNull f.left).homotopy (specUnder.obj a))
    ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)
    ((GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a)
    ((fineTelescopeComparison Q).app a) ((fineTelescopeComparison P).app a)
    hf hr.symm (telescope_fullNull_fine_square f a)
    (GlobalSupportedParameterCoefficient.fineTelescopeComparison_stable f a)
    (fineTelescopeComparison_stable Q a) (fineTelescopeComparison_stable P a)
  exact hiff.mpr
    (boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a)

end AlgebraicGeometry.Scheme.Modules.ParameterFullCurrentNull
