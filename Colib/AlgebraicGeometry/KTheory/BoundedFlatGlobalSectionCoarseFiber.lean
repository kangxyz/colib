/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.Topology.Prespectrum.ConeDescStableEquivalence
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLocalizationTelescopeNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeSquares
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeStable
/-! # Original independent null time, telescope height and same-null coarse fiber comparison -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.LocalizationTelescope
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The actual strict ambient/coarse comparison square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionCoarseFiber.lean:25"
  "adaptation" "Original same whole null and actual stable global coarse fiber comparison"]
def fiberSquare (a : Under R) : Arrow.mk ((openMap f).app a) ⟶
    Arrow.mk ((boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a) :=
  Arrow.homMk ((telescopeRestriction Q).app a) ((OpenTelescope.telescopeRestriction f).app a)
    (congrArg (fun η => η.app a) (open_square f)).symm

/-- The original global support inclusion lifts by its constructed complete null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionCoarseFiber.lean:31"
  "adaptation" "Original same whole null and actual stable global coarse fiber comparison"]
def fiberMap (a : Under R) : (SupportedTelescope.globalTelescope f).obj a ⟶
    homotopyFiber ((openMap f).app a) :=
  homotopyFiberLift ((openMap f).app a) ((forget f).app a) ((null f).homotopy a)

/-- The actual comparison retains both the source coordinate and the complete null path. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionCoarseFiber.lean:36"
  "adaptation" "Original same whole null and actual stable global coarse fiber comparison"]
theorem fiberMap_restriction (a : Under R) :
    fiberMap f a ≫ homotopyFiberMap (fiberSquare f a) =
      (SupportedTelescope.telescopeRestriction f).app a ≫
        homotopyFiberLift ((boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a)
          ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
          ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun η => (η.app a).map n x) (forget_square f).symm
  · apply ContinuousMap.ext
    intro s
    exact null_restriction f a n s x

/-- The specified global coarse fiber lift is stable in every original signed degree. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionCoarseFiber.lean:54"
  "adaptation" "Original same whole null and actual stable global coarse fiber comparison"]
theorem fiberMap_isStableEquivalence (a : Under R) : IsStableEquivalence (fiberMap f a) := by
  have hf : IsStableEquivalence
      (homotopyFiberLift ((boundedAboveFlatCoefficientAmbientBassTelescopeOpen f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedAboveFlatCoefficientSupportedBassTelescopeOpenNull f).homotopy a)) :=
    homotopyFiberLift_isStableEquivalence_of_coneDesc _ _ _
      (boundedAboveFlatCoefficientSupportedBassTelescopeForget_coneFiber_isStableEquivalence f a)
      (boundedAboveFlatCoefficientSupportedBassTelescopeOpenConeMap_isStableEquivalence f a)
  have hb := homotopyFiberMap_isStableEquivalence (fiberSquare f a)
    (telescopeRestriction_isStableEquivalence Q a)
    (OpenTelescope.telescopeRestriction_isStableEquivalence f a)
  have hc := (SupportedTelescope.telescopeRestriction_isStableEquivalence f a).comp hf
  intro d
  let := hb d
  apply (isIso_comp_right_iff ((stableHomotopyFunctor d).map (fiberMap f a))
    ((stableHomotopyFunctor d).map (homotopyFiberMap (fiberSquare f a)))).mp
  rw [← Functor.map_comp, fiberMap_restriction]
  exact hc d

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.LocalizationTelescope

