/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionCoarseFiber
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalFullOpenTelescopeSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientFullOpenBassLocalization

/-! # The original global null after actual full-open restriction -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.FullOpenTelescope
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The actual global ambient-to-full-open telescope map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionFullOpenNull.lean:24"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def openMap : globalTelescope Q ⟶ globalTelescope P :=
  LocalizationTelescope.openMap f ≫ restriction f

/-- Its strict comparison to the original fine full-open map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionFullOpenNull.lean:28"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem openMap_square :
    openMap f ≫ telescopeRestriction P =
      telescopeRestriction Q ≫ boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen f := by
  dsimp only [openMap, boundedAboveFlatCoefficientAmbientBassTelescopeFullOpen]
  rw [Category.assoc, restriction_square, ← Category.assoc,
    LocalizationTelescope.open_square, Category.assoc]

/-- Postcompose the same supported localization null with the original fine restriction. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionFullOpenNull.lean:36"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
def null :
    DiagramNullHomotopy (LocalizationTelescope.forget f)
      (openMap f) where
  homotopy a :=
    (((LocalizationTelescope.null f).homotopy a).postcomp
      ((restriction f).app a)).cast
        (Category.assoc _ _ _)
        (by
          apply Topology.LoopPrespectrum.Hom.ext
          funext m
          ext x
          exact ((restriction f).app a).map_point m)
  naturality {a b} g m s x := by
    change ((globalTelescope P).map g).map m
        (((restriction f).app a).map m
          (((LocalizationTelescope.null f).homotopy a).level m
            (s, x))) =
      ((restriction f).app b).map m
        (((LocalizationTelescope.null f).homotopy b).level m
          (s, ((SupportedTelescope.globalTelescope f).map g).map m x))
    exact (congrArg (fun g ↦ g.map m
      (((LocalizationTelescope.null f).homotopy a).level m (s, x)))
      ((restriction f).naturality g)).symm.trans
        (congrArg (fun y ↦
          ((restriction f).app b).map m y)
          ((LocalizationTelescope.null f).naturality g m s x))

/-- Every postcomposed null value retains its original time and the same restriction map. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionFullOpenNull.lean:64"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem null_level
    (a : Under R) (m : ℕ) (s : unitInterval)
    (x : ((SupportedTelescope.globalTelescope f).obj a).space m) :
    ((null f).homotopy a).level m (s, x) =
      ((restriction f).app a).map m
        (((LocalizationTelescope.null f).homotopy a).level m (s, x)) :=
  rfl

/-- Every original null time agrees through the actual full-open comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalSectionFullOpenNull.lean:73"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem null_restriction (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((SupportedTelescope.globalTelescope f).obj a).space n) :
    ((telescopeRestriction P).app a).map n ((null f).homotopy a |>.level n (s, x)) =
      ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a).level n
        (s, ((SupportedTelescope.telescopeRestriction f).app a).map n x) := by
  rw [null_level, boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull_level]
  exact (congrArg (fun η => (η.app a).map n
    (((LocalizationTelescope.null f).homotopy a).level n (s, x)))
      (restriction_square f)).trans
    (congrArg (fun y => ((boundedAboveFlatCoefficientOpenBassTelescopeRestriction f).app a).map n y)
      (LocalizationTelescope.null_restriction f a n s x))

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.FullOpenTelescope

