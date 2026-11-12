/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFiniteNull
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterTelescopeCells
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedParameterTelescopeCells
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterFineTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionFullOpenNull

/-!
# The original integral Spec-row full null on the whole Bass telescope

The actual finite null square descends at the same original stage and cylinder
height. Its values agree with the existing global and fine full-open nulls at
every independent null time, without selecting a transported replacement null.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The actual Spec-row telescope isomorphisms preserve the entire original full-open null. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterTelescopeNull.lean:35"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem telescope_fullNull_square (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : ((SchemeNaturalSeed.iteratedTelescope (ParameterLaurentTrack.supportedTrack f.left)).obj
      (specUnder.obj a)).space n) :
    ((telescopeIso P).hom.app a).map n
      (((ParameterFullCurrentNull.iteratedNull f.left).homotopy (specUnder.obj a)).level n
        (s, x)) =
      ((FullOpenTelescope.null f).homotopy a).level n
        (s, ((GlobalSupportedParameterCoefficient.telescopeIso f).hom.app a).map n x) := by
  induction x using Quot.inductionOn with
  | h z =>
    exact congrArg (fun y => Telescope.cylinder (fun i => (globalDiagram P i).obj a)
      (fun i => (globalTransition P i).app a) n z.1 (z.2.1, y))
      (finite_fullNull_square f z.1 a n s z.2.2)

/-- The same original null is preserved by the actual comparison to the fine full-open telescope. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalParameterTelescopeNull.lean:51"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem telescope_fullNull_fine_square (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : ((SchemeNaturalSeed.iteratedTelescope (ParameterLaurentTrack.supportedTrack f.left)).obj
      (specUnder.obj a)).space n) :
    ((fineTelescopeComparison P).app a).map n
      (((ParameterFullCurrentNull.iteratedNull f.left).homotopy (specUnder.obj a)).level n
        (s, x)) =
      ((boundedAboveFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a).level n
        (s, ((GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a).map n x) := by
  exact (congrArg (fun y => ((telescopeRestriction P).app a).map n y)
    (telescope_fullNull_square f a n s x)).trans
      (FullOpenTelescope.null_restriction f a n s
        (((GlobalSupportedParameterCoefficient.telescopeIso f).hom.app a).map n x))

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

attribute [colib_tag "COL-0597"]
  telescope_fullNull_fine_square

attribute [colib_tag "COL-0597"]
  telescope_fullNull_square

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
