/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.PerfectScalarUnitTrack


/-! Original scalar/unit comparison, complete endpoints and independent structure time. -/
public section
open Topology SSet
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option linter.mathlibStandardSet true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules
    CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
universe u
namespace ColibTest.ScalarTrack.ScalarUnitTrack
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

include hq in
/-- The full original natural-transformation square, with the actual geometric iso. -/
theorem original_transformations :
    Functor.whiskerRight (perfectGlobalScalar X r) (perfectComplexesRestrictOpenImmersion j) ≫
        (perfectOpenRestrictionFlatIso j).hom =
      (perfectOpenRestrictionFlatIso j).hom ≫ (perfectFlatPullbackUnitIso j q).hom :=
  perfectOpenScalarRestrictionTransformation j r q hq

/-- The complete first comparison face is the specified postcomposed scalar then comparison. -/
theorem original_first_face (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).space n) :
    (perfectOpenScalarRestrictionUnitTrack j r q hq).level n (0, (s, x)) =
      (((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
        (perfectOpenScalarRestrictionMap j)).trans
          (perfectOpenRestrictionFlatHomotopy j)).level n (s, x) :=
  ((perfectOpenScalarRestrictionUnitTrack j r q hq).level n).apply_zero (s, x)

/-- Both comparison and track times remain independent of the original structure time. -/
theorem original_structure_time (n : ℕ) (a s t : unitInterval)
    (x : (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace)).space n) :
    (perfectOpenScalarRestrictionUnitTrack j r q hq).level (n + 1)
        (a, (s, (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen
    X.toRingedSpace)).structureMap n x t)) =
      (originalPrespectrum (RingedSpace.perfectComplexesWaldhausen U.toRingedSpace)).structureMap n
        ((perfectOpenScalarRestrictionUnitTrack j r q hq).level n (a, (s, x))) t :=
  (perfectOpenScalarRestrictionUnitTrack j r q hq).comm n a s x t

end ColibTest.ScalarTrack.ScalarUnitTrack
