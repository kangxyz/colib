/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.CWLifting

/-! # Regression tests for the actual CW double-cylinder lift -/
@[expose] public section

open Topology

open TopCat.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory Set
open scoped unitInterval
universe u
namespace ColibTest.Topology.CWDoubleCylinder

variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]
variable {D : TopCat.{u}} (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
variable {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (TopCat.intervalEndpoints (TopCat.of A)) (endMap f g) l e)
variable {E T : Type u} [TopologicalSpace E] [TopologicalSpace T]
variable (p : C(E, T)) (hp : CubicalSubdivision.BoundaryLifting p) (d : C(D, T))

/-- The global lift projects to the exact original map. -/
theorem strictOriginalMap : p.comp (cwLift A B C f g sq p hp d) = d :=
  cwLift_comp A B C f g sq p hp d

/-- The original chosen left CW lift is retained by descent. -/
theorem leftRetained : (cwLift A B C f g sq p hp d).comp (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e) =
    cwLiftLeft B p hp d (gapLeftEndpoint (B := TopCat.of B)
          (C := TopCat.of C) e) := cwLift_left A B C f g sq p hp d

/-- The original chosen right CW lift is retained by descent. -/
theorem rightRetained : (cwLift A B C f g sq p hp d).comp
    (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e) =
      cwLiftRight C p hp d (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e) :=
  cwLift_right A B C f g sq p hp d

/-- The entire original cylinder, not just its caps, recovers the displayed lift. -/
theorem entireCylinder (t : I) (a : A) :
    cwLift A B C f g sq p hp d (l (a, ULift.up t)) =
      cwLiftCylinderHomotopy A B C f g sq p hp d (t, a) :=
  cwLift_cylinder A B C f g sq p hp d t a

/-- Projection keeps every point of the original base cylinder. -/
theorem entireProjectedCylinder (t : I) (a : A) :
    p (cwLiftCylinderHomotopy A B C f g sq p hp d (t, a)) =
      d (l (a, ULift.up t)) := cwLiftCylinderHomotopy_project A B C f g sq p hp d t a

/-- The attaching homotopy uses exactly the two chosen original endpoint maps. -/
theorem bothAttachingEndpoints (a : A) :
    cwLiftCylinderHomotopy A B C f g sq p hp d (0, a) =
      cwLiftLeft B p hp d (gapLeftEndpoint (B := TopCat.of B) (C := TopCat.of C) e) (f a) ∧
    cwLiftCylinderHomotopy A B C f g sq p hp d (1, a) =
      cwLiftRight C p hp d (gapRightEndpoint (B := TopCat.of B) (C := TopCat.of C) e) (g a) :=
  ⟨(cwLiftCylinderHomotopy A B C f g sq p hp d).map_zero_left a,
    (cwLiftCylinderHomotopy A B C f g sq p hp d).map_one_left a⟩

/-- Continuity is on the literal whole pushout, without a target CW instance. -/
theorem wholeContinuity : Continuous (cwLift A B C f g sq p hp d) :=
  (cwLift A B C f g sq p hp d).continuous

end ColibTest.Topology.CWDoubleCylinder
