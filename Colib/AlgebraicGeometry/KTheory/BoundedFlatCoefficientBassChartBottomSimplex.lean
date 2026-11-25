/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassBottomCommonFamily

/-!
# The original common Bass chart and Laurent bottom simplex

The source order retains all 36 chart vertices followed by the 15 actual
Laurent bottom vertices. The shared boundary functors are checked here,
without identifying dependent nodes before the corresponding reference
isomorphisms have been compared. Adapted from `BassBottomCommonFamily.lean`
and `BassBottomNodeFunctors.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd` in Quillen.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
open scoped Simplicial

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassBottomCommonFamily

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Keep the two charts and complete bottom diagram; no shared-boundary quotient is taken. -/
def nodes : Fin 51 → BoundedFlatCoefficientBassOverlap.Node P u v :=
  Fin.addCases (m := 36) (n := 15) (motive := fun _ ↦ BoundedFlatCoefficientBassOverlap.Node P u v)
    (BoundedFlatCoefficientBassOverlap.nodes P u v) (bottomNodes P u v)

/-- The 50-simplex combining both chart diagrams and the bottom diagram over their common
reference. -/
def simplex : ModelSimplex
    (asSmallCategory (W (space (op P, a))))
    (asSmallCategory (W
      (space (op P, (laurentUnderFunctor R).obj c)))) 50 :=
  ModelSimplex.ofIsos (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (fun i ↦ (nodes P u v i).1) (fun i ↦ (nodes P u v i).2)

/-- The face inclusion selecting the first 36 vertices, which carry the two chart diagrams. -/
def chartFace : ⦋35⦌ ⟶ ⦋50⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.castAdd 15, fun _ _ h ↦ h⟩

/-- The face inclusion selecting the final 15 vertices, which carry the bottom diagram. -/
def bottomFace : ⦋14⦌ ⟶ ⦋50⦌ :=
  SimplexCategory.Hom.mk ⟨Fin.natAdd 36, fun _ _ h ↦ Nat.add_le_add_left h 36⟩

/-- Restricting to the actual chart face recovers the complete original double chart. -/
theorem chart_face : (simplex P u v).face chartFace =
    BoundedFlatCoefficientBassOverlap.simplex P u v := by
  unfold simplex BoundedFlatCoefficientBassOverlap.simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ (BoundedFlatCoefficientBassOverlap.nodes P u v)
    (fun i ↦ by
      change nodes P u v (Fin.castAdd 15 i) = _
      unfold nodes
      rw [Fin.addCases_left])

/-- Restricting to the actual bottom face recovers the complete original Laurent product. -/
theorem bottom_face : (simplex P u v).face bottomFace =
    BoundedFlatCoefficientBassLaurentBottomFace.simplex P u v := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ (bottomNodes P u v)
    (fun i ↦ by
      change nodes P u v (Fin.natAdd 36 i) = _
      unfold nodes
      rw [Fin.addCases_right])).trans (bottom_reference P u v)

/-- The positive boundary source functors literally agree. -/
theorem plus_source_functor :
    (nodes P u v 15).1.hom.toFunctor = (nodes P u v 42).1.hom.toFunctor := rfl
/-- The positive raw normalization intermediate functors literally agree. -/
theorem plus_intermediate_functor : (nodes P u v 16).1.hom.toFunctor =
    (nodes P u v 43).1.hom.toFunctor := rfl
/-- The positive normalized target functors literally agree. -/
theorem plus_target_functor :
    (nodes P u v 17).1.hom.toFunctor = (nodes P u v 44).1.hom.toFunctor := rfl

/-- The inverse boundary source functors literally agree. -/
theorem minus_source_functor :
    (nodes P u v 33).1.hom.toFunctor = (nodes P u v 48).1.hom.toFunctor := rfl
/-- The inverse raw normalization intermediate functors literally agree. -/
theorem minus_intermediate_functor : (nodes P u v 34).1.hom.toFunctor =
    (nodes P u v 49).1.hom.toFunctor := rfl
/-- The inverse normalized target functors literally agree. -/
theorem minus_target_functor :
    (nodes P u v 35).1.hom.toFunctor = (nodes P u v 50).1.hom.toFunctor := rfl


end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassBottomCommonFamily
