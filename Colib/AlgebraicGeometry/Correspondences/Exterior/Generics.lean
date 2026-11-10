/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.Components

/-!
# Actual generic points under a geometrically integral parameter product

Combine the native component correspondence with the native sober-space
bijection between components and generic points. The resulting actual product
generic lies over the original generic, and its closure is the literal
Cartesian preimage. Empty and disconnected sources are retained.
This supplies the native reindexing needed for the original motivic
Exterior/Identity/Unit.lean and Exterior/Simplex/Graph.lean arguments.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

variable {S : Scheme.{u}} (X T : SmoothSite S) [GeometricallyIntegral T.hom]

/-- The native generic-point correspondence induced by the actual product projection. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/Unit.lean:157-162"
  "adaptation" "Actual native generic-point reindexing of parameter-product components"]
def exteriorSourceGenericsEquiv :
    genericPoints X.left ≃ genericPoints (SmoothSite.product X T).left :=
  (genericPoints.equiv (α := X.left)).trans
    ((exteriorSourceComponentsEquiv X T).trans
      (genericPoints.equiv (α := (SmoothSite.product X T).left)).symm)

/-- The new generic point has exactly the Cartesian-preimage component closure. -/
theorem exteriorSourceGenericsEquiv_closure (t : genericPoints X.left) :
    closure ({(exteriorSourceGenericsEquiv X T t).val} :
      Set (SmoothSite.product X T).left) =
      (pullback.fst X.hom T.hom) ⁻¹' closure ({t.val} : Set X.left) := by
  change (genericPoints.component (genericPoints.ofComponent
    (exteriorSourceComponentsEquiv X T (genericPoints.component t)))).val = _
  exact congrArg Subtype.val (genericPoints.component_ofComponent
    (exteriorSourceComponentsEquiv X T (genericPoints.component t)))

/-- The actual product projection takes the corresponding generic to the original point. -/
@[simp↓]
theorem exteriorSourceGenericsEquiv_fst (t : genericPoints X.left) :
    (pullback.fst X.hom T.hom) (exteriorSourceGenericsEquiv X T t).val = t.val := by
  let p := pullback.fst X.hom T.hom
  have ht : IsGenericPoint (exteriorSourceGenericsEquiv X T t).val
      (p ⁻¹' closure ({t.val} : Set X.left)) :=
    exteriorSourceGenericsEquiv_closure X T t
  have hi := ht.image p.continuous
  rw [Set.image_preimage_eq _ p.surjective, isClosed_closure.closure_eq] at hi
  exact hi.eq isGenericPoint_closure

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Topology/Sober.lean:293-331"
  "ingredient"
    "Native generic-point/component equivalence gives the exact product generic and closure"]
  exteriorSourceGenericsEquiv
  exteriorSourceGenericsEquiv_closure
  exteriorSourceGenericsEquiv_fst

end Stacks.Chow
