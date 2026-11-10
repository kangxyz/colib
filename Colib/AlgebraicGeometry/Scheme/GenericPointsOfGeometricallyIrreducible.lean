/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible

/-!
# Generic points under an open geometrically irreducible morphism

The equivalence is between the native generic-point sets of arbitrary schemes.
It is the composite of Mathlib's actual component equivalence with its sober-space
component/generic-point equivalences. Neither scheme is assumed reduced, integral,
Noetherian, connected, smooth, or nonempty.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u
namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f]
  (hf : IsOpenMap f)

/-- The generic of the complete inverse-image component, with no component selected or omitted. -/
def genericPointsEquivOfGeometricallyIrreducible : genericPoints Y ≃ genericPoints X :=
  (genericPoints.equiv (α := Y)).trans
    ((f.irreducibleComponentsEquiv hf).symm.trans
      (genericPoints.equiv (α := X)).symm)

/-- The corresponding component is the literal inverse image under the actual morphism. -/
theorem genericPointsEquivOfGeometricallyIrreducible_closure (y : genericPoints Y) :
    closure ({(f.genericPointsEquivOfGeometricallyIrreducible hf y).val} : Set X) =
      f ⁻¹' closure ({y.val} : Set Y) := by
  change (genericPoints.component (genericPoints.ofComponent
    ((f.irreducibleComponentsEquiv hf).symm (genericPoints.component y)))).val = _
  exact congrArg Subtype.val (genericPoints.component_ofComponent
    ((f.irreducibleComponentsEquiv hf).symm (genericPoints.component y)))

/-- The new generic point lies over the specified original generic point. -/
@[simp]
theorem genericPointsEquivOfGeometricallyIrreducible_apply (y : genericPoints Y) :
    f (f.genericPointsEquivOfGeometricallyIrreducible hf y).val = y.val := by
  have hy : IsGenericPoint (f.genericPointsEquivOfGeometricallyIrreducible hf y).val
      (f ⁻¹' closure ({y.val} : Set Y)) :=
    f.genericPointsEquivOfGeometricallyIrreducible_closure hf y
  have hi := hy.image f.continuous
  rw [Set.image_preimage_eq _ f.surjective, isClosed_closure.closure_eq] at hi
  exact hi.eq isGenericPoint_closure

/-- The inverse equivalence is the actual morphism on underlying points. -/
@[simp]
theorem genericPointsEquivOfGeometricallyIrreducible_symm_apply (x : genericPoints X) :
    ((f.genericPointsEquivOfGeometricallyIrreducible hf).symm x).val = f x.val := by
  simpa only [Equiv.apply_symm_apply] using
    (f.genericPointsEquivOfGeometricallyIrreducible_apply hf
      ((f.genericPointsEquivOfGeometricallyIrreducible hf).symm x)).symm

include hf in
/-- Two generic points over the same point coincide. This asserts no such uniqueness for
arbitrary points of a positive-dimensional fiber. -/
theorem genericPoints_injective_of_geometricallyIrreducible :
    Function.Injective (fun x : genericPoints X => f x.val) := by
  intro x x' h
  apply (f.genericPointsEquivOfGeometricallyIrreducible hf).symm.injective
  apply Subtype.ext
  simpa only [genericPointsEquivOfGeometricallyIrreducible_symm_apply] using h

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/AlgebraicGeometry/Geometrically/Irreducible.lean:85-93"
  "specialization" "Native component correspondence for arbitrary schemes, composed with generics"]
  genericPointsEquivOfGeometricallyIrreducible
  genericPointsEquivOfGeometricallyIrreducible_closure

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Topology/Sober.lean:293-331"
  "ingredient" "Native sober-space generic-point and irreducible-component equivalences"]
  genericPointsEquivOfGeometricallyIrreducible

end AlgebraicGeometry.Scheme.Hom
