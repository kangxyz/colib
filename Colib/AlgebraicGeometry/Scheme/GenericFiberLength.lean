/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.RingTheory.LocalRing.Length
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.Topology.Sober.Generization

/-!
# Closed-fiber length at a generic point of an arbitrary scheme

A generic point of the full source is generic in its scheme-theoretic fiber.
If that fiber is reduced, its local ring there is a field. The pinned Stacks
`quotientStalkEquivFiberStalk` identifies it with the quotient by the extended
maximal ideal, compatibly with the actual stalk map. Consequently that ideal is
the target maximal ideal and the closed-fiber factor in Mathlib's local flat
length formula is one.

Only the fiber is assumed reduced: the source may be nonreduced or disconnected.
No Noetherianity, finite length, or residue-field degree-one hypothesis is used.
Point transport is retained explicitly in `stalkMapOverPoint`.

Pinned Stacks source: commit 5ed82d14634e8d9576bb844c7bd4e3da66d450e7,
`StacksFrontier/AlgebraicGeometry/Morphisms/CohenMacaulay/FibreStalk.lean:343-373`
and `StacksFrontier/Topology/Sober/Generization.lean:38-59`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory TopologicalSpace TensorProduct

universe u v
namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A generic point of the source has no proper generization in its fiber. -/
theorem asFiber_mem_genericPoints_of_mem_genericPoints (x : X)
    (hx : x ∈ genericPoints X) : f.asFiber x ∈ genericPoints (f.fiber (f x)) := by
  refine (mem_genericPoints_iff_forall_specializes_eq _).2 fun z hz =>
    (f.fiberι _).isEmbedding.injective ?_
  rw [f.fiberι_asFiber]
  apply forall_specializes_eq_of_mem_genericPoints hx
  simpa only [f.fiberι_asFiber] using hz.map (f.fiberι _).continuous

/-- The actual closed-fiber quotient is a field at a generic point if that fiber is reduced. -/
theorem isField_quotient_map_maximalIdeal_stalkMap (x : X)
    (hx : x ∈ genericPoints X) [IsReduced (f.fiber (f x))] :
    IsField ((X.presheaf.stalk x) ⧸
      Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) :=
  (quotientStalkEquivFiberStalk f x).isField
    (isField_stalk_of_closure_mem_irreducibleComponents (f.fiber (f x))
      (f.asFiber x) (f.asFiber_mem_genericPoints_of_mem_genericPoints x hx))

/-- The maximal-ideal equality is derived from the actual fiber quotient, not assumed. -/
theorem map_maximalIdeal_stalkMap_of_mem_genericPoints (x : X)
    (hx : x ∈ genericPoints X) [IsReduced (f.fiber (f x))] :
    Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
  IsLocalRing.eq_maximalIdeal (Ideal.Quotient.maximal_of_isField _
    (f.isField_quotient_map_maximalIdeal_stalkMap x hx))

/-- The length-one factor is length as a module over the entire source stalk. -/
theorem length_quotient_map_maximalIdeal_stalkMap (x : X)
    (hx : x ∈ genericPoints X) [IsReduced (f.fiber (f x))] :
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸
        Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) = 1 := by
  rw [f.map_maximalIdeal_stalkMap_of_mem_genericPoints x hx]
  exact Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
    ⟨IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x), ⟨LinearEquiv.refl _ _⟩⟩)

/-- Flat extension along the literal local map preserves arbitrary extended-natural lengths. -/
@[stacks 02M1 "Local flat-length formula, with the reduced generic closed-fiber factor evaluated"]
theorem length_baseChange_stalkMap_of_mem_genericPoints [Flat f] (x : X)
    (hx : x ∈ genericPoints X) [IsReduced (f.fiber (f x))]
    (M : Type v) [AddCommGroup M] [Module (Y.presheaf.stalk (f x)) M] :
    letI := (f.stalkMap x).hom.toAlgebra
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⊗[Y.presheaf.stalk (f x)] M) =
        Module.length (Y.presheaf.stalk (f x)) M := by
  let := (f.stalkMap x).hom.toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
    change IsLocalHom (f.stalkMap x).hom
    infer_instance
  let : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  rw [IsLocalRing.length_baseChange]
  change Module.length (Y.presheaf.stalk (f x)) M *
    Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
      Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x)))) = _
  rw [f.length_quotient_map_maximalIdeal_stalkMap x hx, mul_one]

/-- The actual local map over a named base point, including the necessary stalk transport. -/
def stalkMapOverPoint (x : X) (y : Y) (hxy : f x = y) :
    Y.presheaf.stalk y →+* X.presheaf.stalk x :=
  ((Y.presheaf.stalkCongr (.of_eq hxy.symm)).hom ≫ f.stalkMap x).hom

instance stalkMapOverPoint_isLocalHom (x : X) (y : Y) (hxy : f x = y) :
    IsLocalHom (f.stalkMapOverPoint x y hxy) := by
  dsimp only [stalkMapOverPoint]
  infer_instance

/-- Flatness is unchanged by the actual isomorphism between the two named base stalks. -/
theorem stalkMapOverPoint_flat [Flat f] (x : X) (y : Y) (hxy : f x = y) :
    (f.stalkMapOverPoint x y hxy).Flat := by
  apply RingHom.Flat.comp
  · exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  · exact Flat.stalkMap f x

/-- Point transport carries the maximal ideal to the actual maximal ideal before extension. -/
theorem map_maximalIdeal_stalkMapOverPoint (x : X) (y : Y) (hxy : f x = y)
    (hx : x ∈ genericPoints X) [IsReduced (f.fiber (f x))] :
    Ideal.map (f.stalkMapOverPoint x y hxy) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
  change Ideal.map ((f.stalkMap x).hom.comp
    (Y.presheaf.stalkCongr (.of_eq hxy.symm)).hom.hom) _ = _
  rw [← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective _
    (ConcreteCategory.bijective_of_isIso _).surjective]
  exact f.map_maximalIdeal_stalkMap_of_mem_genericPoints x hx

/-- The closed-fiber length is one for the point-transported local algebra as well. -/
theorem length_quotient_map_maximalIdeal_stalkMapOverPoint
    (x : X) (y : Y) (hxy : f x = y) (hx : x ∈ genericPoints X)
    [IsReduced (f.fiber (f x))] :
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ Ideal.map (f.stalkMapOverPoint x y hxy)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))) = 1 := by
  rw [f.map_maximalIdeal_stalkMapOverPoint x y hxy hx]
  exact Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
    ⟨IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      IsLocalRing.maximalIdeal.isMaximal (X.presheaf.stalk x), ⟨LinearEquiv.refl _ _⟩⟩)

/-- The full local flat-length formula with the closed-fiber factor actually evaluated. -/
@[stacks 02M1 "Length preservation along the actual point-transported flat local map"]
theorem length_baseChange_stalkMapOverPoint [Flat f]
    (x : X) (y : Y) (hxy : f x = y) (hx : x ∈ genericPoints X)
    [IsReduced (f.fiber (f x))]
    (M : Type v) [AddCommGroup M] [Module (Y.presheaf.stalk y) M] :
    letI := (f.stalkMapOverPoint x y hxy).toAlgebra
    Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⊗[Y.presheaf.stalk y] M) =
      Module.length (Y.presheaf.stalk y) M := by
  let := (f.stalkMapOverPoint x y hxy).toAlgebra
  let : IsLocalHom (algebraMap (Y.presheaf.stalk y) (X.presheaf.stalk x)) := by
    change IsLocalHom (f.stalkMapOverPoint x y hxy)
    infer_instance
  let : Module.Flat (Y.presheaf.stalk y) (X.presheaf.stalk x) :=
    f.stalkMapOverPoint_flat x y hxy
  rw [IsLocalRing.length_baseChange]
  change Module.length (Y.presheaf.stalk y) M *
    Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
      Ideal.map (f.stalkMapOverPoint x y hxy) (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))) = _
  rw [f.length_quotient_map_maximalIdeal_stalkMapOverPoint x y hxy hx, mul_one]

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/AlgebraicGeometry/Properties.lean:219-236"
  "ingredient" "Only the scheme-theoretic fiber is reduced, not the full source"]
  isField_quotient_map_maximalIdeal_stalkMap

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/RingTheory/LocalRing/Length.lean:105-125"
  "specialization" "The actual closed-fiber factor is proved to be one at a source generic"]
  length_baseChange_stalkMap_of_mem_genericPoints length_baseChange_stalkMapOverPoint

end AlgebraicGeometry.Scheme.Hom
