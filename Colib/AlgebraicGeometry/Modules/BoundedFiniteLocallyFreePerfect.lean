/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFiniteLocallyFree
public import Colib.Algebra.Homology.MappingCone.WeakMap
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Perfectness
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RepresentativeIndependence

/-!
# Mapping cones and native perfectness of bounded vector-bundle complexes

The actual rotated cone short exact sequence and the geometric extension theorem prove cone
closure. Native Stacks Tag 0F8I then identifies every bounded finite locally free complex as a
perfect complex. The comparison retains the actual complex and needs no geometric hypothesis.
It does not identify the global finite-free-retract predicate with local freeness.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

variable {X : Scheme.{u}}

/-- The original signed cone stays bounded and finite locally free, by its actual extension. -/
theorem boundedFiniteLocallyFreeComplex_mappingCone {K L : CochainComplex X.Modules ℤ}
    (hK : boundedFiniteLocallyFreeComplex X K) (hL : boundedFiniteLocallyFreeComplex X L)
    (f : K ⟶ L) : boundedFiniteLocallyFreeComplex X (CochainComplex.mappingCone f) :=
  boundedFiniteLocallyFreeComplex_of_shortExact (CochainComplex.mappingCone_triangle_shortExact f)
    hL (boundedFiniteLocallyFreeComplex_shift hK 1)

/-- A native bounded finite locally free complex is a native perfect complex on every scheme. -/
@[colib_tag "COL-0313", stacks 0F8I "The original bounded vector-bundle complex is perfect"]
theorem isPerfectComplex_of_boundedFiniteLocallyFree {K : CochainComplex X.Modules ℤ}
    (hK : boundedFiniteLocallyFreeComplex X K) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K := by
  let : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
  let : HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) :=
    HasDerivedCategory.standard _
  have h := perfect_of_boundedFiniteLocallyFree X
    ⟨(HomotopyCategory.quotient X.Modules (ComplexShape.up ℤ)).obj K,
      (ObjectProperty.strictMap_iff _ _ _).2 ⟨K, hK, rfl⟩⟩
  exact RingedSpace.isPerfectComplex_of_isPerfect_representation.{u, u + 1} h
    ⟨((DerivedCategory.quotientCompQhIso X.Modules).app K).symm⟩

/-- The full inclusion into native perfect complexes keeps every original chain map. -/
def boundedFiniteLocallyFreePerfectInclusion (X : Scheme.{u}) :
    (boundedFiniteLocallyFreeComplex X).FullSubcategory ⥤
      ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  ObjectProperty.ιOfLE (fun _ hK => isPerfectComplex_of_boundedFiniteLocallyFree hK)

instance boundedFiniteLocallyFreePerfectInclusion_additive (X : Scheme.{u}) :
    (boundedFiniteLocallyFreePerfectInclusion X).Additive where
  map_add := by intros; rfl

@[simp]
theorem boundedFiniteLocallyFreePerfectInclusion_obj
    (K : (boundedFiniteLocallyFreeComplex X).FullSubcategory) :
    ((boundedFiniteLocallyFreePerfectInclusion X).obj K).obj = K.obj := rfl

@[simp]
theorem boundedFiniteLocallyFreePerfectInclusion_map
    {K L : (boundedFiniteLocallyFreeComplex X).FullSubcategory} (f : K ⟶ L) :
    ((boundedFiniteLocallyFreePerfectInclusion X).map f).hom = f.hom := rfl

end Stacks.Perfect.BoundedLocallyFreeComplexes
