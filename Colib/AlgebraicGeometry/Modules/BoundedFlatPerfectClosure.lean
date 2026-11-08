/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfect
public import Colib.AlgebraicGeometry.Modules.PerfectKernel
public import Colib.Algebra.Homology.MappingCone.WeakMap

/-!
# Shifts and Cones of Bounded Above Flat Perfect Complexes

The actual signed shift and mapping cone preserve native perfectness, flat terms and explicit
upper bounds. The cone proof uses its original rotated short exact sequence.

Adapted from `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Closure.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-- The actual shifted complex has upper term bound `b - n` and the same flat sheaves. -/
theorem boundedAboveFlatPerfectComplex_shift
    {K : CochainComplex (OXMod.{u, u, u} X) ℤ}
    (hK : boundedAboveFlatPerfectComplex X K) (n : ℤ) :
    boundedAboveFlatPerfectComplex X (K⟦n⟧) := by
  obtain ⟨hp, ⟨b, hb⟩, hf⟩ := hK
  refine ⟨isPerfectComplex_shift X hp n,
    ⟨b - n, (CochainComplex.isStrictlyLE_iff _ _).2 ?_⟩, fun i => hf (i + n)⟩
  intro i hi
  change IsZero (K.X (i + n))
  exact K.isZero_of_isStrictlyLE b (i + n) (by omega)

/-- The original mapping cone is still bounded above, flat and perfect. -/
theorem boundedAboveFlatPerfectComplex_mappingCone
    {K L : CochainComplex (OXMod.{u, u, u} X) ℤ}
    (hK : boundedAboveFlatPerfectComplex X K) (hL : boundedAboveFlatPerfectComplex X L)
    (f : K ⟶ L) : boundedAboveFlatPerfectComplex X (CochainComplex.mappingCone f) :=
  boundedAboveFlatPerfectComplex_of_shortExact
    (CochainComplex.mappingCone_triangle_shortExact f)
    hL (boundedAboveFlatPerfectComplex_shift hK 1)

end AlgebraicGeometry.RingedSpace
