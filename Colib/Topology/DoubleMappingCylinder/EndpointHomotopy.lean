/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DoubleMappingCylinder.Gap

/-! # The full original cylinder homotopy between the two endpoint composites -/
/-! Adapted from `Quillen/Topology/DoubleMappingCylinder/EndpointHomotopy.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section
noncomputable section
open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval
universe u
namespace TopCat.DoubleCylinder
variable {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
variable {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}

/-- The original stored cylinder gives the actual under-source homotopy,
with time first and no replacement of either endpoint map. -/
def endpointHomotopy (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e) :
    ((gapLeftEndpoint e).comp f.hom).Homotopy ((gapRightEndpoint e).comp g.hom) where
  toFun z := l (z.2, ULift.up z.1)
  continuous_toFun := l.hom.continuous.comp (by fun_prop)
  map_zero_left a := (gap f g sq a).property.1
  map_one_left a := (gap f g sq a).property.2

/-- The entire track is the original full cylinder, without reparametrization. -/
@[simp] theorem endpointHomotopy_apply
    (sq : IsPushout (TopCat.intervalEndpoints A) (endMap f g) l e) (t : unitInterval) (a : A) :
    endpointHomotopy f g sq (t, a) = l (a, ULift.up t) := rfl

end TopCat.DoubleCylinder
