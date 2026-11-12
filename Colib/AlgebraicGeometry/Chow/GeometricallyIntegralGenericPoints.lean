/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.GeometricallyIntegralPullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero
import StacksFrontier.Topology.Sober.Generization

/-!
# Generic points under a geometrically integral pullback

For a flat universally open map with geometrically integral fibres,
the native inverse-image generic points identify the generic points
of the target and the source. The proof retains the actual point of
the inverse-image scheme.
-/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace CategoryTheory

universe u

namespace Stacks.Chow

variable {P Q : Scheme.{u}} (f : P ⟶ Q)
  [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] [IsLocallyNoetherian Q]

/-- The inverse-image generic specializes to every point over the
specified original point. -/
theorem geometricallyIntegralPullbackPoint_specializes (x : Q) (p : P) (hp : f p = x) :
    geometricallyIntegralPullbackPoint f x ⤳ p := by
  let J := (integralComponentAt x).comap f
  let : IsIntegral J.subscheme := isIntegral_comap_integralComponentAt f x
  have h : ∃ ξ : genericPoints J.subscheme,
      p ∈ closure {J.subschemeι ξ.val} ∧ f (J.subschemeι ξ.val) = x :=
    exists_comap_genericPoint_over f x p hp
  obtain ⟨ξ, hξ, _⟩ := h
  have he : ξ.val = genericPoint J.subscheme := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using ξ.property
  have hs := specializes_iff_mem_closure.mpr hξ
  rw [he] at hs
  exact hs

/-- The actual inverse-image point of a generic point is generic. -/
theorem geometricallyIntegralPullbackPoint_mem_genericPoints (x : genericPoints Q) :
    geometricallyIntegralPullbackPoint f x.val ∈ genericPoints P := by
  apply mem_genericPoints_of_forall_specializes_eq
  intro p hp
  have h : f p = x.val := forall_specializes_eq_of_mem_genericPoints x.property (f p)
    (by simpa only [geometricallyIntegralPullbackPoint_map] using hp.map f.continuous)
  exact (hp.antisymm (geometricallyIntegralPullbackPoint_specializes f x.val p h)).eq

/-- Generic points of the source are exactly the literal inverse-image
generics of generic points of the target. -/
def geometricallyIntegralGenericPointsEquiv : genericPoints Q ≃ genericPoints P where
  toFun x := ⟨geometricallyIntegralPullbackPoint f x.val,
    geometricallyIntegralPullbackPoint_mem_genericPoints f x⟩
  invFun p := ⟨f p.val, mem_genericPoints_of_flat f p.property⟩
  left_inv x := Subtype.ext (geometricallyIntegralPullbackPoint_map f x.val)
  right_inv p := Subtype.ext (forall_specializes_eq_of_mem_genericPoints p.property _
    (geometricallyIntegralPullbackPoint_specializes f (f p.val) p.val rfl))

end Stacks.Chow
