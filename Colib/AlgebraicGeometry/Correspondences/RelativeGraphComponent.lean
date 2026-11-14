/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphLiftCycle
public import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward

/-!
# Scheme-level support equation of a relative graph component

Unlike pointwise coordinate provenance, this equation
retains residue-field information and can be composed with an incidence map.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable (U Y : SmoothSite (Spec (CommRingCat.of k)))

/-- The entire reduced image component satisfies the retained-source equation
as an equality of scheme morphisms, not just an equality of underlying points. -/
theorem image_component_source_eq (z : pullback (C := Scheme) U.hom Y.hom) :
    (integralComponentAt (ambientLift k U Y z)).subschemeι ≫
        pullback.snd U.hom (SmoothSite.product U Y).hom ≫ pullback.fst U.hom Y.hom =
      (integralComponentAt (ambientLift k U Y z)).subschemeι ≫
        pullback.fst U.hom (SmoothSite.product U Y).hom := by
  let e := integralComponentMap (ambientLift k U Y) z
  let : IsIso e := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion
    (ambientLift k U Y) z
  apply (cancel_epi e).mp
  simp only [e, ← Category.assoc, integralComponentMap_subschemeι]
  simp [Category.assoc, SmoothSite.product_hom]

end AlgebraicGeometry.Cor.RelativeGraph
