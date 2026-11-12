/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointFundamentalSum
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ClosedSectionCut

/-!
# The native value of a weighted component cut

The native correspondence obtained by summing the cuts of the original
integral components with their generic weights has the actual weighted
endpoint cycle as its value.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme Scheme.AffineLineFiber AlgebraicCycle

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))}
  {D : Scheme.{u}} [IsNoetherian D]

/-- The value of the signed sum of the actual component correspondences is
the whole weighted endpoint on the retained support. -/
theorem weighted_closedSupport_cut_val
    (f : D ⟶ Spec (.of (Polynomial k))) (a : k)
    (m : D ⟶ pullback X.hom Y.hom) [IsFinite m]
    (c : genericPoints D → (Cor.mk X ⟶ Cor.mk Y))
    (hc : ∀ z : genericPoints D,
      let j := (integralComponentAt z.val).subschemeι
      letI : IsNoetherian (fiber (j ≫ f) a) :=
        isNoetherian_of_finiteType (inclusion (j ≫ f) a ≫ j)
      (c z).val = finiteCyclePushforward ((inclusion (j ≫ f) a ≫ j) ≫ m)
        (fundamentalCycle (fiber (j ≫ f) a))) :
    letI := (fundamentalCycle_genericPoints_finite D).fintype
    (∑ z : genericPoints D,
      ((Module.length (D.presheaf.stalk z.val) (D.presheaf.stalk z.val)).toNat : ℤ) • (c z)).val =
      finiteCyclePushforward m (finiteCyclePushforward (inclusion f a)
        (polynomialEndpointMap f a (fundamentalCycle D))) := by
  classical
  let : Fintype (genericPoints D) := (fundamentalCycle_genericPoints_finite D).fintype
  let w (z : genericPoints D) : ℤ :=
    (Module.length (D.presheaf.stalk z.val) (D.presheaf.stalk z.val)).toNat
  change (finiteCorrespondences X.hom Y.hom).subtype (∑ z : genericPoints D, w z • c z) = _
  rw [map_sum, finiteCyclePushforward_polynomialEndpointMap_fundamentalCycle_eq_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul]
  exact congrArg (w z • ·) (hc z)

end AlgebraicGeometry.Cor
