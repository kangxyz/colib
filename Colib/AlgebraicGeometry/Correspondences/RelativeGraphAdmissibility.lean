/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphOver
public import Colib.AlgebraicGeometry.Chow.WholePolynomialEndpointPushforward

/-! # Admissibility reflection along the actual closed relative graph -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {V U Y : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U)

/-- Retaining the target copy of the source does not change the true source map. -/
@[reassoc (attr := simp)]
theorem ambientOver_fst :
    ambientOver k (Y := Y) f ≫
        pullback.fst V.hom (pullback.fst U.hom Y.hom ≫ U.hom) =
      pullback.fst V.hom Y.hom := by
  simp [ambientOver, graphTargetMap, SmoothSite.product_hom]

/-- Admissibility reflects through the actual closed graph, via its canonical
isomorphism on reduced point closures. No generic dominance is postulated. -/
theorem admissible_of_ambientOver (z : pullback (C := Scheme) V.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint V.hom (SmoothSite.product U Y).hom
      (ambientOver k f z)) :
    IsFiniteCorrespondencePoint V.hom Y.hom z := by
  let e := integralComponentMap (ambientOver k (Y := Y) f) z
  let : IsIso e := AlgebraicCycle.integralComponentMap_isIso_of_isClosedImmersion
    (ambientOver k (Y := Y) f) z
  let p := (integralComponentAt z).subschemeι ≫ pullback.fst V.hom Y.hom
  let r := (integralComponentAt (ambientOver k f z)).subschemeι ≫
    pullback.fst V.hom (SmoothSite.product U Y).hom
  have he : e ≫ r = p := by
    dsimp only [e, r, p]
    rw [← Category.assoc, integralComponentMap_subschemeι]
    simp [Category.assoc, SmoothSite.product_hom]
  have : IsFinite r := hz.1
  refine ⟨?_, ?_⟩
  · change IsFinite p
    rw [← he]
    infer_instance
  · change Set.range p ∈ irreducibleComponents V.left
    rw [range_eq_range_of_surjective p r e he]
    exact hz.2

end AlgebraicGeometry.Cor.RelativeGraph
