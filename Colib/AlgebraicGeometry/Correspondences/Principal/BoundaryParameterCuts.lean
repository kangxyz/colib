/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.BoundaryImageCuts
public import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointParameterCuts

/-!
# The actual parameter is nonzero on original principal images

Original principal supports dominate components of the source. A flat structural
map from that source to the affine line therefore carries their generic points
to the generic point of the line. This proves nonvanishing of the literal endpoint
equation on the actual integral image, without flatness of any principal support.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.PrincipalBoundary

variable {C X Y S V : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  (p : X ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
  [IsAffine X] [V.IsQuasiAffine] (q : C ⟶ X) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (U : C.Opens) [Nonempty U] (hU : (Set.range j)ᶜ ⊆ (U : Set C))
  (f : Γ(C, U)) (hf : IsUnit f)
  (g : V ⟶ Y) (hg : j ≫ q ≫ p = g ≫ t)
  {k : Type u} [Field k] (a : X ⟶ Spec (.of (Polynomial k))) [Flat a]

omit [IsSeparated t] [LocallyOfFiniteType t] in
/-- The original support dominates the affine-line parameter through the flat
structural source map; the support itself is not assumed flat. -/
theorem componentMap_parameter_isDominant (z : support U f) :
    IsDominant (componentMap p t q j U hU f hf g hg z ≫ pullback.fst p t ≫ a) := by
  let := isIntegral_integralComponentAt z.val
  let d := (integralComponentAt z.val).subschemeι ≫ q
  have : IsFinite d := principalCycle_support_isFinite q j U hU f hf z.val z.property
  have he : closure ({d (genericPoint (integralComponentAt z.val).subscheme)} : Set X) =
      Set.range d := by
    simpa only [Set.image_univ, d.isClosedMap.isClosed_range.closure_eq] using
      ((genericPoint_spec (integralComponentAt z.val).subscheme).image d.continuous).def
  have hη : d (genericPoint (integralComponentAt z.val).subscheme) ∈ genericPoints X := by
    rw [genericPoints, Set.mem_ofPred_eq, he]
    exact principalCycle_support_dominates_component q j U hU f hf z.val z.property
  have hline := AlgebraicGeometry.mem_genericPoints_of_flat a hη
  apply ((tfae_isDominant_of_isIntegral
    (componentMap p t q j U hU f hf g hg z ≫ pullback.fst p t ≫ a)).out 1 2).mpr
  rw [← Category.assoc, componentMap_fst]
  simpa only [d, Scheme.Hom.comp_apply, genericPoints_eq_singleton,
    Set.mem_singleton_iff] using hline

omit [IsSeparated t] [LocallyOfFiniteType t] in
/-- The exact integral image also dominates the affine line. -/
theorem imagePoint_parameter_isDominant (z : support U f) :
    IsDominant ((integralComponentAt (imagePoint p t q j U hU f hf g hg z)).subschemeι ≫
      pullback.fst p t ≫ a) := by
  let := isIntegral_integralComponentAt z.val
  have := componentMap_parameter_isDominant p t q j U hU f hf g hg a z
  let e := integralImageMap (componentMap p t q j U hU f hf g hg z)
  have hdom : IsDominant (e ≫
      ((integralComponentAt (imagePoint p t q j U hU f hf g hg z)).subschemeι ≫
        pullback.fst p t ≫ a)) := by
    dsimp only [e, imagePoint]
    rw [← Category.assoc, integralImageMap_inclusion]
    infer_instance
  exact IsDominant.of_comp e _ (H := hdom)

omit [IsSeparated t] [LocallyOfFiniteType t] in
/-- The literal equation used in the finite image cut is genuinely nonzero. -/
theorem imagePoint_endpointEquation_ne_zero (z : support U f) (c : k) :
    PolynomialEndpointFiber.equation
      ((integralComponentAt (imagePoint p t q j U hU f hf g hg z)).subschemeι ≫
        pullback.fst p t ≫ a) c ≠ 0 := by
  let := isIntegral_integralComponentAt (imagePoint p t q j U hU f hf g hg z)
  have := imagePoint_parameter_isDominant p t q j U hU f hf g hg a z
  exact PolynomialEndpointFiber.equation_ne_zero_of_isDominant _ c

/-- The actual literal endpoint cut on the original finite image satisfies the
signed coefficient formula. Nonvanishing is produced from original support dominance,
not supplied as an endpoint assumption. -/
@[colib_tag "COL-1068", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/PrincipalDivisorPushforward.lean:106-114"
  "ingredient" "Finite pushforward of original orders with full residue degrees; the cut- \
    length specialization is proved here."]
theorem componentCorrespondence_endpointCutCoefficient
    [IsLocallyNoetherian (pullback p t)] (z : support U f) (c : k) :
    let D := (integralComponentAt z.val).subscheme
    letI := isIntegral_integralComponentAt z.val
    let r := componentMap p t q j U hU f hf g hg z
    let e := integralImageMap r
    let E := (integralComponentAt (imagePoint p t q j U hU f hf g hg z)).subscheme
    let s := PolynomialEndpointFiber.equation
      ((integralComponentAt (imagePoint p t q j U hU f hf g hg z)).subschemeι ≫
        pullback.fst p t ≫ a) c
    ∀ y, Order.coheight y = 1 →
        (cycle U f) z.val *
          (∑ᶠ x ∈ e.base ⁻¹' {y},
            ((Module.length (D.presheaf.stalk x)
              (D.presheaf.stalk x ⧸ Ideal.span
                {D.presheaf.germ ⊤ x (by trivial) (e.appTop s)})).toNat : ℤ) *
                  (r.residueDegree x : ℤ)) =
        (componentCorrespondence p t q j U hU f hf g hg z).val
            (imagePoint p t q j U hU f hf g hg z) *
          ((Module.length (E.presheaf.stalk y)
            (E.presheaf.stalk y ⧸ Ideal.span
              {E.presheaf.germ ⊤ y (by trivial) s})).toNat : ℤ) := by
  let := isIntegral_integralComponentAt z.val
  dsimp only
  intro y hy
  exact componentCorrespondence_cutCoefficient p t q j U hU f hf g hg z _
    (imagePoint_endpointEquation_ne_zero p t q j U hU f hf g hg a z c) y hy

end Stacks.Chow.PrincipalBoundary
