/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PrincipalEndpointSupportCodimension
public import Colib.AlgebraicGeometry.Correspondences.Principal.PrincipalEndpointOrderCycle
public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialFamily

/-! # Whole original polynomial principal source cycles at zero and one -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X C V W B : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (q : C ⟶ X) [IsProper q] [IsIntegral C] [IsNoetherian C]
    (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (v : W ⟶ C) [IsOpenImmersion v] [IsIntegral W]
    (b : B ⟶ W) [Nonempty B]
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
    [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]

omit [IsIntegral C] [IsIntegral W] [IsNoetherian C] in
include j hcover in
/-- The original full boundary geometry places every original principal-support
endpoint generic in original curve codimension one. No support flatness or
endpoint-cycle certificate is supplied. -/
theorem principalFamily_support_endpoint_coheight
    (z : parameterSpace (q ≫ p))
    (hz : letI := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
      z ∈ (principalCycle (parameterSpace (q ≫ p))
        (ambientRationalFunction (q ≫ p) v f)).support)
    (c : k) (e : genericPoints (pullback (C := Scheme) (endpoint p c)
      ((integralComponentAt z).subschemeι ≫ lineMap p q))) :
    Order.coheight (sourceEndpointToCurve p q c (integralComponentAt z).subschemeι e.val) = 1 := by
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  let := isIntegral_integralComponentAt z
  have : IsAffineHom (projection p) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsAffine (parameterSpace p) := isAffine_of_isAffineHom (projection p)
  have : IsProper (lineMap p q) :=
    MorphismProperty.of_isPullback (lineMap_isPullback p q).flip inferInstance
  have : IsAffineHom (projection (j ≫ (q ≫ p))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback _ _).flip inferInstance
  have : (parameterSpace (j ≫ (q ≫ p))).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ (q ≫ p)))
  have : SmoothOfRelativeDimension 1 (lineMap (q ≫ p) j ≫ lineMap p q) :=
    MorphismProperty.of_isPullback
      ((lineMap_isPullback (q ≫ p) j).paste_horiz (lineMap_isPullback p q)).flip inferInstance
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  let : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤
  let : Nonempty (parameterSpace p) := ⟨endpoint p 0 (genericPoint X)⟩
  let : IsIntegral (parameterSpace p) :=
    isIntegral_of_isOpenImmersion (affinePolynomialIso p).inv
  let i := (integralComponentAt z).subschemeι
  let m := i ≫ lineMap p q
  have : IsFinite m := principalFamily_support_isFinite p q j v b hcover f hf z hz
  have hrange : Set.range m = Set.univ := by
    simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using
      principalCycle_support_dominates_component (lineMap p q) (lineMap (q ≫ p) j)
        (ambientUnitOpen (q ≫ p) v f)
        (complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf)
        (ambientUnitSection (q ≫ p) v f) (isUnit_ambientUnitSection (q ≫ p) v f) z hz
  have : IsDominant m := ⟨by change Dense (Set.range m); rw [hrange]; exact dense_univ⟩
  let r := PrincipalBoundary.retainedMap (lineMap (q ≫ p) j)
    (ambientUnitOpen (q ≫ p) v f)
    (complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf)
    (ambientUnitSection (q ≫ p) v f) (isUnit_ambientUnitSection (q ≫ p) v f) ⟨z, hz⟩
  have hr : r ≫ lineMap (q ≫ p) j = i := PrincipalBoundary.retainedMap_inclusion _ _ _ _ _ _
  exact sourceEndpoint_generic_original_coheight p q c j i r hr e

omit [IsIntegral C] [IsIntegral W] in
include j hcover in
/-- The actual signed whole source endpoint cycle has no coefficients away from
original curve codimension one, by the original full boundary geometry. -/
theorem signedSourceEndpointCycle_eq_zero_of_coheight_ne_one
    (c : k) (x : C) (hx : Order.coheight x ≠ 1) :
    letI := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
    signedSourceEndpointCycle p q c (ambientRationalFunction (q ≫ p) v f) x = 0 := by
  classical
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  let Z := principalCycle (parameterSpace (q ≫ p)) (ambientRationalFunction (q ≫ p) v f)
  let := Z.finite_support.fintype
  unfold signedSourceEndpointCycle
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro z _
  let i := (integralComponentAt z.val).subschemeι
  let E := pullback (endpoint p c) (i ≫ lineMap p q)
  let := sourceEndpoint_isNoetherian p q c i
  change Z z.val * finiteCyclePushforward (sourceEndpointToCurve p q c i)
    (AlgebraicCycle.fundamentalCycle E) x = 0
  suffices finiteCyclePushforward (sourceEndpointToCurve p q c i)
      (AlgebraicCycle.fundamentalCycle E) x = 0 by rw [this, mul_zero]
  by_contra hn
  have hm : x ∈ (finiteCyclePushforward (sourceEndpointToCurve p q c i)
      (AlgebraicCycle.fundamentalCycle E)).support := hn
  obtain ⟨e, he, rfl⟩ := finiteCyclePushforward_support_subset _ _ hm
  exact hx (principalFamily_support_endpoint_coheight p q j v b hcover f hf z.val z.property c
    ⟨e, AlgebraicCycle.support_fundamentalCycle_subset E he⟩)

include j hcover in
/-- Both actual whole signed source endpoint cycles are determined: zero cancels,
and one is the original curve's native principal cycle with unchanged orders. -/
theorem signedSourceEndpointCycle_zero_one :
    letI := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
    signedSourceEndpointCycle p q 0 (ambientRationalFunction (q ≫ p) v f) = 0 ∧
    signedSourceEndpointCycle p q 1 (ambientRationalFunction (q ≫ p) v f) =
      principalCycle C (curveRationalFunction v f) := by
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  have hfn : f ≠ 0 := by
    intro hz
    have H := hf
    rw [hz, map_zero] at H
    exact zero_ne_one H
  have H (x : C) :
      signedSourceEndpointCycle p q 0 (ambientRationalFunction (q ≫ p) v f) x = 0 ∧
      signedSourceEndpointCycle p q 1 (ambientRationalFunction (q ≫ p) v f) x =
        principalCycle C (curveRationalFunction v f) x := by
    by_cases hx : Order.coheight x = 1
    · exact signedSourceEndpointCycle_zero_one_of_coheight p q v f hfn x hx
    · rw [signedSourceEndpointCycle_eq_zero_of_coheight_ne_one p q j v b hcover f hf 0 x hx,
        signedSourceEndpointCycle_eq_zero_of_coheight_ne_one p q j v b hcover f hf 1 x hx,
        principalCycle_apply, Scheme.ord_eq_zero_of_coheight_neq_one hx]
      exact ⟨rfl, rfl⟩
  constructor
  · apply Function.locallyFinsuppWithin.ext
    exact fun x => (H x).1
  · apply Function.locallyFinsuppWithin.ext
    exact fun x => (H x).2

end AlgebraicGeometry.PrincipalFamilyUnitOpen
