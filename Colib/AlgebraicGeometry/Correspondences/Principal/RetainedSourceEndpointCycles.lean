/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialSourceEndpointCycles
public import Colib.AlgebraicGeometry.Chow.NoetherianPushforward

/-! # Original whole source endpoint cycles on the unchanged retained open -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace Stacks.Chow

/-- Native Noetherian pushforward through an open immersion preserves each
original coefficient; its residue degree is literally one. -/
theorem noetherianCyclePushforward_apply_of_isOpenImmersion
    {U C : Scheme.{u}} [IsNoetherian U] (j : U ⟶ C) [IsOpenImmersion j]
    (Z : AlgebraicCycle U ℤ) (x : U) : noetherianCyclePushforward j Z (j x) = Z x := by
  classical
  rw [noetherianCyclePushforward_apply, ← finsum_set_coe_eq_finsum_mem]
  rw [finsum_eq_single _ ⟨x, by simp⟩]
  · rw [residueDegree_eq_one_of_isPreimmersion]
    simp
  · intro z hz
    exact (hz (Subtype.ext (j.isEmbedding.injective z.property))).elim

end Stacks.Chow

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- An actual open subscheme of the original Noetherian curve is Noetherian. -/
theorem retainedCurve_isNoetherian {C V : Scheme.{u}} [IsNoetherian C]
    (j : V ⟶ C) [IsOpenImmersion j] : IsNoetherian V := by
  let : NoetherianSpace V := j.isEmbedding.isInducing.noetherianSpace
  let : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian j
  exact {}

variable {k : Type u} [Field k] {X C V W B : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : C ⟶ X) [IsIntegral C] [IsNoetherian C]
    (j : V ⟶ C) [IsOpenImmersion j] [V.IsQuasiAffine]
    (v : W ⟶ C) [IsOpenImmersion v]
    (b : B ⟶ W) [Nonempty B]
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
    [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]

/-- The original support factorization into the retained polynomial open gives
its unchanged whole endpoint map to the original retained curve. -/
def retainedSourceEndpointMap (c : k)
    (z : letI := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
      (principalCycle (parameterSpace (q ≫ p))
        (ambientRationalFunction (q ≫ p) v f)).support) :
    pullback (endpoint p c) ((integralComponentAt z.val).subschemeι ≫ lineMap p q) ⟶ V := by
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  have : IsAffineHom (projection (j ≫ (q ≫ p))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback _ _).flip inferInstance
  have : (parameterSpace (j ≫ (q ≫ p))).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ (q ≫ p)))
  let r := PrincipalBoundary.retainedMap (lineMap (q ≫ p) j)
    (ambientUnitOpen (q ≫ p) v f)
    (complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf)
    (ambientUnitSection (q ≫ p) v f) (isUnit_ambientUnitSection (q ≫ p) v f) z
  exact pullback.snd (endpoint p c) ((integralComponentAt z.val).subschemeι ≫ lineMap p q) ≫
    r ≫ projection (j ≫ (q ≫ p))

omit [IsIntegral C] [IsNoetherian C] in
/-- The retained endpoint map keeps the same original curve point and support. -/
@[reassoc (attr := simp)]
theorem retainedSourceEndpointMap_inclusion (c : k)
    (z : letI := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
      (principalCycle (parameterSpace (q ≫ p))
        (ambientRationalFunction (q ≫ p) v f)).support) :
    retainedSourceEndpointMap p q j v b hcover f hf c z ≫ j =
      sourceEndpointToCurve p q c (integralComponentAt z.val).subschemeι := by
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  unfold retainedSourceEndpointMap
  rw [sourceEndpointToCurve_projection, Category.assoc, Category.assoc, ← lineMap_projection]
  have H := PrincipalBoundary.retainedMap_inclusion (lineMap (q ≫ p) j)
    (ambientUnitOpen (q ≫ p) v f)
    (complement_subset_ambientUnitOpen (q ≫ p) j v b hcover f hf)
    (ambientUnitSection (q ≫ p) v f) (isUnit_ambientUnitSection (q ≫ p) v f) z
  simpa only [Category.assoc] using congrArg
    (fun a => pullback.snd (endpoint p c) ((integralComponentAt z.val).subschemeι ≫
      lineMap p q) ≫ a ≫ projection (q ≫ p)) H

/-- The signed whole source endpoint cycle is retained on the original open. -/
def retainedSignedSourceEndpointCycle (c : k) : AlgebraicCycle V ℤ := by
  classical
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  let Z := principalCycle (parameterSpace (q ≫ p)) (ambientRationalFunction (q ≫ p) v f)
  let := Z.finite_support.fintype
  exact ∑ z : Z.support,
    letI := sourceEndpoint_isNoetherian p q c (integralComponentAt z.val).subschemeι
    Z z.val • noetherianCyclePushforward (retainedSourceEndpointMap p q j v b hcover f hf c z)
      (AlgebraicCycle.fundamentalCycle _)

omit [IsIntegral C] in
/-- Native pushforward through the original retained inclusion recovers the
same whole original source endpoint cycle, including all signed collisions. -/
theorem retainedSignedSourceEndpointCycle_inclusion (c : k) :
    letI := retainedCurve_isNoetherian j
    letI := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
    noetherianCyclePushforward j (retainedSignedSourceEndpointCycle p q j v b hcover f hf c) =
      signedSourceEndpointCycle p q c (ambientRationalFunction (q ≫ p) v f) := by
  classical
  let := retainedCurve_isNoetherian j
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  let Z := principalCycle (parameterSpace (q ≫ p)) (ambientRationalFunction (q ≫ p) v f)
  let := Z.finite_support.fintype
  unfold retainedSignedSourceEndpointCycle signedSourceEndpointCycle
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  let := sourceEndpoint_isNoetherian p q c (integralComponentAt z.val).subschemeι
  rw [map_zsmul, noetherianCyclePushforward_comp_apply, retainedSourceEndpointMap_inclusion,
    noetherianCyclePushforward_eq_finiteCyclePushforward]

local instance {A D : Scheme.{u}} (i : A ⟶ D) [IsOpenImmersion i]
    [IsIntegral A] [IsIntegral D] : IsDominant i :=
  ⟨i.isOpenEmbedding.isOpen_range.dense ⟨i (genericPoint A), Set.mem_range_self _⟩⟩

variable [IsAffine X] [IsIntegral X] [Smooth p] [IsProper q]
    [SmoothOfRelativeDimension 1 (j ≫ q)] [IsIntegral W] [IsIntegral V]

/-- The two whole signed source endpoint cycles on the unchanged original
retained curve are zero and its original restricted principal cycle. -/
theorem retainedSignedSourceEndpointCycle_zero_one :
    letI := retainedCurve_isNoetherian j
    retainedSignedSourceEndpointCycle p q j v b hcover f hf 0 = 0 ∧
    retainedSignedSourceEndpointCycle p q j v b hcover f hf 1 =
      principalCycle V (j.functionFieldMap (curveRationalFunction v f)) := by
  let := retainedCurve_isNoetherian j
  let := nonempty_ambientUnitOpen_of_boundary (q ≫ p) v b f hf
  have H := signedSourceEndpointCycle_zero_one p q j v b hcover f hf
  constructor
  · apply Function.locallyFinsuppWithin.ext
    intro x
    have H0 := congrArg (fun Z : AlgebraicCycle C ℤ => Z (j x))
      (retainedSignedSourceEndpointCycle_inclusion p q j v b hcover f hf 0)
    rw [noetherianCyclePushforward_apply_of_isOpenImmersion, H.1] at H0
    exact H0
  · apply Function.locallyFinsuppWithin.ext
    intro x
    have H1 := congrArg (fun Z : AlgebraicCycle C ℤ => Z (j x))
      (retainedSignedSourceEndpointCycle_inclusion p q j v b hcover f hf 1)
    rw [noetherianCyclePushforward_apply_of_isOpenImmersion, H.2] at H1
    rw [← functionFieldEquiv_openImmersion_eq_schemeFunctionFieldMap j]
    exact H1.trans (principalCycle_functionFieldEquiv_openImmersion_apply j _ x).symm

end AlgebraicGeometry.PrincipalFamilyUnitOpen
