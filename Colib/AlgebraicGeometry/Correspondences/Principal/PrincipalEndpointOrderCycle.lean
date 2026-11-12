/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PrincipalEndpointSourceCycle
public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointOriginalCodimension

/-! # Original signed source endpoint cycles and original curve orders -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X C W : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : C ⟶ X) [IsIntegral C] [IsNoetherian C]
    [IsIntegral (parameterSpace (q ≫ p))] [IsNoetherian (parameterSpace (q ≫ p))]
    (v : W ⟶ C) [IsOpenImmersion v] [IsIntegral W]

/-- Every original codimension-one curve point is computed on an internally
chosen actual affine chart. Both signed whole source endpoint coefficients are
therefore determined by the unchanged original curve order. -/
@[colib_tag "COL-1097", colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/AlgebraicGeometry/Chow/RationalEquivalence/FlatPullbackPrincipalDiviso\
    r.lean:585-627"
  "ingredient" "Original local fraction and order as full quotient-length difference; the \
    support and endpoint assembly is proved here."]
theorem signedSourceEndpointCycle_zero_one_of_coheight
    (f : Γ(W, ⊤)) (hf : f ≠ 0) [Nonempty (ambientUnitOpen (q ≫ p) v f)]
    (x : C) (hx : Order.coheight x = 1) :
    signedSourceEndpointCycle p q 0 (ambientRationalFunction (q ≫ p) v f) x = 0 ∧
    signedSourceEndpointCycle p q 1 (ambientRationalFunction (q ≫ p) v f) x =
      C.ord (curveRationalFunction v f) x := by
  obtain ⟨y, hy⟩ := C.affineCover.covers x
  let U := C.affineCover.X (C.affineCover.idx x)
  let u : U ⟶ C := C.affineCover.f (C.affineCover.idx x)
  change u y = x at hy
  have : Nonempty U := ⟨y⟩
  have : IsIntegral U := isIntegral_of_isOpenImmersion u
  have : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian u
  have : IsNoetherian U := {}
  have : IsAffineHom (projection (u ≫ (q ≫ p))) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have : IsAffine (parameterSpace (u ≫ (q ≫ p))) :=
    isAffine_of_isAffineHom (projection (u ≫ (q ≫ p)))
  have : IsLocallyNoetherian (parameterSpace (u ≫ (q ≫ p))) :=
    LocallyOfFiniteType.isLocallyNoetherian (lineMap (q ≫ p) u)
  have : IsNoetherian (parameterSpace (u ≫ (q ≫ p))) := {}
  have hcy : Order.coheight y = 1 := by
    rw [← coheight_eq_of_isOpenImmersion u, hy]
    exact hx
  have H := ambientPrincipalSupportCuts_zero_one v (q ≫ p) u f hf y hcy
  rw [signedSourceEndpointCycle_apply, signedSourceEndpointCycle_apply]
  simpa only [hy] using H

end AlgebraicGeometry.PrincipalFamilyUnitOpen
