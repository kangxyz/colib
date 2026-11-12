/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointLengthBalance
public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointTorCuts

/-!
# Whole original endpoint fundamental cycles under finite pushforward

Finite dominant maps between original integral supports preserve the full
endpoint cycle with the original generic residue degree. Smoothness and
normality are required only on the original affine base, never on the supports.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- Finite support over the original Noetherian base gives a whole Noetherian endpoint. -/
theorem polynomialEndpoint_isNoetherian {k : Type u} [CommRing k]
    {X D : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsNoetherian X]
    (n : D ⟶ parameterSpace p) [IsFinite n] (c : k) :
    IsNoetherian (pullback (C := Scheme) (endpoint p c) n) :=
  { toIsLocallyNoetherian :=
      LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (endpoint p c) n)
    toCompactSpace :=
      QuasiCompact.compactSpace_of_compactSpace (pullback.fst (endpoint p c) n) }

/-- Native finite pushforward of the full original endpoint fundamental cycle
is its actual generic source degree times the full original target endpoint cycle. -/
theorem polynomialEndpoint_fundamentalCycle_pushforward
    {k : Type u} [Field k] {X C D : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [IsNoetherian X] [Smooth p]
    (n : D ⟶ parameterSpace p) [IsFinite n] [IsDominant n] [IsIntegral D]
    (j : C ⟶ D) [IsFinite j] [IsDominant j] [IsIntegral C] (c : k) :
    letI := polynomialEndpoint_isNoetherian p n c
    letI := polynomialEndpoint_isNoetherian p (j ≫ n) c
    finiteCyclePushforward (polynomialEndpointMap p n j c)
      (AlgebraicCycle.fundamentalCycle (pullback (C := Scheme) (endpoint p c) (j ≫ n))) =
      (j.residueDegree (genericPoint C) : ℤ) •
        AlgebraicCycle.fundamentalCycle (pullback (C := Scheme) (endpoint p c) n) := by
  let := polynomialEndpoint_isNoetherian p n c
  let := polynomialEndpoint_isNoetherian p (j ≫ n) c
  let : Smooth (projection p) := by
    have := PrincipalFamilyEndpointCuts.projection_smoothOfRelativeDimension p
    exact SmoothOfRelativeDimension.smooth 1 _
  let : IsLocallyNoetherian (parameterSpace p) :=
    LocallyOfFiniteType.isLocallyNoetherian (projection p ≫ p)
  let : IsLocallyNoetherian D := LocallyOfFiniteType.isLocallyNoetherian n
  let : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian j
  let : Surjective p := ⟨fun y => ⟨genericPoint X, Subsingleton.elim _ _⟩⟩
  let : IsDominant (pullback.snd p
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) := inferInstance
  let r := polynomialEndpointMap p n j c
  apply Function.locallyFinsuppWithin.ext
  intro y
  change finiteCyclePushforward r _ y =
    (j.residueDegree (genericPoint C) : ℤ) *
      AlgebraicCycle.fundamentalCycle (pullback (endpoint p c) n) y
  rw [finiteCyclePushforward_apply]
  by_cases hy : y ∈ genericPoints (pullback (C := Scheme) (endpoint p c) n)
  · rw [AlgebraicCycle.fundamentalCycle_apply_generic _ ⟨y, hy⟩,
      ← polynomialEndpoint_finsum_stalkLength p n j c ⟨y, hy⟩]
    apply finsum_mem_congr rfl
    intro x hx
    have hxgen := r.mem_genericPoints_of_image_generic x (hx.symm ▸ hy)
    rw [AlgebraicCycle.fundamentalCycle_apply_generic _ ⟨x, hxgen⟩]
  · rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem _ y hy, mul_zero]
    apply finsum_mem_eq_zero_of_forall_eq_zero
    intro x hx
    have hxnot : x ∉ genericPoints (pullback (C := Scheme) (endpoint p c) (j ≫ n)) := by
      intro hxgen
      have H := polynomialEndpoint_generic_image_generic_of_smooth p (j ≫ n) c
        (pullback.fst (endpoint p c) n) r (polynomialEndpointMap_fst p n j c) ⟨x, hxgen⟩
      exact hy (hx ▸ H)
    rw [AlgebraicCycle.fundamentalCycle_apply_of_notMem _ x hxnot, zero_mul]

end AlgebraicGeometry.PrincipalFamilyUnitOpen
