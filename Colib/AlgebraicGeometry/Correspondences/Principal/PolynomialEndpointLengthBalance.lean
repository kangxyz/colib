/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointFiberMap
public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointStalkLength
public import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointCutCodimension
public import Colib.AlgebraicGeometry.Morphisms.QuasiFinite.Coheight

/-! # Actual full polynomial endpoint fibre length balance -/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X C D : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (n : D ⟶ parameterSpace p) (j : C ⟶ D) (c : k)

private theorem endpoint_closed : IsClosedImmersion (endpoint p c) := by
  let H := (endpoint_parameter_isPullback p c).flip
  rw [← H.isoPullback_hom_snd]
  infer_instance

/-- The actual cartesian square bijects the whole endpoint-map point fibre with
the unchanged source support points above the target support point. -/
theorem polynomialEndpointMap_fiber_bijOn
    (y : pullback (C := Scheme) (endpoint p c) n) :
    Set.BijOn (pullback.snd (endpoint p c) (j ≫ n))
      ((polynomialEndpointMap p n j c) ⁻¹' {y})
      (j ⁻¹' {pullback.snd (endpoint p c) n y}) := by
  let := endpoint_closed p c
  constructor
  · intro x hx
    change j (pullback.snd (endpoint p c) (j ≫ n) x) = _
    have H := congrArg (fun f => f x) (polynomialEndpointMap_snd p n j c)
    exact H.symm.trans (congrArg (pullback.snd (endpoint p c) n) hx)
  constructor
  · intro a _ b _ hab
    exact (pullback.snd (endpoint p c) (j ≫ n)).isEmbedding.injective hab
  · intro z hz
    obtain ⟨x, hx, hy⟩ := Scheme.exists_preimage_of_isPullback
      (polynomialEndpointMap_isPullback p n j c) z y hz
    exact ⟨x, hy, hx⟩

/-- Every generic point of the full endpoint has codimension one in its original
integral support. This does not require finite-support flatness. -/
theorem polynomialEndpoint_generic_coheight [IsIntegral D] [IsLocallyNoetherian D]
    [IsDominant (n ≫ pullback.snd p
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]
    (y : genericPoints (pullback (C := Scheme) (endpoint p c) n)) :
    Order.coheight (pullback.snd (endpoint p c) n y.val) = 1 := by
  let H := ((IsPullback.of_hasPullback (endpoint p c) n).flip.paste_vert
    (endpoint_parameter_isPullback p c)).flip
  let z : genericPoints _ :=
    ⟨H.isoPullback.hom y.val, mem_genericPoints_of_flat H.isoPullback.hom y.property⟩
  have hdim := PolynomialEndpointFiber.fiberInclusion_generic_coheight _ c z
  simpa only [z, PolynomialEndpointFiber.fiberInclusion, ← Scheme.Hom.comp_apply,
    H.isoPullback_hom_snd] using hdim

/-- The full original endpoint stalk lengths satisfy finite degree balance on
all source points above an actual target endpoint generic point. -/
theorem polynomialEndpoint_finsum_stalkLength
    [IsIntegral C] [IsIntegral D] [IsLocallyNoetherian C] [IsLocallyNoetherian D]
    [IsFinite j] [IsDominant j]
    [IsDominant (n ≫ pullback.snd p
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))]
    (y : genericPoints (pullback (C := Scheme) (endpoint p c) n)) :
    (∑ᶠ x ∈ (polynomialEndpointMap p n j c) ⁻¹' {y.val},
      ((Module.length ((pullback (endpoint p c) (j ≫ n)).presheaf.stalk x)
        ((pullback (endpoint p c) (j ≫ n)).presheaf.stalk x)).toNat : ℤ) *
          ((polynomialEndpointMap p n j c).residueDegree x : ℤ)) =
      (j.residueDegree (genericPoint C) : ℤ) *
        ((Module.length ((pullback (endpoint p c) n).presheaf.stalk y.val)
          ((pullback (endpoint p c) n).presheaf.stalk y.val)).toNat : ℤ) := by
  let := endpoint_closed p c
  let s := PolynomialEndpointFiber.equation
    (n ≫ pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c
  have hs : s ≠ 0 := PolynomialEndpointFiber.equation_ne_zero_of_isDominant _ c
  have hy := polynomialEndpoint_generic_coheight p n c y
  have H := finsum_principalCutLength_mul_residueDegree j s hs
    (pullback.snd (endpoint p c) n y.val) hy
    (fun x hx => j.coheight_eq_one_of_locallyQuasiFinite x (hx ▸ hy))
  rw [polynomialEndpoint_stalk_length p n c y.val]
  rw [← H]
  apply finsum_mem_eq_of_bijOn (pullback.snd (endpoint p c) (j ≫ n))
    (polynomialEndpointMap_fiber_bijOn p n j c y.val)
  intro x _
  have hdeg := Scheme.FiniteDominantFace.endpoint_residueDegree
    (pullback.snd (endpoint p c) (j ≫ n)) j (pullback.snd (endpoint p c) n)
    (polynomialEndpointMap p n j c) (polynomialEndpointMap_isPullback p n j c) x
  rw [hdeg, polynomialEndpoint_stalk_length p (j ≫ n) c x]
  have heqn : PolynomialEndpointFiber.equation
      ((j ≫ n) ≫ pullback.snd p
        (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c =
      j.appTop s := by
    rw [Category.assoc, PolynomialEndpointFiber.equation_comp]
  exact congrArg (fun a : Γ(C, ⊤) =>
    ((Module.length (C.presheaf.stalk (pullback.snd (endpoint p c) (j ≫ n) x))
      (C.presheaf.stalk (pullback.snd (endpoint p c) (j ≫ n) x) ⧸ Ideal.span
        {(C.presheaf.germ ⊤ (pullback.snd (endpoint p c) (j ≫ n) x) (by trivial) a)})).toNat : ℤ) *
      (j.residueDegree (pullback.snd (endpoint p c) (j ≫ n) x) : ℤ)) heqn

end AlgebraicGeometry.PrincipalFamilyUnitOpen
