/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.PolynomialEndpointFiber
public import Colib.AlgebraicGeometry.Correspondences.Principal.FiniteCutPushforward
public import Colib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk

/-!
# The literal polynomial parameter in the actual endpoint kernel

The original polynomial section is the cartesian pullback of scalar evaluation.
Its kernel therefore uses the existing full polynomial endpoint-fibre equation,
not a reduced support or a chosen unrelated Cartier generator.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The original polynomial endpoint is literally the cartesian scalar-evaluation fibre. -/
theorem endpoint_parameter_isPullback (c : k) :
    IsPullback (endpoint p c) p
      (pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))
      (Stacks.Chow.PolynomialEndpointFiber.endpoint c) := by
  apply IsPullback.of_right (h₁₂ := projection p)
    (h₂₂ := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
    (v₁₃ := p)
  · rw [endpoint_projection]
    have he : Stacks.Chow.PolynomialEndpointFiber.endpoint c ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = 𝟙 _ := by
      rw [Stacks.Chow.PolynomialEndpointFiber.endpoint, ← Spec.map_comp]
      have h : CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k) ≫
          CommRingCat.ofHom (Polynomial.evalRingHom c) = 𝟙 (CommRingCat.of k) := by
        ext a
        exact Polynomial.eval_C
      rw [h, Spec.map_id]
    rw [he]
    exact IsPullback.of_id_fst
  · exact pullback.lift_snd _ _ _
  · exact IsPullback.of_hasPullback _ _

/-- The actual global parameter equation pulled from the original affine line. -/
abbrev endpointEquation (c : k) : Γ(parameterSpace p, ⊤) :=
  Stacks.Chow.PolynomialEndpointFiber.equation
    (pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c

/-- The original endpoint and native scalar-evaluation fibre have identical
kernel ideal sheaves, including nilpotent structure. -/
theorem endpoint_ker_eq_parameterFiber (c : k) :
    (endpoint p c).ker =
      (Stacks.Chow.PolynomialEndpointFiber.fiberInclusion
        (pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))
        c).ker := by
  have H := (endpoint_parameter_isPullback p c).flip
  rw [← H.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso]

/-- The full ideal sheaf of the actual endpoint has the literal parameter equation. -/
theorem endpoint_ker_stalk_eq_parameter (c : k) (x : parameterSpace p) :
    IdealSheafData.stalk (endpoint p c).ker x =
      Ideal.span {(parameterSpace p).presheaf.germ ⊤ x (by trivial) (endpointEquation p c)} := by
  rw [endpoint_ker_eq_parameterFiber]
  exact Stacks.Chow.PolynomialEndpointFiber.fiberInclusion_ker_stalk _ _ _

/-- The actual endpoint stalk map has exactly the full literal parameter kernel. -/
theorem endpoint_stalkMap_ker_eq_parameter (c : k) (x : X) :
    RingHom.ker ((endpoint p c).stalkMap x).hom =
      Ideal.span {((parameterSpace p).presheaf.germ ⊤ (endpoint p c x)
        (by trivial) (endpointEquation p c))} := by
  have H := (endpoint_parameter_isPullback p c).flip
  let : IsClosedImmersion (endpoint p c) := by
    rw [← H.isoPullback_hom_snd]
    infer_instance
  rw [← IdealSheafData.stalk_ker_of_isClosedImmersion, endpoint_ker_stalk_eq_parameter]

/-- At zero the actual equation is the original global polynomial coordinate. -/
@[simp] theorem endpointEquation_zero : endpointEquation p 0 = parameter p := by
  simp only [endpointEquation, Stacks.Chow.PolynomialEndpointFiber.equation,
    map_zero, sub_zero, parameter]

/-- At one the actual equation is the original coordinate minus one. -/
@[simp] theorem endpointEquation_one : endpointEquation p 1 = parameter p - 1 := by
  simp only [endpointEquation, Stacks.Chow.PolynomialEndpointFiber.equation,
    map_one, map_sub, parameter]

end AlgebraicGeometry.PrincipalFamilyUnitOpen

namespace Stacks.Chow.PolynomialEndpointFiber

/-- The literal endpoint equation respects the original composition of scheme maps. -/
theorem equation_comp {k : Type u} [Field k] {P Q : Scheme.{u}}
    (f : P ⟶ Spec (.of (Polynomial k))) (i : Q ⟶ P) (c : k) :
    equation (i ≫ f) c = i.appTop (equation f c) := by
  simp only [equation, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]

/-- Dominance alone makes the literal endpoint equation nonzero. In particular,
no flatness of an integral finite support is required. -/
theorem equation_ne_zero_of_isDominant {k : Type u} [Field k] {P : Scheme.{u}}
    [IsIntegral P] (f : P ⟶ Spec (.of (Polynomial k))) [IsDominant f] (c : k) :
    equation f c ≠ 0 := by
  let : Nonempty (⊤ : P.Opens) := ⟨⟨genericPoint P, by trivial⟩⟩
  let : Nonempty (⊤ : (Spec (.of (Polynomial k))).Opens) :=
    ⟨⟨genericPoint (Spec (.of (Polynomial k))), by trivial⟩⟩
  intro hz
  have H := dominantFunctionFieldMap_globalSection f
    ((Scheme.ΓSpecIso (.of (Polynomial k))).inv (Polynomial.X - Polynomial.C c))
  change _ = P.germToFunctionField ⊤ (equation f c) at H
  rw [hz, map_zero] at H
  have hb := (dominantFunctionFieldMap f).injective (H.trans (map_zero _).symm)
  have hs := (Spec (.of (Polynomial k))).germToFunctionField_injective ⊤
    (hb.trans (map_zero _).symm)
  exact Polynomial.X_sub_C_ne_zero c
    ((ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Polynomial k))).inv).1
      (hs.trans (map_zero _).symm))

end Stacks.Chow.PolynomialEndpointFiber
