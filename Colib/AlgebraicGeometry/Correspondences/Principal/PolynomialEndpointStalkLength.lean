/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointParameterCuts

/-!
# Full original polynomial endpoint stalk lengths

The actual endpoint pullback stalk is the quotient by the literal pulled
parameter equation. The equality is in extended natural lengths, before taking
integers, and includes the entire nilpotent structure of the fibre.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [Field k] {X D : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (m : D ⟶ parameterSpace p) (c : k)

/-- The full kernel on the original support fibre is the literal pulled parameter. -/
theorem polynomialEndpoint_stalkMap_ker
    (x : pullback (C := Scheme) (endpoint p c) m) :
    RingHom.ker ((pullback.snd (endpoint p c) m).stalkMap x).hom =
      Ideal.span {(D.presheaf.germ ⊤ (pullback.snd (endpoint p c) m x) (by trivial)
        (Stacks.Chow.PolynomialEndpointFiber.equation
          (m ≫ pullback.snd p (Spec.map (CommRingCat.ofHom
            (Polynomial.C : k →+* Polynomial k)))) c))} := by
  let a := m ≫ pullback.snd p
    (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))
  let e := pullback.snd (endpoint p c) m
  let H := ((IsPullback.of_hasPullback (endpoint p c) m).flip.paste_vert
    (endpoint_parameter_isPullback p c)).flip
  have he : e = H.isoPullback.hom ≫ Stacks.Chow.PolynomialEndpointFiber.fiberInclusion a c :=
    H.isoPullback_hom_snd.symm
  let : IsClosedImmersion e := by rw [he]; infer_instance
  have hk : e.ker = (Stacks.Chow.PolynomialEndpointFiber.fiberInclusion a c).ker := by
    rw [he, Scheme.Hom.ker_comp_of_isIso]
  change RingHom.ker (e.stalkMap x).hom = _
  rw [← IdealSheafData.stalk_ker_of_isClosedImmersion, hk]
  exact Stacks.Chow.PolynomialEndpointFiber.fiberInclusion_ker_stalk a c (e x)

/-- The full actual fibre stalk has precisely the full original parameter-cut
length on the unchanged support, including infinite lengths when present. -/
theorem polynomialEndpoint_stalk_length
    (x : pullback (C := Scheme) (endpoint p c) m) :
    Module.length ((pullback (endpoint p c) m).presheaf.stalk x)
      ((pullback (endpoint p c) m).presheaf.stalk x) =
      Module.length (D.presheaf.stalk (pullback.snd (endpoint p c) m x))
        (D.presheaf.stalk (pullback.snd (endpoint p c) m x) ⧸
          Ideal.span {(D.presheaf.germ ⊤ (pullback.snd (endpoint p c) m x) (by trivial)
            (Stacks.Chow.PolynomialEndpointFiber.equation
              (m ≫ pullback.snd p (Spec.map (CommRingCat.ofHom
                (Polynomial.C : k →+* Polynomial k)))) c))}) := by
  let H := (endpoint_parameter_isPullback p c).flip
  let : IsClosedImmersion (endpoint p c) := by
    rw [← H.isoPullback_hom_snd]
    infer_instance
  let e := pullback.snd (endpoint p c) m
  let φ := (e.stalkMap x).hom
  have hs := SurjectiveOnStalks.stalkMap_surjective e x
  have HL := (Module.length_eq_of_surjective
    (Ideal.Quotient.mk_surjective (I := RingHom.ker φ))).trans
      (Module.length_eq_of_ringEquiv (φ.quotientKerEquivOfSurjective hs))
  have hk : RingHom.ker φ = _ := polynomialEndpoint_stalkMap_ker p m c x
  rw [hk] at HL
  exact HL.symm

end AlgebraicGeometry.PrincipalFamilyUnitOpen
