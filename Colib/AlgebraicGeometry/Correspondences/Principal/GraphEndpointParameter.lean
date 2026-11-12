/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.EndpointParameterCuts
public import Colib.AlgebraicGeometry.Correspondences.Graph.FlatFiber

/-!
# The literal equation of the original graph-endpoint ambient map

The original graph fibre ambient map is cartesian over the original polynomial
endpoint. Pasting its square with scalar evaluation identifies its full stalk
kernel with the native parameter equation. No correspondence support is flattened
or reduced in this comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.PrincipalFamilyUnitOpen

universe u

namespace Stacks.Chow

/-- The actual graph fibre ambient map is a base change of the original graph map. -/
theorem graphFiberAmbientMap_isPullback {S X Y Z : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (φ : X ⟶ Y) (hφ : φ ≫ g = f) :
    IsPullback (correspondenceGraphFiberAmbientMap f g h φ hφ)
      (pullback.fst f h) (pullback.fst g h) φ := by
  apply IsPullback.of_right (h₁₂ := pullback.snd g h) (h₂₂ := g) (v₁₃ := h)
  · simpa only [correspondenceGraphFiberAmbientMap, pullback.map, pullback.lift_snd,
      Category.comp_id, hφ] using (IsPullback.of_hasPullback f h).flip
  · simp [correspondenceGraphFiberAmbientMap, pullback.map]
  · exact (IsPullback.of_hasPullback g h).flip

variable {k : Type u} [Field k] {X Z : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))

/-- The original graph-endpoint ambient is cartesian over scalar evaluation. -/
theorem graphEndpoint_parameter_isPullback (c : k) :
    IsPullback
      (correspondenceGraphFiberAmbientMap p (projection p ≫ p) h
        (endpoint p c) (by simp))
      (pullback.fst p h ≫ p)
      (pullback.fst (projection p ≫ p) h ≫
        pullback.snd p (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))))
      (PolynomialEndpointFiber.endpoint c) :=
  (graphFiberAmbientMap_isPullback p (projection p ≫ p) h
    (endpoint p c) (by simp)).paste_vert (endpoint_parameter_isPullback p c)

/-- The full graph-endpoint kernel is the literal scalar-evaluation fibre ideal. -/
theorem graphEndpoint_ker_stalk_eq_parameter (c : k)
    (x : pullback (C := Scheme) (projection p ≫ p) h) :
    IdealSheafData.stalk
      (correspondenceGraphFiberAmbientMap p (projection p ≫ p) h
        (endpoint p c) (by simp)).ker x =
      Ideal.span {((pullback (projection p ≫ p) h).presheaf.germ ⊤ x (by trivial)
        (PolynomialEndpointFiber.equation
          (pullback.fst (projection p ≫ p) h ≫
            pullback.snd p (Spec.map
              (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c))} := by
  have H := (graphEndpoint_parameter_isPullback p h c).flip
  rw [← H.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso]
  exact PolynomialEndpointFiber.fiberInclusion_ker_stalk _ _ _

/-- Pulling the full graph-endpoint ideal onto any actual support uses the
literal pulled parameter, retaining the unreduced intersection ideal. -/
theorem graphEndpoint_comap_ker_stalk_eq_parameter {E : Scheme.{u}}
    (i : E ⟶ pullback (projection p ≫ p) h) (c : k) (x : E) :
    IdealSheafData.stalk
      ((correspondenceGraphFiberAmbientMap p (projection p ≫ p) h
        (endpoint p c) (by simp)).ker.comap i) x =
      Ideal.span {(E.presheaf.germ ⊤ x (by trivial)
        (PolynomialEndpointFiber.equation
          (i ≫ pullback.fst (projection p ≫ p) h ≫
            pullback.snd p (Spec.map
              (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)))) c))} := by
  rw [IdealSheafData.stalk_comap, graphEndpoint_ker_stalk_eq_parameter,
    Ideal.map_span, Set.image_singleton]
  have hglobal (s : Γ(pullback (projection p ≫ p) h, ⊤)) :
      i.stalkMap x ((pullback (projection p ≫ p) h).presheaf.germ ⊤ (i x) (by trivial) s) =
        E.presheaf.germ ⊤ x (by trivial) (i.appTop s) := by
    exact Scheme.Hom.germ_stalkMap_apply i ⊤ x (by trivial) s
  rw [hglobal]
  simp only [PolynomialEndpointFiber.equation_comp]

end Stacks.Chow
