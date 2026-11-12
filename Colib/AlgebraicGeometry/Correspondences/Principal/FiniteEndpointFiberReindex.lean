/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.FiniteDominantEndpointGenericity
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Actual endpoint generic points and original source fibres

The whole evaluation fibre is reindexed by target endpoint generic points and
points of the original source lying above them. Going down supplies genericity
in the forward direction; quasi-finiteness reflects it in the reverse direction.
All schemes and both maps in the original cartesian square are unchanged.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped Polynomial

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.Scheme.FiniteDominantFace

variable {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  {C D E F : Scheme.{u}} [IsIntegral C]
  (f : C ⟶ Spec (.of A[X])) [IsFinite f] [IsDominant f]
  (e : E ⟶ C) (b : E ⟶ Spec (.of A)) (a : A)
  (hsq : IsPullback e b f (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))))
  (q : F ⟶ Spec (.of A)) [IsFinite q]
  (j : C ⟶ D) [IsFinite j] (i : F ⟶ D) [IsClosedImmersion i]
  (r : E ⟶ F) (hr : r ≫ q = b) (hcart : IsPullback e r j i)

/-- The actual original endpoint generic point retains both its target endpoint
point and the unchanged source support point. -/
def genericEndpointFiberMap (x : genericPoints E) :
    Σ y : genericPoints F, {z : C // j z = i y.val} :=
  ⟨⟨r x.val, original_face_generic_image_generic f e b a hsq q r hr x.val x.property⟩,
    ⟨e x.val, congrArg (fun g : E ⟶ D => g x.val) hcart.w⟩⟩

/-- No source point or target collision is lost: the actual generic-point map is
bijective onto the original source fibres over target endpoint generic points. -/
theorem genericEndpointFiberMap_bijective :
    Function.Bijective (genericEndpointFiberMap f e b a hsq q j i r hr hcart) := by
  have : IsClosedImmersion e := MorphismProperty.of_isPullback hcart.flip inferInstance
  have : IsFinite r := MorphismProperty.of_isPullback hcart inferInstance
  constructor
  · intro x y h
    apply Subtype.ext
    apply e.isEmbedding.injective
    exact congrArg (fun z : Σ y : genericPoints F, {z : C // j z = i y.val} => z.2.val) h
  · rintro ⟨y, z⟩
    obtain ⟨x, hx, hy⟩ := Scheme.exists_preimage_of_isPullback hcart z.val y.val z.property
    have hxgen : x ∈ genericPoints E :=
      r.mem_genericPoints_of_image_generic x (hy.symm ▸ y.property)
    refine ⟨⟨x, hxgen⟩, ?_⟩
    apply Sigma.ext (Subtype.ext hy)
    apply (Subtype.heq_iff_coe_eq (fun z => by
      change j z = i (r x) ↔ j z = i y.val
      rw [hy])).mpr
    exact hx

/-- Canonical actual endpoint/source-fibre reindexing. -/
def genericEndpointFiberEquiv :
    genericPoints E ≃ (Σ y : genericPoints F, {z : C // j z = i y.val}) :=
  Equiv.ofBijective _ (genericEndpointFiberMap_bijective f e b a hsq q j i r hr hcart)

include hcart in
omit [IsIntegral C] [IsFinite j] in
/-- Both residue-degree factors are those of the original maps. Closed endpoint
inclusions have degree one, so the square identifies the finite-source factor. -/
theorem endpoint_residueDegree (x : E) : r.residueDegree x = j.residueDegree (e x) := by
  have : IsClosedImmersion e := MorphismProperty.of_isPullback hcart.flip inferInstance
  have H := congrArg (fun g : E ⟶ D => g.residueDegree x) hcart.w
  simpa only [Stacks.Chow.residueDegree_comp,
    Stacks.Chow.residueDegree_eq_one_of_isPreimmersion, mul_one, one_mul] using H.symm

include hsq hr hcart in
/-- Original source lengths or signed weights pass through both actual finite
maps, retaining every target image collision in the endpoint sum. -/
@[colib_tag "COL-1083"]
theorem finsum_endpoint_source_fibres {Y : Scheme.{u}} (g : F ⟶ Y)
    (L : C → ℤ) (y : Y) :
    (∑ᶠ x : genericPoints E,
      if g (r x.val) = y then L (e x.val) * ((r ≫ g).residueDegree x.val : ℤ) else 0) =
    ∑ᶠ z : (Σ t : genericPoints F, {x : C // j x = i t.val}),
      if g z.1.val = y then L z.2.val *
        ((j.residueDegree z.2.val : ℤ) * (g.residueDegree z.1.val : ℤ)) else 0 := by
  apply finsum_eq_of_bijective
    (genericEndpointFiberMap f e b a hsq q j i r hr hcart)
    (genericEndpointFiberMap_bijective f e b a hsq q j i r hr hcart)
  intro x
  dsimp only [genericEndpointFiberMap]
  rw [Stacks.Chow.residueDegree_comp, endpoint_residueDegree e j i r hcart]
  simp only [Nat.cast_mul, mul_comm]

end AlgebraicGeometry.Scheme.FiniteDominantFace
