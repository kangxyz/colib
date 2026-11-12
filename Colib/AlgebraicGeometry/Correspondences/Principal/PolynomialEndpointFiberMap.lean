/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Principal.PolynomialEndpointGenericity
public import Colib.AlgebraicGeometry.Correspondences.Principal.FiniteEndpointFiberReindex

/-!
# Canonical maps between the original polynomial endpoint fibres

The fibre map and its cartesian square are constructed from the original finite
support map. Neither a genericity certificate nor a cartesian-square witness is
an input to the resulting original source-fibre coefficient comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {k : Type u} [CommRing k] {X C D : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) (n : D ⟶ parameterSpace p) (j : C ⟶ D) (c : k)

/-- The canonical original endpoint map induced by the original support morphism. -/
def polynomialEndpointMap :
    pullback (endpoint p c) (j ≫ n) ⟶ pullback (endpoint p c) n :=
  pullback.map (endpoint p c) (j ≫ n) (endpoint p c) n (𝟙 _) j (𝟙 _)
    (by simp) (by simp)

@[reassoc (attr := simp)]
theorem polynomialEndpointMap_fst :
    polynomialEndpointMap p n j c ≫ pullback.fst (endpoint p c) n =
      pullback.fst (endpoint p c) (j ≫ n) := by
  simp only [polynomialEndpointMap, pullback.map, pullback.lift_fst, Category.comp_id]

@[reassoc (attr := simp)]
theorem polynomialEndpointMap_snd :
    polynomialEndpointMap p n j c ≫ pullback.snd (endpoint p c) n =
      pullback.snd (endpoint p c) (j ≫ n) ≫ j := by
  simp only [polynomialEndpointMap, pullback.map, pullback.lift_snd]

/-- The actual endpoint square is a base change of the unchanged support map. -/
theorem polynomialEndpointMap_isPullback :
    IsPullback (pullback.snd (endpoint p c) (j ≫ n)) (polynomialEndpointMap p n j c)
      j (pullback.snd (endpoint p c) n) := by
  apply IsPullback.of_bot (v₂₁ := pullback.fst (endpoint p c) n) (v₂₂ := n)
  · rw [polynomialEndpointMap_fst]
    exact (IsPullback.of_hasPullback (endpoint p c) (j ≫ n)).flip
  · exact (polynomialEndpointMap_snd p n j c).symm
  · exact (IsPullback.of_hasPullback (endpoint p c) n).flip

instance [IsFinite j] : IsFinite (polynomialEndpointMap p n j c) :=
  MorphismProperty.of_isPullback (polynomialEndpointMap_isPullback p n j c) inferInstance

end AlgebraicGeometry.PrincipalFamilyUnitOpen

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

/-- The original smooth affine base, finite support maps, and literal polynomial
endpoint supply the full source-fibre reindex and both residue degrees internally.
Every collision at the unchanged outer target remains in the coefficient sum. -/
@[colib_tag "COL-1084"]
theorem polynomialEndpoint_finsum_source_fibres
    {k : Type u} [Field k] {X C D Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsAffine X] [IsIntegral X] [Smooth p]
    (n : D ⟶ parameterSpace p) [IsFinite n]
    (j : C ⟶ D) [IsFinite j] [IsIntegral C] [IsDominant (j ≫ n)] (c : k)
    (g : pullback (endpoint p c) n ⟶ Y) (L : C → ℤ) (y : Y) :
    (∑ᶠ x : genericPoints (pullback (C := Scheme) (endpoint p c) (j ≫ n)),
      if g (polynomialEndpointMap p n j c x.val) = y then
        L (pullback.snd (endpoint p c) (j ≫ n) x.val) *
          ((polynomialEndpointMap p n j c ≫ g).residueDegree x.val : ℤ) else 0) =
    ∑ᶠ z : (Σ t : genericPoints (pullback (C := Scheme) (endpoint p c) n),
      {x : C // j x = pullback.snd (endpoint p c) n t.val}),
      if g z.1.val = y then L z.2.val *
        ((j.residueDegree z.2.val : ℤ) * (g.residueDegree z.1.val : ℤ)) else 0 := by
  let : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, by trivial⟩⟩
  let : IsDomain Γ(X, ⊤) := IsIntegral.component_integral ⊤
  let : IsAffine (Scheme.SmoothSite.mk p).left := inferInstanceAs (IsAffine X)
  let : IsIntegrallyClosed Γ(X, ⊤) :=
    Scheme.SmoothSite.AffineSectionCoordinates.sections_isIntegrallyClosed
      (Scheme.SmoothSite.mk p)
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Polynomial.evalRingHom (affineScalar p c)))) :=
    IsClosedImmersion.spec_of_surjective _ (Polynomial.eval_surjective _)
  let : IsClosedImmersion (endpoint p c) :=
    MorphismProperty.of_isPullback (affinePolynomialIso_endpoint_isPullback p c).flip
      inferInstance
  exact Scheme.FiniteDominantFace.finsum_endpoint_source_fibres
    ((j ≫ n) ≫ (affinePolynomialIso p).inv)
    (pullback.snd (endpoint p c) (j ≫ n))
    (pullback.fst (endpoint p c) (j ≫ n) ≫ X.isoSpec.hom) (affineScalar p c)
    (polynomialEndpoint_coordinate_isPullback p (j ≫ n) c)
    (pullback.fst (endpoint p c) n ≫ X.isoSpec.hom) j (pullback.snd (endpoint p c) n)
    (polynomialEndpointMap p n j c) (by rw [← Category.assoc, polynomialEndpointMap_fst])
    (polynomialEndpointMap_isPullback p n j c) g L y

end AlgebraicGeometry.PrincipalFamilyUnitOpen
