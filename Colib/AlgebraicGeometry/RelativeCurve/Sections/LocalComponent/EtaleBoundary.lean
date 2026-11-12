/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleIntegralBase
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.BoundaryBaseChange

/-!
# The full boundary at an integral original etale neighborhood

On the integral marked refinement, the exact native affine coordinate ring is a domain.
The original finite projective-line cover and its nonempty etale chart then force the entire
retained boundary on every actual normal component to meet every base fiber. Normality and
Noetherianity of the curve model are supplied from its original etale base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

set_option backward.isDefEq.respectTransparency false in
/-- On an integral original affine etale neighborhood, the same original full boundary is
surjective over the base. Finiteness alone is not used to infer nonemptiness. The integral
neighborhood itself is supplied by `exists_integral_etaleNeighborhood_refinement`. -/
theorem exists_etaleNeighborhood_normalComponent_surjectiveBoundary
    {S : Scheme.{u}} [QuasiSeparatedSpace S]
    {A : Type u} [CommRing A] [IsLocallyNoetherian (Spec (.of A))]
    (α : Spec (.of A) ⟶ S) [Smooth α] [IsSeparated α] [QuasiCompact α]
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ Spec (.of A))
    (C : EtaleNeighborhood (mk α) ξ)
    [IsIntegral ((etaleNeighborhoodToSmooth (mk α) ξ).obj C).left]
    {N Y E D : Scheme.{u}} [IsNormal N] [IsIntegral N]
    (p : N ⟶ Spec (.of A)) [IsProper p]
    (π : N ⟶ projectiveLine A) [IsFinite π]
    (hπ : π ≫ (projectiveLine A ↘ Spec (.of A)) = p)
    (j : Y ⟶ N) (a : Y ⟶ Spec (.of (Polynomial A)))
    (ha : a ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = j ≫ p)
    (hj : j ≫ π = a ≫ projectiveLineXChart A)
    (e : E ⟶ N) [IsOpenImmersion e] [Nonempty E]
    (c : E ⟶ Spec (.of (Polynomial A))) [Etale c]
    (hc : c ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) = e ≫ p)
    (he : e ≫ π = c ≫ projectiveLineXChart A)
    (b : D ⟶ N) (hb : Set.range b = (Set.range j)ᶜ)
    (x : (pullback p (etaleNeighborhoodHom (mk α) ξ C).left : Scheme.{u})) :
    ∃ U : (pullback p (etaleNeighborhoodHom (mk α) ξ C).left : Scheme.{u}).Opens,
      (U : Set (pullback p (etaleNeighborhoodHom (mk α) ξ C).left : Scheme.{u})) =
        _root_.irreducibleComponent x ∧
      Surjective (pullback.fst U.ι
        (pullback.fst (pullback.fst p (etaleNeighborhoodHom (mk α) ξ C).left) b) ≫
          U.ι ≫ pullback.snd p (etaleNeighborhoodHom (mk α) ξ C).left) := by
  have : IsLocallyNoetherian (mk α).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of A)))
  have := etaleNeighborhood_pullback_isNoetherian (mk α) ξ p C
  have := etaleNeighborhood_pullback_isNormal (mk α) ξ p C
  have := isDomain_etaleNeighborhood_ring (mk α) ξ C
  refine ⟨normalComponentOpen x, rfl, ?_⟩
  exact surjective_baseChanged_normalComponentBoundary_of_etale_chart
    (R := C.obj.left.unop) p (etaleNeighborhoodHom (mk α) ξ C).left
      π hπ j a ha hj e c hc he b hb x

end AlgebraicGeometry.Scheme.SmoothSite
