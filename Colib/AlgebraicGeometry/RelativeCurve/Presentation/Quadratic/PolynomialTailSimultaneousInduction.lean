/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.ActualPolynomialNeighborhoodPreimage
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.NeighborhoodRepresentativeSurjective
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.SeparableCoefficientStructuralMono

/-! # Polynomial-tail simultaneous induction

UNVERIFIED integration candidate. All lower-dimensional hypotheses are discharged
by Nat induction, but this file and its positive-step dependency still require
production validation. No completed public rigidity endpoint is claimed.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe u
namespace QuadraticIncidence.InfinityChart
local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

variable (K Ω : Type u) [Field K] [Field Ω] [IsAlgClosed Ω]
    (P : PresheafWithTransfers.{u + 1} K) (hP : PresheafWithTransfers.IsA1Invariant P)
    (n : ℕ)
    (hn : ∀ (V : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj V)), (n + 1) • z = 0)
    (hnK : IsUnit ((n + 1 : ℕ) : K))

include hP hn hnK

/-- Successor for all finite separable coefficient fields simultaneously. -/
theorem polynomialTailIsomorphisms_succ_of_actual_neighborhoods
    (d : ℕ)
    (hLower : PolynomialTailIsomorphisms K Ω ((PresheafWithTransfers.toPresheaf K).obj P) d) :
    PolynomialTailIsomorphisms K Ω ((PresheafWithTransfers.toPresheaf K).obj P) (d + 1) := by
  intro E _ _ _ _ ξ hs
  let X := SmoothSite.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin (d + 1)) E))))
  let : IsAffine X.left := inferInstanceAs (IsAffine (Spec (.of (MvPolynomial (Fin (d + 1)) E))))
  let Q := (PresheafWithTransfers.toPresheaf K).obj P
  let g : X ⟶ base (Spec (.of K)) := homMk X.hom (by change X.hom ≫ 𝟙 _ = X.hom; simp)
  let f := Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin (d + 1)) E)))
  have hf : f ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)) = X.hom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  let : Mono (etaleNeighborhoodValuePullback g (ξ := ξ) rfl Q) :=
    mono_structuralNeighborhoodPullback_of_separable_coefficient K E X f hf ξ hs Q
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(AddCommGrpCat.mono_iff_injective _).mp inferInstance, ?_⟩
  apply etaleNeighborhoodValuePullback_surjective_of_representatives g rfl Q
  intro A b
  let U := (etaleNeighborhoodToSmooth X ξ).obj A
  let : IsAffine U.left := inferInstanceAs (IsAffine (Spec A.obj.left.unop))
  let η := etaleNeighborhoodMark X ξ A
  let c := etaleNeighborhoodHom X ξ A ≫ g
  have hcomponent := exists_actual_polynomial_neighborhood_preimage
    K E Ω d ξ hs P hP n hn hnK hLower A b
  have transport (ζ : Spec (.of Ω) ⟶ (base (Spec (.of K))).left)
      (hζ : η ≫ c.left = ζ) :
      ∃ z : etaleNeighborhoodValue (base (Spec (.of K))) ζ Q,
        etaleNeighborhoodValuePullback c (ξ := η) hζ Q z =
          toEtaleNeighborhoodValueFromObject U η Q b := by
    subst ζ
    exact hcomponent
  exact transport _ (by
    change η ≫ ((etaleNeighborhoodHom X ξ A).left ≫ g.left) = ξ ≫ g.left
    rw [← Category.assoc]
    exact congrArg (fun h => h ≫ g.left) (etaleNeighborhoodMark_hom X ξ A))

/-- The simultaneous Nat induction with only coefficient HI and prime-to-char torsion. -/
theorem polynomialTailIsomorphisms_all_dimensions (d : ℕ) :
    PolynomialTailIsomorphisms K Ω ((PresheafWithTransfers.toPresheaf K).obj P) d := by
  induction d with
  | zero => exact polynomialTailIsomorphisms_zero K Ω _
  | succ d ih =>
    exact polynomialTailIsomorphisms_succ_of_actual_neighborhoods K Ω P hP n hn hnK d ih

end QuadraticIncidence.InfinityChart
