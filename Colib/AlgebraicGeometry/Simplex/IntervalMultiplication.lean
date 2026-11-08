/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Simplex.Prism
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Tactic.FinCases

/-!
# Multiplication and contraction on the actual barycentric interval

The interval remains the existing barycentric quotient spectrum `Δ¹`, and
products remain the existing literal scheme fiber products over `Spec R`.
The map constructed here multiplies the second barycentric coordinate:
`(t₀, t₁), (s₀, s₁) ↦ (1 - t₁ * s₁, t₁ * s₁)`.
Consequently vertex zero `(1, 0)` is absorbing and vertex one `(0, 1)` is the
unit. This agrees with the endpoint ordering in the actual prism. It does not
confuse the polynomial chart's retained coordinate `t₀` with `t₁`.

The construction uses the existing barycentric ring universal property and
Mathlib's `Γ`–`Spec` adjunction, so its source need not be affine. In particular
it gives the actual contraction of `U × Δ¹`, for arbitrary objects `U` of the
smooth site and arbitrary commutative coefficient rings. No homotopy
invariance or transfer structure is assumed.

The multiplication is the geometric input used in the proof of MVW2006,
Lemma 2.16, printed p. 17. Together with the endpoint argument of Lemma 2.18
it gives the ordinary-presheaf contraction underlying Corollary 2.19, printed
p. 18. This module makes no claim about transfers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Simplicial BigOperators

universe u

namespace AlgebraicSimplex

variable (R : Type u) [CommRing R]

local notation "I" => Functor.obj (cosimplicialSmoothSite R) (SimplexCategory.mk 1)

/-- The original barycentric coordinate as a global section of the actual interval. -/
def intervalCoordinate (i : Fin 2) : Γ((I).left, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R 1))).inv (coordinate R 1 i)

/-- Pullback from the original barycentric ring, using the native affine counit. -/
def intervalPullback {U : SmoothSite (Spec (.of R))} (f : U ⟶ I) :
    CoordinateRing R 1 →+* Γ(U.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R 1))).inv ≫ f.left.appTop).hom

/-- The second barycentric coordinate pulled back along an actual interval morphism. -/
def intervalValue {U : SmoothSite (Spec (.of R))} (f : U ⟶ I) : Γ(U.left, ⊤) :=
  intervalPullback R f (coordinate R 1 1)

private theorem intervalPullback_constant {U : SmoothSite (Spec (.of R))}
    (f : U ⟶ I) (r : R) :
    intervalPullback R f (constant R 1 r) =
      U.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
  have h := congrArg
    (fun k : CommRingCat.of R ⟶ Γ((I).left, ⊤) => k r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (constant R 1)))
  change (Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R 1))).inv
      (constant R 1 r) =
    (structureMap R 1).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) at h
  exact (congrArg (fun s : Γ((I).left, ⊤) => f.left.appTop s) h).trans
    (congrArg (fun k : U.left ⟶ Spec (.of R) =>
      k.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
        (MorphismProperty.Over.w f))

/-- An actual morphism over `Spec R` to the interval is determined by `t₁`. -/
private theorem interval_hom_ext {U : SmoothSite (Spec (.of R))} {f g : U ⟶ I}
    (h : intervalValue R f = intervalValue R g) : f = g := by
  apply MorphismProperty.Over.Hom.ext
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  change intervalPullback R f = intervalPullback R g
  apply ringHom_ext
  · intro r
    rw [intervalPullback_constant, intervalPullback_constant]
  · intro i
    have hzero : coordinate R 1 0 = 1 - coordinate R 1 1 := by
      apply eq_sub_iff_add_eq.mpr
      exact (Fin.sum_univ_two (fun i => coordinate R 1 i)).symm.trans (sum_coordinate R 1)
    have hz (k : U ⟶ I) :
        intervalPullback R k (coordinate R 1 0) = 1 - intervalValue R k := by
      calc
        _ = intervalPullback R k (1 - coordinate R 1 1) := congrArg _ hzero
        _ = intervalPullback R k 1 - intervalValue R k := map_sub _ _ _
        _ = 1 - intervalValue R k := congrArg (fun s => s - intervalValue R k) (map_one _)
    fin_cases i
    · exact (hz f).trans ((congrArg (fun s => 1 - s) h).trans (hz g).symm)
    · exact h

private theorem intervalPullback_vertexAt (U : SmoothSite (Spec (.of R)))
    (v : Fin 2) (a : CoordinateRing R 1) :
    intervalPullback R (vertexAt R U v) a =
      U.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv
        (vertexEvaluation R v a)) := by
  have h := congrArg
    (fun k : CommRingCat.of (CoordinateRing R 1) ⟶ Γ(Spec (.of R), ⊤) => k a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (vertexEvaluation R v)))
  change U.hom.appTop
    ((Spec.map (CommRingCat.ofHom (vertexEvaluation R v))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (CoordinateRing R 1))).inv a)) = _
  exact congrArg (fun s => U.hom.appTop s) h.symm

@[simp]
private theorem intervalValue_vertexAt_zero (U : SmoothSite (Spec (.of R))) :
    intervalValue R (vertexAt R U 0) = 0 := by
  simp [intervalValue, intervalPullback_vertexAt]

@[simp]
private theorem intervalValue_vertexAt_one (U : SmoothSite (Spec (.of R))) :
    intervalValue R (vertexAt R U 1) = 1 := by
  simp [intervalValue, intervalPullback_vertexAt]

/-- The actual ring map defining multiplication, with images `(1 - s * t, s * t)`. -/
def intervalMultiplicationRingHom :
    CoordinateRing R 1 →+* Γ((SmoothSite.product I I).left, ⊤) :=
  lift
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (SmoothSite.product I I).hom.appTop).hom)
    (fun i => if i = 0 then
      1 - intervalValue R (SmoothSite.productFst I I) *
        intervalValue R (SmoothSite.productSnd I I)
    else intervalValue R (SmoothSite.productFst I I) *
      intervalValue R (SmoothSite.productSnd I I)) (by
        refine (Fin.sum_univ_two _).trans ?_
        rw [ite_eq_left rfl, ite_eq_right (by decide)]
        exact sub_add_cancel _ _)

/-- Multiplication of `t₁` on the original barycentric interval over `Spec R`. -/
def intervalMultiplication : SmoothSite.product I I ⟶ I :=
  SmoothSite.homMk
    (ΓSpec.adjunction.homEquiv (SmoothSite.product I I).left
      (op (CommRingCat.of (CoordinateRing R 1)))
      (CommRingCat.ofHom (intervalMultiplicationRingHom R)).op) (by
    apply ext_to_Spec
    change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      (Spec.map (CommRingCat.ofHom (constant R 1))).appTop ≫
      (ΓSpec.adjunction.homEquiv (SmoothSite.product I I).left
        (op (CommRingCat.of (CoordinateRing R 1)))
        (CommRingCat.ofHom (intervalMultiplicationRingHom R)).op).appTop =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (SmoothSite.product I I).hom.appTop
    rw [← Scheme.ΓSpecIso_inv_naturality_assoc,
      ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change intervalMultiplicationRingHom R (constant R 1 r) = _
    exact lift_constant _ _ _ r)

private theorem intervalMultiplication_pullback :
    intervalPullback R (intervalMultiplication R) = intervalMultiplicationRingHom R := by
  exact congrArg CommRingCat.Hom.hom
    (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
      (CommRingCat.ofHom (intervalMultiplicationRingHom R)))

@[simp]
theorem intervalMultiplication_coordinate_one :
    (intervalMultiplication R).left.appTop (intervalCoordinate R 1) =
      (SmoothSite.productFst I I).left.appTop (intervalCoordinate R 1) *
        (SmoothSite.productSnd I I).left.appTop (intervalCoordinate R 1) := by
  change intervalPullback R (intervalMultiplication R) (coordinate R 1 1) = _
  rw [intervalMultiplication_pullback]
  exact (lift_coordinate _ _ _ 1).trans (ite_eq_right (by decide))

@[simp]
theorem intervalMultiplication_coordinate_zero :
    (intervalMultiplication R).left.appTop (intervalCoordinate R 0) =
      1 - (SmoothSite.productFst I I).left.appTop (intervalCoordinate R 1) *
        (SmoothSite.productSnd I I).left.appTop (intervalCoordinate R 1) := by
  change intervalPullback R (intervalMultiplication R) (coordinate R 1 0) = _
  rw [intervalMultiplication_pullback]
  exact (lift_coordinate _ _ _ 0).trans (ite_eq_left rfl)

private theorem intervalValue_comp_intervalMultiplication
    {U : SmoothSite (Spec (.of R))} (f : U ⟶ SmoothSite.product I I) :
    intervalValue R (f ≫ intervalMultiplication R) =
      intervalValue R (f ≫ SmoothSite.productFst I I) *
        intervalValue R (f ≫ SmoothSite.productSnd I I) := by
  change f.left.appTop ((intervalMultiplication R).left.appTop (intervalCoordinate R 1)) = _
  rw [intervalMultiplication_coordinate_one, map_mul]
  rfl

@[reassoc (attr := simp)]
theorem intervalInclusion_zero_comp_intervalMultiplication :
    intervalInclusion R I 0 ≫ intervalMultiplication R = vertexAt R I 0 := by
  apply interval_hom_ext R
  rw [intervalValue_comp_intervalMultiplication]
  simp only [intervalInclusion_fst, intervalInclusion_snd, intervalValue_vertexAt_zero]
  exact mul_zero _

@[reassoc (attr := simp)]
theorem intervalInclusion_one_comp_intervalMultiplication :
    intervalInclusion R I 1 ≫ intervalMultiplication R = 𝟙 I := by
  apply interval_hom_ext R
  rw [intervalValue_comp_intervalMultiplication]
  simp only [intervalInclusion_fst, intervalInclusion_snd, intervalValue_vertexAt_one]
  exact mul_one _

/-- The two interval projections of `(U × Δ¹) × Δ¹`. -/
def intervalContractionParameters (U : SmoothSite (Spec (.of R))) :
    SmoothSite.product (SmoothSite.product U I) I ⟶ SmoothSite.product I I :=
  SmoothSite.productLift
    (SmoothSite.productFst (SmoothSite.product U I) I ≫ SmoothSite.productSnd U I)
    (SmoothSite.productSnd (SmoothSite.product U I) I)

private theorem intervalInclusion_comp_intervalContractionParameters
    (U : SmoothSite (Spec (.of R))) (v : Fin 2) :
    intervalInclusion R (SmoothSite.product U I) v ≫ intervalContractionParameters R U =
      SmoothSite.productSnd U I ≫ intervalInclusion R I v := by
  apply SmoothSite.product_hom_ext <;> simp [intervalContractionParameters]

/-- The actual interval contraction `(u, t, s) ↦ (u, t * s)`, using coordinate `t₁`. -/
@[colib_ref "MVW2006" "Lecture 2, Lemma 2.16, proof, printed p. 17"
  "generalization" "Actual interval contraction over any commutative base; no transfer claim"]
def intervalContraction (U : SmoothSite (Spec (.of R))) :
    SmoothSite.product (SmoothSite.product U I) I ⟶ SmoothSite.product U I :=
  SmoothSite.productLift
    (SmoothSite.productFst (SmoothSite.product U I) I ≫ SmoothSite.productFst U I)
    (intervalContractionParameters R U ≫ intervalMultiplication R)

@[reassoc (attr := simp)]
theorem intervalInclusion_zero_comp_intervalContraction
    (U : SmoothSite (Spec (.of R))) :
    intervalInclusion R (SmoothSite.product U I) 0 ≫ intervalContraction R U =
      SmoothSite.productFst U I ≫ intervalInclusion R U 0 := by
  apply SmoothSite.product_hom_ext
  · simp [intervalContraction]
  · simp only [Category.assoc, intervalContraction, SmoothSite.productLift_snd]
    rw [← Category.assoc, intervalInclusion_comp_intervalContractionParameters]
    simp

@[reassoc (attr := simp)]
theorem intervalInclusion_one_comp_intervalContraction
    (U : SmoothSite (Spec (.of R))) :
    intervalInclusion R (SmoothSite.product U I) 1 ≫ intervalContraction R U =
      𝟙 (SmoothSite.product U I) := by
  apply SmoothSite.product_hom_ext
  · simp [intervalContraction]
  · simp only [Category.assoc, intervalContraction, SmoothSite.productLift_snd]
    rw [← Category.assoc, intervalInclusion_comp_intervalContractionParameters]
    simp

end AlgebraicSimplex

attribute [colib_tag "COL-0320"] AlgebraicSimplex.intervalMultiplication
attribute [colib_tag "COL-0320"] AlgebraicSimplex.intervalContraction
