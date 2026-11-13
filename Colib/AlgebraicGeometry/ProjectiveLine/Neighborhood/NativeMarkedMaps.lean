/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.Neighborhood.NativeBoundary
public import Colib.AlgebraicGeometry.Morphisms.Smooth.PolynomialProjection

/-! # Literal marked maps and full retained overlap for the native zero neighborhood -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
variable (R : Type u) [CommRing R] (O : (Spec (.of (Polynomial R))).Opens)

/-- The whole zero section of the polynomial line, induced by evaluation at zero. -/
abbrev polynomialZero : Spec (.of R) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))

/-- The structure map of the polynomial line over the coefficient spectrum. -/
abbrev polynomialProjection : Spec (.of (Polynomial R)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))

@[reassoc (attr := simp)] theorem polynomialZero_projection :
    polynomialZero R ≫ polynomialProjection R = 𝟙 _ := by
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 _ := by ext r; simp
  rw [h, Spec.map_id]

instance : SmoothOfRelativeDimension 1 (polynomialProjection R) :=
  AffineLineEtaleCompactification.polynomialProjection_smooth_one R

/-- The whole base zero factors through the unchanged original neighborhood. -/
def zeroLift (hO : Set.range (polynomialZero R) ⊆ O) : Spec (.of R) ⟶ O.toScheme :=
  IsOpenImmersion.lift O.ι (polynomialZero R) (by simpa only [Scheme.Opens.range_ι] using hO)

@[reassoc (attr := simp)] theorem zeroLift_original
    (hO : Set.range (polynomialZero R) ⊆ O) :
    zeroLift R O hO ≫ O.ι = polynomialZero R := IsOpenImmersion.lift_fac _ _ _

/-- This is the complete Cartesian marking, not just an equality of supports. -/
theorem zeroLift_isPullback (hO : Set.range (polynomialZero R) ⊆ O) :
    IsPullback (zeroLift R O hO) (𝟙 _) O.ι (polynomialZero R) :=
  IsPullback.of_vert_isIso_mono ⟨by simp only [zeroLift_original, Category.id_comp]⟩

@[reassoc] theorem zeroLift_projective
    (hO : Set.range (polynomialZero R) ⊆ O) :
    zeroLift R O hO ≫ O.ι ≫ chart R = zeroSection R := by
  exact zeroLift_original_assoc R O hO (chart R)

instance (hO : Set.range (polynomialZero R) ⊆ O) :
    IsClosedImmersion (zeroLift R O hO ≫ (O.ι ≫ chart R)) := by
  rw [zeroLift_projective]
  infer_instance

/-- The puncture is the entire original D(X), before base restriction. -/
abbrev puncture : (Spec (.of (Polynomial R))).Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)

theorem puncture_disjoint_zero :
    Disjoint (Set.range (puncture R).ι) (Set.range (polynomialZero R)) := by
  apply Set.disjoint_left.mpr
  intro x hx hz
  rw [Scheme.Opens.range_ι] at hx
  exact hx ((mem_range_evalZero_iff R x).mp hz)

/-- The literal overlap maps to the unchanged original punctured neighborhood. -/
def overlapToRetained : pullback O.ι (puncture R).ι ⟶ (punctureOpen R O).toScheme :=
  IsOpenImmersion.lift (punctureOpen R O).ι (pullback.fst O.ι (puncture R).ι ≫ O.ι) (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    refine ⟨(pullback.fst O.ι (puncture R).ι x).property, ?_⟩
    have h := congrArg (fun f => f x) (pullback.condition (f := O.ι) (g := (puncture R).ι))
    change (pullback.fst O.ι (puncture R).ι ≫ O.ι) x ∈ puncture R
    rw [h]
    exact (pullback.snd O.ι (puncture R).ι x).property)

@[reassoc (attr := simp)] theorem overlapToRetained_original :
    overlapToRetained R O ≫ (punctureOpen R O).ι =
      pullback.fst O.ι (puncture R).ι ≫ O.ι := IsOpenImmersion.lift_fac _ _ _

@[reassoc] theorem overlapToRetained_projective :
    overlapToRetained R O ≫ retainedInclusion R O =
      pullback.fst O.ι (puncture R).ι ≫ (O.ι ≫ chart R) := by
  simp only [retainedInclusion, overlapToRetained_original_assoc]

instance : SmoothOfRelativeDimension 1
    (retainedInclusion R O ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))) := by
  rw [retainedInclusion, Category.assoc, chart_projection]
  let : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) :=
    AffineLineEtaleCompactification.polynomialProjection_smooth_one R
  exact smoothOfRelativeDimension_comp (n := 0) (m := 1) _ _

end AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
