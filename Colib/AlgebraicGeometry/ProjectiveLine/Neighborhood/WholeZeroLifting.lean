/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.Neighborhood.NativeMarkedMaps
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.WholePolynomialProducer

/-!
# Constructed second correction on the whole original punctured line

The only geometric inputs are the original affine polynomial open containing
the entire zero and a base point. The native projective line, missing boundary,
full zero marking, actual finite projective coefficient, global graph frame,
common base frames and signed relative pencil are all constructed. In the
output, U is literally top, so the independent source is the entire D(X) over
the resulting base open. No local-zero or correction witness is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil
open AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood

variable {k : Type u} [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (b : Spec (.of R) ⟶ Spec (.of k)) [Smooth b]
  (O : (Spec (.of (Polynomial R))).Opens) [IsAffine O.toScheme]

/-- The actual identity finite projective presentation. -/
abbrev compactProjection : projectiveSpaceOverRing 1 (.of R) ⟶ Spec (.of R) :=
  (𝟙 (projectiveSpaceOverRing 1 (.of R))) ≫
    (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))

omit [IsNoetherianRing R] [IsAffine O.toScheme] in
@[reassoc] theorem inclusion_projection :
    (O.ι ≫ chart R) ≫ compactProjection R = O.ι ≫ coordinateLineProjection R := by
  simp only [compactProjection, Category.id_comp, Category.assoc, chart_projection]

local instance : IsAffine (puncture R).toScheme := IsAffineOpen.Spec_basicOpen _
local instance : IsAffine (punctureOpen R O).toScheme :=
  punctureOpen_affine R O (show IsAffineOpen O from ‹IsAffine O.toScheme›)

local instance : SmoothOfRelativeDimension 1
    (retainedInclusion R O ≫ compactProjection R) := by
  simpa only [compactProjection, Category.id_comp] using
    (inferInstance : SmoothOfRelativeDimension 1
      (retainedInclusion R O ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))))

local notation "q" => coordinateLineProjection R
local notation "π" => compactProjection R
local notation "j" => O.ι ≫ chart R
local notation "hq" => inclusion_projection R O
set_option quotPrecheck false in
local notation "a" => (puncture R).ι
local notation "v" => retainedInclusion R O
local notation "φ" => overlapToRetained R O
local notation "hφ" => overlapToRetained_projective R O

/-- The signed second lift exists after an actual base-only neighborhood.
The beta source is the literal whole puncture pullback; alpha is the original
open pullback, and the target is the entire retained original puncture over V. -/
theorem exists_wholeZero_base_lifting
    (hO : Set.range (polynomialZero R) ⊆ O) (w : Spec (.of R))
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V), w ∈ V ∧
      ∃ hW : IsAffineOpen (parameterOpen q ⊤ V),
        letI : IsAffine V.toScheme := hV
        letI : IsAffine (parameterOpen q ⊤ V).toScheme := hW
        PresheafWithTransfers.HasRestrictionDifferenceLifting P
          (refinedGraph b q ⊤ V π j O.ι hq a v φ hφ)
          (refinedBeta b q ⊤ V π j O.ι hq a)
          (refinedAlpha b q ⊤ V π j O.ι hq a) := by
  let : IsFinite (coordinateMark R R (Polynomial.evalRingHom 0) ≫ q) := by
    change IsFinite (polynomialZero R ≫ polynomialProjection R)
    rw [polynomialZero_projection]
    infer_instance
  let : IsFinite (boundaryInclusion R O ≫ π) := by
    simpa only [compactProjection, Category.id_comp] using boundary_finite R O hO
  have hc : ∀ x : projectiveSpaceOverRing 1 (.of R),
      x ∈ Set.range v ∨ x ∈ Set.range (boundaryInclusion R O) ∨
        x ∈ Set.range (zeroLift R O hO ≫ j) := by
    intro x
    simpa only [zeroLift_projective] using retained_boundary_zero_cover R O x
  exact exists_wholePolynomial_base_lifting R R b 1 (𝟙 _) j O.ι hq a
    (Polynomial.evalRingHom 0) (zeroLift R O hO) (zeroLift_original R O hO)
    (zeroLift_isPullback R O hO) (boundaryInclusion R O)
    (inclusion_disjoint_boundary R O) (puncture_disjoint_zero R) v hc φ hφ w P hP

end AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
