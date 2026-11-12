/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.Neighborhood.WholeZeroCylinder
public import Mathlib.RingTheory.Smooth.Basic

/-! # Actual original coefficient localization from a selected zero point

Adapted from the original zero-point lifting argument at motivic
`a6805c4a87cdfd7717dd7a94039246a167f15380`. The coefficient algebra is the
literal Localization.Away r of the original R. The entire new Spec R[r^-1]
zero section is retained, and the independent second correction is then
constructed over an actual affine base open containing the chosen lift.
No first correction or desired original-target lift is assumed here.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.RelativeCurvePencil
open AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
variable {k R S : Type u} [Field k] [CommRing R] [CommRing S]

/-- The actual inverse-image original polynomial open, with its original scalar map. -/
abbrev polynomialScalarOpen (f : R →+* S) (O : (Spec (.of (Polynomial R))).Opens) :
    (Spec (.of (Polynomial S))).Opens :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ⁻¹ᵁ O

local instance (A : Type u) [CommRing A] : IsAffine (puncture A).toScheme :=
  IsAffineOpen.Spec_basicOpen _

local instance (A : Type u) [CommRing A] (U : (Spec (.of (Polynomial A))).Opens)
    [IsAffine U.toScheme] : IsAffine (punctureOpen A U).toScheme :=
  punctureOpen_affine A U (show IsAffineOpen U from ‹IsAffine U.toScheme›)

local instance (A : Type u) [CommRing A] (U : (Spec (.of (Polynomial A))).Opens) :
    SmoothOfRelativeDimension 1 (retainedInclusion A U ≫ compactProjection A) := by
  simpa only [compactProjection, Category.id_comp] using
    (inferInstance : SmoothOfRelativeDimension 1
      (retainedInclusion A U ≫ (projectiveSpaceOverRing 1 (.of A) ↘ Spec (.of A))))

section Localized
variable [Algebra k R] [Algebra.Smooth k R]
  (R) (O : (Spec (.of (Polynomial R))).Opens) [IsAffine O.toScheme]

/-- Starting with only the selected zero point, construct the true original-base
localization and the full native torus correction. The final base open is the
one produced by the simultaneous whole-boundary coefficient framing. -/
theorem exists_zeroPoint_native_torus_lifting
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (w : Spec (.of R)) (hw : polynomialZero R w ∈ O) :
    ∃ r : R, w ∈ PrimeSpectrum.basicOpen r ∧
      let S := Localization.Away r
      letI : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away r
      letI : Algebra.Smooth k S := Algebra.Smooth.comp k R S
      let O₂ := polynomialScalarOpen (algebraMap R S) O
      ∃ hO₂ : IsAffineOpen O₂,
        letI : IsAffine O₂.toScheme := hO₂
        Set.range (polynomialZero S) ⊆ O₂ ∧
        ∃ w' : Spec (.of S),
          Spec.map (CommRingCat.ofHom (algebraMap R S)) w' = w ∧
          ∃ (V : (Spec (.of S)).Opens) (hV : IsAffineOpen V), w' ∈ V ∧
            letI : IsAffine V.toScheme := hV
            let q := coordinateLineProjection S
            letI : IsAffine (parameterOpen q ⊤ V).toScheme := by
              change IsAffineOpen (parameterOpen q ⊤ V)
              have h : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
              simpa only [parameterOpen, top_inf_eq] using h
            let b := Spec.map (CommRingCat.ofHom (algebraMap k S))
            PresheafWithTransfers.HasRestrictionDifferenceLifting P
              (refinedGraph b q ⊤ V (compactProjection S) (O₂.ι ≫ chart S) O₂.ι
                (inclusion_projection S O₂) (puncture S).ι (retainedInclusion S O₂)
                (overlapToRetained S O₂) (overlapToRetained_projective S O₂))
              (wholeZeroBeta (k := k) S O₂ V)
              (refinedAlpha b q ⊤ V (compactProjection S) (O₂.ι ≫ chart S) O₂.ι
                (inclusion_projection S O₂) (puncture S).ι) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨r, hr, hO₂, hzero⟩ := exists_affine_whole_zero_base_restriction R O
    (show IsAffineOpen O from ‹IsAffine O.toScheme›) w hw
  let S := Localization.Away r
  let : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away r
  let : Algebra.Smooth k S := Algebra.Smooth.comp k R S
  let O₂ := polynomialScalarOpen (algebraMap R S) O
  let : IsAffine O₂.toScheme := hO₂
  have hw' : w ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    change w ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away r)))
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨w', hw'⟩ := hw'
  obtain ⟨V, hV, hwV, hL⟩ :=
    exists_wholeZero_native_torus_lifting (k := k) S O₂ hzero w' P hP
  exact ⟨r, hr, hO₂, hzero, w', hw', V, hV, hwV, hL⟩

end Localized
end AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine.ZeroNeighborhood
