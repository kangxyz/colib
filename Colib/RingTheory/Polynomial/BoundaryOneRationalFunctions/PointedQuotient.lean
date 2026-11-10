/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.BoundaryOneRationalFunctions.PointedExact
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# The actual signed value after removing the identity-point function

The quotient here is the group of actual admissible localized units modulo the
integer powers of the literal function `X - 1`. Its signed value is constructed
from degree and evaluation at zero. Its kernel is exactly the original
boundary-one subgroup, which embeds in the quotient, and the map is surjective.

This is the algebraic producer for the affine reduced-divisor sequence. It is
not the geometric reduced torus and does not assert a correspondence comparison.
The geometric comparison must carry this literal generator to the actual
unit-one graph before these results can be applied to the motivic cokernel.
-/

@[expose] public noncomputable section

namespace Polynomial.BoundaryOneRationalFunctions

variable {R : Type*} [CommRing R]

/-- The actual admissible subgroup inherits the canonical commutative group of units. -/
instance instCommGroupAdmissibleGroup : CommGroup (admissibleGroup R) :=
  Subgroup.toCommGroup (G := (Ring R)ˣ) (admissibleGroup R)

variable [Nontrivial R]

omit [Nontrivial R] in
/-- Every actual boundary-one function has signed value one. -/
@[simp] theorem signedValueHom_boundaryInclusion (f : group R) :
    signedValueHom (boundaryInclusion f) = 1 := by
  have h := (boundary_iff_degree_zeroValue (boundaryInclusion f)).mp f.property
  change (-1 : Rˣ) ^ fractionDegree (boundaryInclusion f) *
    zeroValueHom (boundaryInclusion f) = 1
  rw [h.1, h.2, zpow_zero, one_mul]

/-- Quotient of actual functions by every signed power of the identity-point function. -/
abbrev pointedGroup (R : Type*) [CommRing R] :=
  admissibleGroup R ⧸ Subgroup.zpowers (identityPointFraction (R := R))

/-- The genuine quotient projection, with no chosen splitting. -/
def toPointed : admissibleGroup R →* pointedGroup R :=
  QuotientGroup.mk' (Subgroup.zpowers identityPointFraction)

omit [Nontrivial R] in
/-- The original identity-point function becomes the multiplicative identity. -/
@[simp] theorem toPointed_identityPoint :
    toPointed (identityPointFraction (R := R)) = 1 :=
  (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)

/-- The actual signed value descends through the literal identity-point quotient. -/
def pointedSignedValue : pointedGroup R →* Rˣ :=
  QuotientGroup.lift (Subgroup.zpowers identityPointFraction) signedValueHom
    (Subgroup.zpowers_le.mpr signedValueHom_identityPoint)

@[simp] theorem pointedSignedValue_toPointed (f : admissibleGroup R) :
    pointedSignedValue (toPointed f) = signedValueHom f := rfl

/-- The boundary-one inclusion followed by the actual quotient map. -/
def pointedBoundary : group R →* pointedGroup R :=
  toPointed.comp boundaryInclusion

/-- Removing the identity-point function does not identify distinct boundary-one functions. -/
theorem pointedBoundary_injective : Function.Injective (pointedBoundary (R := R)) := by
  apply (injective_iff_map_eq_one _).mpr
  intro m hm
  have hmem : boundaryInclusion m ∈ Subgroup.zpowers identityPointFraction :=
    (QuotientGroup.eq_one_iff _).mp hm
  obtain ⟨d, hd⟩ := Subgroup.mem_zpowers_iff.mp hmem
  exact (boundary_identityPoint_intersection m d hd.symm).1

@[simp] theorem pointedSignedValue_pointedBoundary (m : group R) :
    pointedSignedValue (pointedBoundary m) = 1 :=
  signedValueHom_boundaryInclusion m

/-- Exactness is proved for the constructed maps, not assumed as a norm hypothesis. -/
theorem pointedSignedValue_eq_one_iff (x : pointedGroup R) :
    pointedSignedValue x = 1 ↔ ∃ m : group R, pointedBoundary m = x := by
  obtain ⟨f, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.zpowers (identityPointFraction (R := R))) x
  constructor
  · intro hf
    obtain ⟨m, hm⟩ := signedValue_kernel_decomposition f hf
    refine ⟨m, ?_⟩
    change toPointed (boundaryInclusion m) = toPointed f
    rw [hm, map_mul, map_zpow, toPointed_identityPoint, one_zpow, mul_one]
  · rintro ⟨m, hm⟩
    rw [← hm]
    exact pointedSignedValue_pointedBoundary m

/-- The computed signed-value kernel is the range of the actual boundary-one inclusion. -/
theorem pointedSignedValue_ker :
    (pointedSignedValue (R := R)).ker = (pointedBoundary (R := R)).range := by
  ext x
  exact pointedSignedValue_eq_one_iff x

/-- Every unit has an actual localized rational-function preimage in the quotient. -/
theorem pointedSignedValue_surjective :
    Function.Surjective (pointedSignedValue (R := R)) := by
  intro u
  obtain ⟨f, hf⟩ := boundaryInvariant_surjective (R := R) (1, u)
  exact ⟨toPointed f, congrArg Prod.snd hf⟩

variable {S : Type*} [CommRing S] [Nontrivial S]

omit [Nontrivial R] [Nontrivial S] in
/-- Coefficient specialization sends the actual identity-point function to itself. -/
@[simp] theorem admissibleMap_identityPoint (φ : R →+* S) :
    admissibleMap φ (identityPointFraction (R := R)) = identityPointFraction := by
  have hlin : denominatorMap φ (linearDenominator (-1 : Rˣ)) =
      linearDenominator (-1 : Sˣ) := by
    apply Subtype.ext
    simp [denominatorMap, linearDenominator]
  simp only [identityPointFraction, admissibleMap_fraction, hlin, map_one]

/-- Coefficient specialization on the literal identity-point quotient. -/
def pointedMap (φ : R →+* S) : pointedGroup R →* pointedGroup S :=
  QuotientGroup.map _ _ (admissibleMap φ) (by
    intro f hf
    obtain ⟨d, rfl⟩ := Subgroup.mem_zpowers_iff.mp hf
    change admissibleMap φ (identityPointFraction ^ d) ∈
      Subgroup.zpowers identityPointFraction
    rw [map_zpow, admissibleMap_identityPoint]
    exact Subgroup.zpow_mem_zpowers _ _)

omit [Nontrivial R] [Nontrivial S] in
@[simp] theorem pointedMap_toPointed (φ : R →+* S) (f : admissibleGroup R) :
    pointedMap φ (toPointed f) = toPointed (admissibleMap φ f) := rfl

/-- The exact quotient sequence is natural even for noninjective coefficient maps. -/
theorem pointedSignedValue_natural (φ : R →+* S) (x : pointedGroup R) :
    pointedSignedValue (pointedMap φ x) =
      Units.map φ.toMonoidHom (pointedSignedValue x) := by
  obtain ⟨f, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.zpowers (identityPointFraction (R := R))) x
  exact signedValueHom_natural φ f

omit [Nontrivial R] [Nontrivial S] in
/-- Naturality retains the same boundary-one functions, not merely isomorphic kernels. -/
theorem pointedBoundary_natural (φ : R →+* S) (f : group R) :
    pointedMap φ (pointedBoundary f) = pointedBoundary (map φ f) := by
  change toPointed (admissibleMap φ (boundaryInclusion f)) = _
  rw [boundaryInclusion_natural]
  rfl

end Polynomial.BoundaryOneRationalFunctions
