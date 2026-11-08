/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.Topology.Sober

/-!
# Native cycles with specified generic coefficients

When the actual set `genericPoints X` is finite, its coefficients assemble as a
finite sum of native `Function.locallyFinsuppWithin.single` cycles. The resulting
object is Mathlib's `AlgebraicCycle X R`. Evaluation gives precisely the specified
coefficient at a generic point and zero elsewhere. Consequently its support is
finite, and every native cycle supported on the generic points is recovered.

The finiteness proof is an explicit lower input. An incidence application must
derive it from the actual incidence geometry; this module does not postulate
Noetherianness, component dominance, or any Tor comparison. Negative integer
coefficients are retained. No fundamental-cycle multiplicities are substituted
for derived-intersection multiplicities.

Implementation provenance: `kangxyz/motivic` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Cycles/GenericCoefficients.lean`, declarations
`IntegralCycle.ofGenericCoefficients` and `toPoints_ofGenericCoefficients_apply`.
This is a fresh direct-native implementation, not the missing historical Colib
file and not a copy of the source's separate `IntegralCycle` representation.
The source consumers are `Composition/Incidence/Cycle.lean` and `TorCycle.lean`.

The mathematical convention is Stacks Project, Tag 02QR, clause (1):
cycles are formal sums of integral closed subschemes, represented in the native
API by their generic points. This finite, ungraded supporting construction does
not assert a dimension condition or any result about intersection multiplicity.
-/

@[expose] public noncomputable section

open TopologicalSpace Function.locallyFinsuppWithin
open scoped BigOperators

attribute [local instance] Classical.propDecidable

universe u v

namespace AlgebraicGeometry.AlgebraicCycle

variable {X : Scheme.{u}} {R : Type v}

section AddCommMonoid

variable [AddCommMonoid R] (hfin : (genericPoints X).Finite)

/-- The native finite sum of the prescribed coefficients at all actual generic points.
The finiteness witness is supplied by the consuming geometry. -/
@[stacks 02QR "(1), finite ungraded cycles supported on actual generic points"]
def ofGenericCoefficients : (genericPoints X → R) →+ AlgebraicCycle X R := by
  classical
  letI := hfin.fintype
  refine
    { toFun := fun c => ∑ x : genericPoints X, single x.val (c x)
      map_zero' := by simp
      map_add' := ?_ }
  intro c d
  apply Function.locallyFinsuppWithin.ext
  intro x
  simp only [coe_sum, Finset.sum_apply, coe_add, Pi.add_apply, single_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  split_ifs <;> simp

/-- The construction uses a literal finite sum of native point cycles. -/
theorem ofGenericCoefficients_eq_sum (c : genericPoints X → R) :
    ofGenericCoefficients hfin c =
      letI := hfin.fintype
      ∑ x : genericPoints X, single x.val (c x) := rfl

open Classical in
/-- The assembled cycle has exactly the prescribed coefficients, and vanishes
at points which are not generic points of irreducible components. -/
theorem ofGenericCoefficients_apply (c : genericPoints X → R) (x : X) :
    ofGenericCoefficients hfin c x =
      if hx : x ∈ genericPoints X then c ⟨x, hx⟩ else 0 := by
  letI := hfin.fintype
  rw [ofGenericCoefficients_eq_sum]
  simp only [coe_sum, Finset.sum_apply]
  by_cases hx : x ∈ genericPoints X
  · rw [dif_pos hx, Finset.sum_eq_single (⟨x, hx⟩ : genericPoints X)]
    · simp
    · intro y hy hne
      have hxy : x ≠ y.val := fun h => hne (Subtype.ext h.symm)
      simp [single_apply, hxy]
    · simp
  · rw [dif_neg hx]
    apply Finset.sum_eq_zero
    intro y hy
    have hxy : x ≠ y.val := fun h => hx (h.symm ▸ y.property)
    simp [single_apply, hxy]

/-- Evaluation at an actual generic point recovers its input coefficient. -/
@[simp]
theorem ofGenericCoefficients_apply_generic (c : genericPoints X → R)
    (x : genericPoints X) : ofGenericCoefficients hfin c x.val = c x := by
  classical
  simp [ofGenericCoefficients_apply, x.property]

/-- No coefficient is introduced outside the actual generic points. -/
theorem ofGenericCoefficients_apply_of_notMem (c : genericPoints X → R)
    (x : X) (hx : x ∉ genericPoints X) : ofGenericCoefficients hfin c x = 0 := by
  classical
  simp [ofGenericCoefficients_apply, hx]

/-- A coefficient supported at one actual generic point is the native prime cycle
with that coefficient. -/
@[simp]
theorem ofGenericCoefficients_single (x : genericPoints X) (r : R) :
    ofGenericCoefficients hfin (Pi.single x r) = single x.val r := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro y
  by_cases hy : y ∈ genericPoints X
  · simp [ofGenericCoefficients_apply, hy, Pi.single_apply, single_apply, Subtype.ext_iff]
  · have hyx : y ≠ x.val := fun h => hy (h.symm ▸ x.property)
    simp [ofGenericCoefficients_apply, hy, single_apply, hyx]

/-- A cycle assembled from generic coefficients is supported on those generic points. -/
theorem support_ofGenericCoefficients_subset (c : genericPoints X → R) :
    (ofGenericCoefficients hfin c).support ⊆ genericPoints X := by
  classical
  intro x hx
  by_contra h
  exact hx (ofGenericCoefficients_apply_of_notMem hfin c x h)

/-- The actual support records exactly the generic points with nonzero coefficients. -/
theorem support_ofGenericCoefficients (c : genericPoints X → R) :
    (ofGenericCoefficients hfin c).support =
      Subtype.val '' Function.support c := by
  ext x
  constructor
  · intro hx
    have hgeneric := support_ofGenericCoefficients_subset hfin c hx
    refine ⟨⟨x, hgeneric⟩, ?_, rfl⟩
    change c ⟨x, hgeneric⟩ ≠ 0
    rw [← ofGenericCoefficients_apply_generic hfin c ⟨x, hgeneric⟩]
    exact hx
  · rintro ⟨y, hy, rfl⟩
    change ofGenericCoefficients hfin c y.val ≠ 0
    change c y ≠ 0 at hy
    simpa only [ofGenericCoefficients_apply_generic] using hy

/-- Finite generic indexing gives finite cycle support even when `X` is not compact. -/
theorem finite_support_ofGenericCoefficients (c : genericPoints X → R) :
    (ofGenericCoefficients hfin c).support.Finite :=
  hfin.subset (support_ofGenericCoefficients_subset hfin c)

/-- Generic coefficients uniquely determine a cycle supported on the generic points. -/
theorem ofGenericCoefficients_eq_self (D : AlgebraicCycle X R)
    (hD : D.support ⊆ genericPoints X) :
    ofGenericCoefficients hfin (fun x => D x.val) = D := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro x
  by_cases hx : x ∈ genericPoints X
  · exact ofGenericCoefficients_apply_generic hfin (fun y => D y.val) ⟨x, hx⟩
  · rw [ofGenericCoefficients_apply_of_notMem hfin _ x hx]
    by_contra hzero
    exact hx (hD (Ne.symm hzero))

/-- Distinct generic coefficient functions give distinct native cycles. -/
theorem ofGenericCoefficients_injective :
    Function.Injective (ofGenericCoefficients hfin :
      (genericPoints X → R) → AlgebraicCycle X R) := by
  intro c d h
  funext x
  have he := congrArg (fun D : AlgebraicCycle X R => D x.val) h
  simpa only [ofGenericCoefficients_apply_generic] using he

/-- Equality may be checked at the actual generic coefficient functions. -/
@[simp]
theorem ofGenericCoefficients_eq_iff (c d : genericPoints X → R) :
    ofGenericCoefficients hfin c = ofGenericCoefficients hfin d ↔ c = d :=
  (ofGenericCoefficients_injective hfin).eq_iff

/-- The zero coefficient function produces the zero native cycle. -/
@[simp]
theorem ofGenericCoefficients_zero : ofGenericCoefficients hfin (0 : genericPoints X → R) = 0 :=
  map_zero _

/-- Addition of generic coefficients is addition in the native cycle group. -/
@[simp]
theorem ofGenericCoefficients_add (c d : genericPoints X → R) :
    ofGenericCoefficients hfin (c + d) =
      ofGenericCoefficients hfin c + ofGenericCoefficients hfin d :=
  map_add _ _ _

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup R] (hfin : (genericPoints X).Finite)

/-- Negating the coefficients negates the native cycle; signed Tor coefficients
therefore remain signed at this lower assembly step. -/
@[simp]
theorem ofGenericCoefficients_neg (c : genericPoints X → R) :
    ofGenericCoefficients hfin (-c) = -ofGenericCoefficients hfin c :=
  map_neg _ _

/-- Subtraction of generic coefficients is native cycle subtraction. -/
@[simp]
theorem ofGenericCoefficients_sub (c d : genericPoints X → R) :
    ofGenericCoefficients hfin (c - d) =
      ofGenericCoefficients hfin c - ofGenericCoefficients hfin d :=
  map_sub _ _ _

/-- Integer multiplicities are retained by the assembly. -/
@[simp]
theorem ofGenericCoefficients_zsmul (n : ℤ) (c : genericPoints X → R) :
    ofGenericCoefficients hfin (n • c) = n • ofGenericCoefficients hfin c :=
  map_zsmul _ _ _

end AddCommGroup

end AlgebraicGeometry.AlgebraicCycle
