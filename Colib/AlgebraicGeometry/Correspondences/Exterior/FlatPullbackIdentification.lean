/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.PrimePullbackSupport
public import Colib.AlgebraicGeometry.Correspondences.Exterior.IncidencePushPull

/-!
# Native exterior cycles are diagonal pushforwards of actual flat pullbacks

Let `B = X × Y`, let `π : B × T → B` be the projection, and let `j` be the
existing common-parameter closed immersion into `(X × T) × (Y × T)`. For an
admissible point `z`, put `d = δ_B(z)` and `r = dim T`. The actual native
`flatPullback` sends the prime `[z]` in grade `d` to the unique generic point
of its integral inverse image, with weight one. The actual finite pushforward
along `j` sends that point, with degree one, to `nativeExteriorPoint z`.
Thus `j_* π^* [z]` equals the existing `nativeExteriorPrime z`.

For signed finite correspondences the extension is the actual finite sum of
these graded pullbacks with the original integer coefficients. Each summand
uses its own grade; there is no equidimensionality hypothesis on `X` or `Y`.
This identifies the existing operation, without replacing it or assuming its
value on primes. Exterior Tor-cycle transport and composition remain separate.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]

local notation3 (prettyPrint := false) "C" => fieldChowSituation k
local notation3 (prettyPrint := false) "B" => (pullback X.hom Y.hom : Scheme)
local notation3 (prettyPrint := false) "BT" => exteriorOuterProduct X Y T
local notation3 (prettyPrint := false) "π" =>
  (pullback.fst (pullback.fst X.hom Y.hom ≫ X.hom) T.hom)
local notation3 (prettyPrint := false) "sB" => (pullback.fst X.hom Y.hom ≫ X.hom)
local notation3 (prettyPrint := false) "sBT" => (π ≫ sB)
local notation3 (prettyPrint := false) "r" => exteriorParameterDimension T

local instance : IsLocallyNoetherian B :=
  LocallyOfFiniteType.isLocallyNoetherian (show B ⟶ Spec (.of k) from sB)

/-- The actual native weight, at the original point's own shifted grade. -/
theorem nativeExterior_flatPullbackWeight (z : B) :
    flatPullbackWeight C sBT π
      (relativeDimension (C).dimensionFunction sB z + (r : ℤ))
      (geometricallyIntegralPullbackPoint π z) = 1 :=
  flatPullbackWeight_geometricallyIntegralPullbackPoint C sBT sB π rfl r
    (relativeDimension_exteriorOuterProjection X Y T) z

/-- Prime comparison with the already defined native exterior operation. -/
@[stacks 02RB "actual prime pullback along the geometrically integral parameter projection",
  stacks 02R4 "actual closed-immersion pushforward with residue degree one"]
theorem nativeExteriorPrime_eq_diagonal_flatPullback
    (z : B) (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    (nativeExteriorPrime X Y T z hz).val =
      finiteCyclePushforward (exteriorOuterDiagonal X Y T)
        (flatPullback C sBT sB π rfl r
          (relativeDimension_exteriorOuterProjection X Y T)
          (relativeDimension (C).dimensionFunction sB z)
          (pointCycleAtOwnDimension C sB z 1)).val := by
  rw [flatPullback_pointCycleAtOwnDimension,
    finiteCyclePushforward_single_of_isClosedImmersion,
    exteriorOuterDiagonal_pullbackPoint X Y T z hz,
    nativeExteriorPrime_eq_single]
  rfl

/-- A signed finite sum of the actual native point pullbacks, each in its own grade.
This packages existing operations on native cycles; it is not a new cycle model. -/
def nativeExteriorParameterPullback :
    finiteCorrespondences X.hom Y.hom →+ AlgebraicCycle BT ℤ :=
  liftFiniteCorrespondence X.hom Y.hom fun z _ =>
    (flatPullback C sBT sB π rfl r
      (relativeDimension_exteriorOuterProjection X Y T)
      (relativeDimension (C).dimensionFunction sB z)
      (pointCycleAtOwnDimension C sB z 1)).val

/-- The signed extension is the literal finite integer sum, with no positivity premise. -/
theorem nativeExteriorParameterPullback_apply (α : finiteCorrespondences X.hom Y.hom) :
    nativeExteriorParameterPullback X Y T α =
      ∑ᶠ z : B, if IsFiniteCorrespondencePoint X.hom Y.hom z then
        α.val z •
          (flatPullback C sBT sB π rfl r
            (relativeDimension_exteriorOuterProjection X Y T)
            (relativeDimension (C).dimensionFunction sB z)
            (pointCycleAtOwnDimension C sB z 1)).val else 0 := by
  classical
  rfl

/-- On every signed prime, the parameter sum is the actual signed native pullback. -/
theorem nativeExteriorParameterPullback_single (z : B)
    (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) (n : ℤ) :
    nativeExteriorParameterPullback X Y T
      (singleFiniteCorrespondence X.hom Y.hom z hz n) =
        (flatPullback C sBT sB π rfl r
          (relativeDimension_exteriorOuterProjection X Y T)
          (relativeDimension (C).dimensionFunction sB z)
          (pointCycleAtOwnDimension C sB z n)).val := by
  rw [nativeExteriorParameterPullback, liftFiniteCorrespondence_single,
    flatPullback_pointCycleAtOwnDimension, flatPullback_pointCycleAtOwnDimension]
  apply Function.locallyFinsuppWithin.ext
  intro p
  classical
  by_cases hp : p = geometricallyIntegralPullbackPoint π z <;>
    simp [single_apply, hp]

/-- The existing signed exterior operation is precisely diagonal pushforward of the
finite sum of actual native flat pullbacks. Every original integer coefficient survives. -/
theorem nativeExterior_eq_diagonal_parameterPullback
    (α : finiteCorrespondences X.hom Y.hom) :
    (nativeExterior X Y T α).val =
      finiteCyclePushforward (exteriorOuterDiagonal X Y T)
        (nativeExteriorParameterPullback X Y T α) := by
  classical
  let φ : ∀ z : B, IsFiniteCorrespondencePoint X.hom Y.hom z → AlgebraicCycle BT ℤ :=
    fun z _ =>
      (flatPullback C sBT sB π rfl r
        (relativeDimension_exteriorOuterProjection X Y T)
        (relativeDimension (C).dimensionFunction sB z)
        (pointCycleAtOwnDimension C sB z 1)).val
  let forget := (finiteCorrespondences (SmoothSite.product X T).hom
    (SmoothSite.product Y T).hom).subtype
  change forget (∑ᶠ z, finiteCorrespondenceContribution X.hom Y.hom
      (nativeExteriorPrime X Y T) α z) =
    finiteCyclePushforward (exteriorOuterDiagonal X Y T)
      (∑ᶠ z, finiteCorrespondenceContribution X.hom Y.hom φ α z)
  rw [forget.map_finsum
    (finite_support_finiteCorrespondenceContribution X.hom Y.hom
      (nativeExteriorPrime X Y T) α),
    (finiteCyclePushforward (exteriorOuterDiagonal X Y T)).map_finsum
      (finite_support_finiteCorrespondenceContribution X.hom Y.hom φ α)]
  apply finsum_congr
  intro z
  by_cases hz : IsFiniteCorrespondencePoint X.hom Y.hom z
  · simp only [finiteCorrespondenceContribution, dite_eq_left hz, map_zsmul]
    exact congrArg (fun β : AlgebraicCycle
      (pullback (SmoothSite.product X T).hom (SmoothSite.product Y T).hom) ℤ => α.val z • β)
      (nativeExteriorPrime_eq_diagonal_flatPullback X Y T z hz)
  · simp only [finiteCorrespondenceContribution, dite_eq_right hz, map_zero]

/-- The final signed-cycle interface, displaying the actual finite sum and every grade. -/
theorem nativeExterior_eq_diagonal_flatPullback_finsum
    (α : finiteCorrespondences X.hom Y.hom) :
    (nativeExterior X Y T α).val =
      finiteCyclePushforward (exteriorOuterDiagonal X Y T)
        (∑ᶠ z : B, if IsFiniteCorrespondencePoint X.hom Y.hom z then
          α.val z •
            (flatPullback C sBT sB π rfl r
              (relativeDimension_exteriorOuterProjection X Y T)
              (relativeDimension (C).dimensionFunction sB z)
              (pointCycleAtOwnDimension C sB z 1)).val else 0) := by
  rw [nativeExterior_eq_diagonal_parameterPullback, nativeExteriorParameterPullback_apply]

/-- Coefficientwise the signed sum uses the actual native weight at the grade of
its original label. The sum is finite by the original correspondence support. -/
theorem nativeExteriorParameterPullback_coeff
    (α : finiteCorrespondences X.hom Y.hom) (p : BT) :
    nativeExteriorParameterPullback X Y T α p =
      α.val (π p) * flatPullbackWeight C sBT π
        (relativeDimension (C).dimensionFunction sB (π p) + (r : ℤ)) p := by
  classical
  let φ : ∀ z : B, IsFiniteCorrespondencePoint X.hom Y.hom z → AlgebraicCycle BT ℤ :=
    fun z _ =>
      (flatPullback C sBT sB π rfl r
        (relativeDimension_exteriorOuterProjection X Y T)
        (relativeDimension (C).dimensionFunction sB z)
        (pointCycleAtOwnDimension C sB z 1)).val
  let ev : AlgebraicCycle BT ℤ →+ ℤ :=
    { toFun := fun β => β p
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ᶠ z, finiteCorrespondenceContribution X.hom Y.hom φ α z) = _
  rw [ev.map_finsum
    (finite_support_finiteCorrespondenceContribution X.hom Y.hom φ α)]
  rw [finsum_eq_single _ (π p)]
  · by_cases ha : IsFiniteCorrespondencePoint X.hom Y.hom (π p)
    · simp [finiteCorrespondenceContribution, ha, ev, φ, flatPullback_apply,
        pointCycleAtOwnDimension]
    · have hzero : α.val (π p) = 0 := by
        by_contra hzero
        exact ha (α.property.2 _ hzero)
      simp [finiteCorrespondenceContribution, ha, ev, hzero]
  · intro z hz
    by_cases ha : IsFiniteCorrespondencePoint X.hom Y.hom z
    · simp [finiteCorrespondenceContribution, ha, ev, φ, flatPullback_apply,
        pointCycleAtOwnDimension, single_apply, Ne.symm hz]
    · simp [finiteCorrespondenceContribution, ha, ev]

/-- When a particular input cycle already has a native grade, the signed sum
agrees with one application of the existing graded flat-pullback homomorphism. -/
theorem nativeExteriorParameterPullback_eq_flatPullback
    (n : ℤ) (α : finiteCorrespondences X.hom Y.hom)
    (hα : α.val ∈ cyclesOfDimension C sB n) :
    nativeExteriorParameterPullback X Y T α =
      (flatPullback C sBT sB π rfl r
        (relativeDimension_exteriorOuterProjection X Y T) n ⟨α.val, hα⟩).val := by
  apply Function.locallyFinsuppWithin.ext
  intro p
  rw [nativeExteriorParameterPullback_coeff, flatPullback_apply]
  by_cases hp : α.val (π p) = 0
  · simp [hp]
  · rw [(mem_cyclesOfDimension_iff_forall_point C sB n α.val).mp hα (π p) hp]

/-- The graded target interface needed by native 02RG. The grade belongs to the
input cycle, not to every component of the ambient smooth schemes. -/
theorem nativeExterior_eq_diagonal_flatPullback
    (n : ℤ) (α : finiteCorrespondences X.hom Y.hom)
    (hα : α.val ∈ cyclesOfDimension C sB n) :
    (nativeExterior X Y T α).val =
      finiteCyclePushforward (exteriorOuterDiagonal X Y T)
        (flatPullback C sBT sB π rfl r
          (relativeDimension_exteriorOuterProjection X Y T) n ⟨α.val, hα⟩).val := by
  rw [nativeExterior_eq_diagonal_parameterPullback,
    nativeExteriorParameterPullback_eq_flatPullback X Y T n α hα]

end Stacks.Chow
