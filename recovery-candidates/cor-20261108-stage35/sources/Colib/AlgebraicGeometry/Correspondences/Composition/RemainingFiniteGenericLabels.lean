/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteModel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalizationBaseChange

/-!
# Original generic labels of the whole remaining finite model

The generic points of the full finite model are in bijection with precisely the
original exterior generic points whose images specialize to the actual local
image point. The map is the actual projection; surjectivity is proved from
Stacks 01J7 and the underlying-point surjectivity of scheme pullbacks.
No labels with coincident images are identified.

The affine model's minimal primes are compared with these actual scheme labels
using the native affine-open generic-point equivalence. The resulting prime is
the comap of the maximal ideal along the actual global-section germ map.
There is no reducedness, irreducibility, dominance, or perfect-field assumption.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The original exterior labels that survive localization at the actual image point. -/
abbrev correspondenceRemainingOriginalGenericLabels
    (x : correspondenceLeftImageIncidence f g h i z w v) :=
  {q : genericPoints (correspondenceLeftIntermediateSupportProduct f g h i z w v) //
    correspondenceLeftIntermediateImageMap f g h i z w v q.1 ⤳
      correspondenceLeftImageIncidenceInclusion f g h i z w v x}

/-- The actual localization projection sends a model point to a label over a generization
of the actual image point. -/
theorem correspondenceRemainingFiniteModel_image_specializes
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    correspondenceLeftIntermediateImageMap f g h i z w v
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q) ⤳
      correspondenceLeftImageIncidenceInclusion f g h i z w v x := by
  let T := correspondenceLeftIntermediateImageProduct f g h i z w v
  let y := correspondenceLeftImageIncidenceInclusion f g h i z w v x
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  have hspec : T.fromSpecStalk y (π q) ⤳ y := by
    have hmem : T.fromSpecStalk y (π q) ∈ Set.range (T.fromSpecStalk y) := ⟨π q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at hmem
  have hcomm : correspondenceLeftIntermediateImageMap f g h i z w v
      (correspondenceRemainingFiniteModelProjection f g h i z w v x q) =
      T.fromSpecStalk y (π q) := by
    simpa only [Scheme.Hom.comp_apply] using
      congrArg (fun k : correspondenceRemainingFiniteModel f g h i z w v x ⟶ T => k q)
        (pullback.condition (f := correspondenceLeftIntermediateImageMap f g h i z w v)
          (g := T.fromSpecStalk y))
  rw [hcomm]
  exact hspec

/-- The actual projection is a bijection on all retained original generic labels. -/
def correspondenceRemainingFiniteGenericEquivOriginal
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    genericPoints (correspondenceRemainingFiniteModel f g h i z w v x) ≃
      correspondenceRemainingOriginalGenericLabels f g h i z w v x := by
  let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
  let := flat_correspondenceRemainingFiniteModelProjection f g h i z w v x
  let k : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x) →
      correspondenceRemainingOriginalGenericLabels f g h i z w v x :=
    fun q => ⟨correspondenceRemainingFiniteGenericLabel f g h i z w v x q,
      correspondenceRemainingFiniteModel_image_specializes f g h i z w v x q.1⟩
  apply Equiv.ofBijective k
  constructor
  · intro q q' heq
    apply Subtype.ext
    apply ρ.isEmbedding.injective
    exact congrArg (fun r => r.1.1) heq
  · intro η
    let T := correspondenceLeftIntermediateImageProduct f g h i z w v
    let y := correspondenceLeftImageIncidenceInclusion f g h i z w v x
    have hmem : correspondenceLeftIntermediateImageMap f g h i z w v η.1.1 ∈
        Set.range (T.fromSpecStalk y) := by
      rw [Scheme.range_fromSpecStalk]
      exact η.2
    obtain ⟨a, ha⟩ := hmem
    obtain ⟨q, hq, _⟩ := Scheme.Pullback.exists_preimage_pullback η.1.1 a ha.symm
    have hgen : q ∈ genericPoints (correspondenceRemainingFiniteModel f g h i z w v x) :=
      mem_genericPoints_of_flat_preimmersion ρ (hq.symm ▸ η.1.2)
    refine ⟨⟨q, hgen⟩, ?_⟩
    apply Subtype.ext
    exact Subtype.ext hq

/-- The generic-label bijection is the actual projection on underlying points. -/
theorem correspondenceRemainingFiniteGenericEquivOriginal_val
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x)) :
    (correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x q).1.1 =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q.1 := rfl

/-- The native affine generic-point equivalence, read in the minimal `PrimeSpectrum` type
used by the integer Euler formula. -/
def correspondenceRemainingFiniteGenericEquivMinPrime [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    genericPoints (correspondenceRemainingFiniteModel f g h i z w v x) ≃
      {q : PrimeSpectrum (correspondenceRemainingFiniteRing f g h i z w v x) // IsMin q} := by
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  let T := correspondenceRemainingFiniteModel f g h i z w v x
  let etop : genericPoints T ≃ {q : genericPoints T // q.1 ∈ (⊤ : T.Opens)} :=
    { toFun := fun q => ⟨q, trivial⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let emin : minimalPrimes (correspondenceRemainingFiniteRing f g h i z w v x) ≃
      {q : PrimeSpectrum (correspondenceRemainingFiniteRing f g h i z w v x) // IsMin q} :=
    { toFun := fun q => ⟨⟨q.1, q.2.1.1⟩, PrimeSpectrum.isMin_iff.mpr q.2⟩
      invFun := fun q => ⟨q.1.asIdeal, PrimeSpectrum.isMin_iff.mp q.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact etop.trans ((genericPointsInOpenEquivMinimalPrimes (isAffineOpen_top T)).trans emin)

/-- The selected minimal prime is the actual section-germ prime, not a chosen isomorphic label. -/
theorem correspondenceRemainingFiniteGenericEquivMinPrime_asIdeal [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x)) :
    (correspondenceRemainingFiniteGenericEquivMinPrime f g h i z w v hz hw x q).1.asIdeal =
      (IsLocalRing.maximalIdeal
        ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.stalk q.1)).comap
          ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ
            ⊤ q.1 trivial).hom := by
  let := isAffine_correspondenceRemainingFiniteModel f g h i z w v hz hw x
  let T := correspondenceRemainingFiniteModel f g h i z w v x
  change ((genericPointsInOpenEquivMinimalPrimes (isAffineOpen_top T) ⟨q, trivial⟩ :
    minimalPrimes (correspondenceRemainingFiniteRing f g h i z w v x)) :
      Ideal (correspondenceRemainingFiniteRing f g h i z w v x)) = _
  rw [genericPointsInOpenEquivMinimalPrimes_asIdeal,
    IsAffineOpen.primeIdealOf_eq_map_closedPoint]
  rfl

/-- Every minimal source prime is exactly one retained original exterior generic label. -/
def correspondenceRemainingFiniteMinPrimeEquivOriginal [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (x : correspondenceLeftImageIncidence f g h i z w v) :
    {q : PrimeSpectrum (correspondenceRemainingFiniteRing f g h i z w v x) // IsMin q} ≃
      correspondenceRemainingOriginalGenericLabels f g h i z w v x :=
  (correspondenceRemainingFiniteGenericEquivMinPrime f g h i z w v hz hw x).symm.trans
    (correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x)

end Stacks.Chow
