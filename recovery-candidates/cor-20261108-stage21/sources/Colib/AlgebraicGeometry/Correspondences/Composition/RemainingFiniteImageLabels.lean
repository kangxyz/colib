/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteGenericLabels

/-!
# Literal image-stalk primes group the retained original exterior labels

The original label's image prime is the actual structure-map point of its unique
whole finite-model lift. Its image under native `fromSpecStalk` is proved to be
the original exterior image. This gives the exact fibre-label bijection required
to regroup the concrete finite Tor family into the same image-prime fibres as
the fixed-original-label Euler theorem. No chosen prime contraction, guessed
label map, or injectivity of the finite exterior map is used.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  (x : correspondenceLeftImageIncidence f g h i z w v)

local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "B" => correspondenceRemainingFiniteRing f g h i z w v x
local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "q'" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "L" =>
  correspondenceRemainingOriginalGenericLabels f g h i z w v x

/-- The actual image-stalk prime of a retained original exterior generic label. -/
def correspondenceRemainingOriginalImagePrime (η : L) : PrimeSpectrum R :=
  correspondenceRemainingFiniteModelStructure f g h i z w v x
    ((correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x).symm η).1

/-- The image prime represents exactly the original exterior image under native fromSpecStalk. -/
theorem correspondenceRemainingOriginalImagePrime_fromSpecStalk (η : L) :
    (T).fromSpecStalk x₀ (correspondenceRemainingOriginalImagePrime f g h i z w v x η) =
      q' η.1.1 := by
  let e := correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x
  let a := e.symm η
  have hlabel : correspondenceRemainingFiniteGenericLabel f g h i z w v x a = η.1 :=
    congrArg Subtype.val (e.apply_symm_apply η)
  have hpoint : correspondenceRemainingFiniteModelProjection f g h i z w v x a.1 = η.1.1 :=
    congrArg Subtype.val hlabel
  have H := congrArg
    (fun m : correspondenceRemainingFiniteModel f g h i z w v x ⟶ T => m a.1)
    (pullback.condition (f := q') (g := (T).fromSpecStalk x₀))
  simpa only [Scheme.Hom.comp_apply, hpoint] using H.symm

/-- The fibre of the literal image-prime map is all original exterior generic labels over that
actual image point. Colliding finite images remain distinct labels. -/
def correspondenceRemainingOriginalImagePrimeFiberEquiv (p : PrimeSpectrum R) :
    {η : L // correspondenceRemainingOriginalImagePrime f g h i z w v x η = p} ≃
      {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p} where
  toFun η := ⟨η.1.1,
    (correspondenceRemainingOriginalImagePrime_fromSpecStalk f g h i z w v x η.1).symm.trans
      (congrArg ((T).fromSpecStalk x₀) η.2)⟩
  invFun η := by
    have hspec : q' η.1.1 ⤳ x₀ := by
      rw [η.2]
      have hmem : (T).fromSpecStalk x₀ p ∈ Set.range ((T).fromSpecStalk x₀) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at hmem
    let a : L := ⟨η.1, hspec⟩
    exact ⟨a, ((T).fromSpecStalk x₀).isEmbedding.injective
      ((correspondenceRemainingOriginalImagePrime_fromSpecStalk f g h i z w v x a).trans η.2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Actual finite-model geometry makes the whole retained generic-label set finite. -/
theorem finite_correspondenceRemainingOriginalGenericLabels [IsSeparated h]
    [IsLocallyNoetherian T]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w) :
    Finite L := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let := moduleFinite_correspondenceRemainingFiniteRing f g h i z w v hz hw x
  let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  let : Finite {p : PrimeSpectrum B // IsMin p} :=
    (PrimeSpectrum.finite_setOfPred_isMin B).to_subtype
  exact Finite.of_equiv _
    ((correspondenceRemainingFiniteGenericEquivMinPrime f g h i z w v hz hw x).symm.trans
      (correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x))

end Stacks.Chow
