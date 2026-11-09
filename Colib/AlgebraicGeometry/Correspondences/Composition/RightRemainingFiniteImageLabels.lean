/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteGenericLabels

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

/-- The actual image-stalk prime of a retained original exterior generic label. -/
def correspondenceRightRemainingOriginalImagePrime
    (x : correspondenceRightImageIncidence f g h i z w v) (η :
      (correspondenceRightRemainingOriginalGenericLabels f g h i z w v x)) :
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    PrimeSpectrum R := by
  dsimp only
  exact correspondenceRightRemainingFiniteModelStructure f g h i z w v x
    ((correspondenceRightRemainingFiniteGenericEquivOriginal f g h i z w v x).symm η).1

/-- The image prime represents exactly the original exterior image under native fromSpecStalk. -/
theorem correspondenceRightRemainingOriginalImagePrime_fromSpecStalk
    (x : correspondenceRightImageIncidence f g h i z w v) (η :
      (correspondenceRightRemainingOriginalGenericLabels f g h i z w v x)) :
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    (T).fromSpecStalk x₀ (correspondenceRightRemainingOriginalImagePrime f g h i z w v x η) =
      q' η.1.1 := by
  dsimp only
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let q' := correspondenceRightIntermediateImageMap f g h i z w v
  let e := correspondenceRightRemainingFiniteGenericEquivOriginal f g h i z w v x
  let a := e.symm η
  have hlabel : correspondenceRightRemainingFiniteGenericLabel f g h i z w v x a = η.1 :=
    congrArg Subtype.val (e.apply_symm_apply η)
  have hpoint : correspondenceRightRemainingFiniteModelProjection f g h i z w v x a.1 = η.1.1 :=
    congrArg Subtype.val hlabel
  have H := congrArg
    (fun m : correspondenceRightRemainingFiniteModel f g h i z w v x ⟶ T => m a.1)
    (pullback.condition (f := q') (g := (T).fromSpecStalk x₀))
  change (T).fromSpecStalk x₀
    (pullback.snd q' ((T).fromSpecStalk x₀) a.1) = q' η.1.1
  change pullback.fst q' ((T).fromSpecStalk x₀) a.1 = η.1.1 at hpoint
  simpa only [Scheme.Hom.comp_apply, hpoint] using H.symm

/-- The fibre of the literal image-prime map is all original exterior generic labels over that
actual image point. Colliding finite images remain distinct labels. -/
def correspondenceRightRemainingOriginalImagePrimeFiberEquiv
    (x : correspondenceRightImageIncidence f g h i z w v) (p : PrimeSpectrum
      (correspondenceRightRemainingImageStalk f g h i z w v x)) :
    let E := correspondenceRightIntermediateSupportProduct f g h i z w v
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let L := correspondenceRightRemainingOriginalGenericLabels f g h i z w v x
    {η : L // correspondenceRightRemainingOriginalImagePrime f g h i z w v x η = p} ≃
      {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p} := by
  dsimp only
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let q' := correspondenceRightIntermediateImageMap f g h i z w v
  let L := correspondenceRightRemainingOriginalGenericLabels f g h i z w v x
  exact
    { toFun := fun η => ⟨η.1.1,
        (correspondenceRightRemainingOriginalImagePrime_fromSpecStalk
          f g h i z w v x η.1).symm.trans
            (congrArg ((T).fromSpecStalk x₀) η.2)⟩
      invFun := fun η => by
        have hspec : q' η.1.1 ⤳ x₀ := by
          rw [η.2]
          have hmem : (T).fromSpecStalk x₀ p ∈ Set.range ((T).fromSpecStalk x₀) := ⟨p, rfl⟩
          rwa [Scheme.range_fromSpecStalk] at hmem
        let a : L := ⟨η.1, hspec⟩
        exact ⟨a, ((T).fromSpecStalk x₀).isEmbedding.injective
          ((correspondenceRightRemainingOriginalImagePrime_fromSpecStalk
            f g h i z w v x a).trans η.2)⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }

/-- Actual finite-model geometry makes the whole retained generic-label set finite. -/
theorem finite_correspondenceRightRemainingOriginalGenericLabels
    (x : correspondenceRightImageIncidence f g h i z w v) [IsSeparated i]
    [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v) :
    let L := correspondenceRightRemainingOriginalGenericLabels f g h i z w v x
    Finite L := by
  dsimp only
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let B := correspondenceRightRemainingFiniteRing f g h i z w v x
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let := moduleFinite_correspondenceRightRemainingFiniteRing f g h i z w v hw hv x
  let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  let : Finite {p : PrimeSpectrum B // IsMin p} :=
    (PrimeSpectrum.finite_setOfPred_isMin B).to_subtype
  exact Finite.of_equiv _
    ((correspondenceRightRemainingFiniteGenericEquivMinPrime f g h i z w v hw hv x).symm.trans
      (correspondenceRightRemainingFiniteGenericEquivOriginal f g h i z w v x))

end Stacks.Chow
