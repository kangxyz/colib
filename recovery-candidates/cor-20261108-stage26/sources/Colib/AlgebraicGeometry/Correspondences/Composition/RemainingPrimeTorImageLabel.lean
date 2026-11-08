/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingPrimeTorComparison
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteGenericLabels
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteResidueTransport

/-!
# The remaining Tor prime closure has the original image label

The prime of the full finite algebra is the native germ prime at the original model generic
point. The proved ΓSpecIso scalar triangle identifies its literal contraction with the actual
structure point in the spectrum of the image-exterior stalk. The original pullback square
therefore identifies its prime closure with the integral closure of the original exterior
label's image. Neither the label nor the finite-map residue degree is replaced or merged.

This is a consumer of the canonical finite model, its generic-label equivalences, and the
residue-transport packet. It does not reconstruct their proofs. Nonminimal and vertical image
closures remain allowed; no admissibility or finite-correspondence assertion is made here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i) [IsSeparated h]
  (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
  (x : correspondenceLeftImageIncidence f g h i z w v)

local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "e" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "B" => correspondenceRemainingFiniteRing f g h i z w v x
local notation3 (prettyPrint := false) "E" =>
  correspondenceRemainingFiniteGenericEquivMinPrime f g h i z w v hz hw x

/-- The literal contracted prime is the original model structure point, not an unlabeled prime. -/
theorem correspondenceRemainingImagePrime_eq_modelStructure
    (q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x)) :
    correspondenceRemainingImagePrime f g h i z w v x (E q).1 =
      correspondenceRemainingFiniteModelStructure f g h i z w v x q.1 := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  apply PrimeSpectrum.ext
  rw [correspondenceRemainingImagePrime_asIdeal,
    correspondenceRemainingFiniteGenericEquivMinPrime_asIdeal]
  exact correspondenceRemainingFiniteGermPrime_comap_algebraMap f g h i z w v x q.1

/-- The image-exterior point of the contracted prime is the actual original label's image. -/
theorem correspondenceRemainingImagePrime_fromSpecStalk
    (q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x)) :
    (T).fromSpecStalk e (correspondenceRemainingImagePrime f g h i z w v x (E q).1) =
      correspondenceLeftIntermediateImageMap f g h i z w v
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q.1) := by
  rw [correspondenceRemainingImagePrime_eq_modelStructure f g h i z w v hz hw x q]
  simpa only [Scheme.Hom.comp_apply] using
    (congrArg (fun k : correspondenceRemainingFiniteModel f g h i z w v x ⟶ T => k q.1)
      (pullback.condition (f := correspondenceLeftIntermediateImageMap f g h i z w v)
        (g := (T).fromSpecStalk e))).symm

/-- The prime closure used in remaining Tor is the integral closure of the actual image label. -/
theorem correspondenceRemainingImagePrimeClosure_eq_actualImage
    (q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x)) :
    correspondenceRemainingImagePrimeClosure f g h i z w v x (E q).1 =
      integralComponentAt (correspondenceLeftIntermediateImageMap f g h i z w v
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q.1)) := by
  unfold correspondenceRemainingImagePrimeClosure
  rw [correspondenceRemainingImagePrime_fromSpecStalk f g h i z w v hz hw x q]

/-- The actual image-label closure has exactly the original contracted germ-prime ideal stalk. -/
theorem correspondenceRemainingActualImageClosure_stalk
    (q : genericPoints (correspondenceRemainingFiniteModel f g h i z w v x)) :
    letI := correspondenceRemainingFiniteAlgebra f g h i z w v x
    IdealSheafData.stalk
      (integralComponentAt (correspondenceLeftIntermediateImageMap f g h i z w v
        (correspondenceRemainingFiniteModelProjection f g h i z w v x q.1))) e =
      (E q).1.asIdeal.comap (algebraMap R B) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  rw [← correspondenceRemainingImagePrimeClosure_eq_actualImage f g h i z w v hz hw x q,
    correspondenceRemainingImagePrimeClosure_stalk, correspondenceRemainingImagePrime_asIdeal]

/-- Retained original exterior labels, including coincident images, give the literal closure. -/
theorem correspondenceRemainingImagePrimeClosure_eq_originalLabel
    (η : correspondenceRemainingOriginalGenericLabels f g h i z w v x) :
    correspondenceRemainingImagePrimeClosure f g h i z w v x
      (E ((correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x).symm η)).1 =
        integralComponentAt (correspondenceLeftIntermediateImageMap f g h i z w v η.1.1) := by
  let q := (correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x).symm η
  have hη : correspondenceRemainingFiniteModelProjection f g h i z w v x q.1 = η.1.1 := by
    rw [← correspondenceRemainingFiniteGenericEquivOriginal_val f g h i z w v x q]
    exact congrArg (fun a => a.1.1)
      ((correspondenceRemainingFiniteGenericEquivOriginal f g h i z w v x).apply_symm_apply η)
  rw [correspondenceRemainingImagePrimeClosure_eq_actualImage f g h i z w v hz hw x q, hη]

end Stacks.Chow
