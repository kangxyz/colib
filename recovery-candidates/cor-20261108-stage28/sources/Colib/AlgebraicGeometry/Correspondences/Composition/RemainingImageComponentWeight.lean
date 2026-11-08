/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageComponentEuler
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorGrade
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.ClosedImmersionBaseChange

/-!
# The actual image-component Euler coefficients are the native 02RG weights

The canonical generic component over a supporting minimal image-stalk prime maps
back to the original image point. Native flatness of `comapRestrict` proves this
point identity; it is not an extra grouping hypothesis. Native 02R8 then computes
its actual dimension grade. The full localized quotient length therefore equals
the image-side `flatPullbackWeight` in native 02RG, including inseparable and
nonreduced exterior multiplicities. The resulting integer remaining Euler identity
uses those literal native weights and the same original remaining diagonal list.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

attribute [local instance] isIntegral_integralComponentAt

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "C" => fieldChowSituation K
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "π'" =>
  correspondenceLeftImageExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "q" => (correspondenceIncidenceMap f g h z w).toImage
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)
local notation3 (prettyPrint := false) "sT" => π' ≫ sJ

variable (x : correspondenceLeftImageIncidence f g h i z w v)
  (t : correspondenceIncidence f g h z w)

local notation3 (prettyPrint := false) "x₀" =>
  correspondenceLeftImageIncidenceInclusion f g h i z w v x
local notation3 (prettyPrint := false) "R" => correspondenceRemainingImageStalk f g h i z w v x
local notation3 (prettyPrint := false) "D" => correspondenceRemainingImageComponent f g h i z w v t
local notation3 (prettyPrint := false) "I" => IdealSheafData.stalk D x₀

/-- The actual minimal-prime label lies over the specified original image point. -/
theorem correspondenceRemainingImageComponentGenericLabel_projection
    (p : {p : PrimeSpectrum R // IsMin p}) (hp : I ≤ p.1.asIdeal) :
    π' ((T).fromSpecStalk x₀ p.1) = q t := by
  let F := integralComponentAt (q t)
  let y := correspondenceRemainingImageComponentGenericLabel f g h i z w v x t p hp
  let a := comapRestrict F π'
  have : Flat a := flat_comapRestrict F π'
  have ha : a y.1 = genericPoint F.subscheme := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using
      a.mem_genericPoints_of_flat y.2
  rw [← correspondenceRemainingImageComponentGenericLabel_spec f g h i z w v x t p hp]
  calc π' ((D).subschemeι y.1) = F.subschemeι (a y.1) := by
        simpa only [Scheme.Hom.comp_apply] using
          congrArg (fun m => m y.1) (comapRestrict_subschemeι F π').symm
    _ = q t := by rw [ha]; exact subschemeι_genericPoint_integralComponentAt (q t)

/-- The actual full localized quotient length is the native image-side flat-cycle weight
at the proved grade of the original image point. -/
theorem length_correspondenceRemainingImageComponentStalk_eq_flatPullbackWeight
    [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (p : {p : PrimeSpectrum R // IsMin p}) (hp : I ≤ p.1.asIdeal) :
    ((Module.length (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule p.1.asIdeal.primeCompl
        (correspondenceRemainingImageComponentStalk f g h i z w v x t))).toNat : ℤ) =
      flatPullbackWeight C sT π'
        (relativeDimension (C).dimensionFunction sJ (q t) +
          (correspondenceThirdSupportDimension K h i v : ℤ)) ((T).fromSpecStalk x₀ p.1) := by
  classical
  let y := correspondenceRemainingImageComponentGenericLabel f g h i z w v x t p hp
  have hy := correspondenceRemainingImageComponentGenericLabel_spec f g h i z w v x t p hp
  have hd := relativeDimension_comap_genericPoint_eq_add C sJ sT π' rfl
    (correspondenceThirdSupportDimension K h i v)
    (relativeDimension_correspondenceLeftImageExteriorProjection K f g h i z w v) (q t) y
  change relativeDimension (C).dimensionFunction sT
      ((D).subschemeι (correspondenceRemainingImageComponentGenericLabel
        f g h i z w v x t p hp).1) = _ at hd
  rw [hy] at hd
  rw [length_correspondenceRemainingImageComponentStalk_eq_componentMultiplicity
    f g h i z w v x t p hp]
  have hD : ((integralComponentAt (π' ((T).fromSpecStalk x₀ p.1))).comap π') = D :=
    congrArg (fun a => (integralComponentAt a).comap π')
      (correspondenceRemainingImageComponentGenericLabel_projection K f g h i z w v x t p hp)
  change componentMultiplicity (D).subschemeι
      (correspondenceRemainingImageComponentGenericLabel f g h i z w v x t p hp) =
    closedSubschemeCycleCoeff C sT
      ((integralComponentAt (π' ((T).fromSpecStalk x₀ p.1))).comap π').subschemeι
      (relativeDimension (C).dimensionFunction sJ (q t) +
        (correspondenceThirdSupportDimension K h i v : ℤ)) ((T).fromSpecStalk x₀ p.1)
  rw [closedSubschemeCycleCoeff_congr C sT hD]
  unfold closedSubschemeCycleCoeff
  let H : ∃ a : genericPoints (D).subscheme,
      (D).subschemeι a.1 = (T).fromSpecStalk x₀ p.1 ∧
        relativeDimension (C).dimensionFunction sT ((T).fromSpecStalk x₀ p.1) =
          relativeDimension (C).dimensionFunction sJ (q t) +
            (correspondenceThirdSupportDimension K h i v : ℤ) := ⟨y, hy, hd⟩
  rw [dite_eq_left H]
  have heq : Classical.choose H = y :=
    Subtype.ext ((D).subschemeι.isClosedEmbedding.injective
      ((Classical.choose_spec H).1.trans hy.symm))
  rw [heq]

/-- Factoring the original finite map through its image gives exactly the grade in native
02RG's fixed-original-label formula, without changing the full image multiplicity. -/
theorem length_correspondenceRemainingImageComponentStalk_eq_originalGradeWeight
    [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (p : {p : PrimeSpectrum R // IsMin p}) (hp : I ≤ p.1.asIdeal) :
    ((Module.length (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule p.1.asIdeal.primeCompl
        (correspondenceRemainingImageComponentStalk f g h i z w v x t))).toNat : ℤ) =
      flatPullbackWeight C sT π'
        (relativeDimension (C).dimensionFunction (q ≫ sJ) t +
          (correspondenceThirdSupportDimension K h i v : ℤ)) ((T).fromSpecStalk x₀ p.1) := by
  let := isFinite_correspondenceIncidenceToImage f g h z w hz hw
  rw [relativeDimension_eq_of_finite_residueField (C).dimensionFunction sJ q t
    (residueField_finite_of_locallyQuasiFinite q t)]
  exact length_correspondenceRemainingImageComponentStalk_eq_flatPullbackWeight
    K f g h i z w v x t p hp

open Classical in
/-- The full image-component quotient absorbs exactly the native image-exterior weights in
integer remaining Euler. No fibre factor is discarded or replaced by one. -/
theorem seqEuler_correspondenceRemainingImageComponentStalk_nativeWeights
    [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hx : x ∈ genericPoints (correspondenceLeftImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v x₀))
    (hs : IdealSheafData.stalk (pullback.diagonal h).ker
      (correspondenceLeftImageMiddlePair f g h i z w v x₀) = Ideal.span (Set.range s)) :
    Koszul.seqEuler
      (fun j => correspondenceRemainingImageMiddleStalkMap f g h i z w v x (s j))
      (correspondenceRemainingImageComponentStalk f g h i z w v x t) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        if I ≤ p.1.asIdeal then
          flatPullbackWeight C sT π'
            (relativeDimension (C).dimensionFunction sJ (q t) +
              (correspondenceThirdSupportDimension K h i v : ℤ))
            ((T).fromSpecStalk x₀ p.1) *
              Koszul.seqEuler
                (fun j => correspondenceRemainingImageMiddleStalkMap f g h i z w v x (s j))
                (R ⧸ p.1.asIdeal)
        else 0 := by
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian sT
  rw [seqEuler_correspondenceRemainingImageComponentStalk f g h i z w v x t hx s hs]
  apply finsum_congr
  intro p
  by_cases hp : I ≤ p.1.asIdeal
  · rw [dite_eq_left hp, ite_eq_left hp,
      ← length_correspondenceRemainingImageComponentStalk_eq_componentMultiplicity
        f g h i z w v x t p hp,
      length_correspondenceRemainingImageComponentStalk_eq_flatPullbackWeight
        K f g h i z w v x t p hp]
  · rw [dite_eq_right hp, ite_eq_right hp]

end Stacks.Chow
