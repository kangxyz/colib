/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageGenericStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageExteriorSquare
public import Colib.RingTheory.Koszul.GenericEuler
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes

/-!
# Remaining Euler on the full exterior of one original image component

For each original incidence point, take its actual image point closure in the
whole intermediate image and its scheme-theoretic inverse image in the image
exterior. The coefficient module below is the stalk quotient of that full
inverse image, not its reduction. Native local-ring/ideal-sheaf comparison
identifies each localized length with the actual component multiplicity.

The remaining list is the literal image of the original middle diagonal list.
Its ideal of definition follows from the actual generic remaining incidence,
not from a supplied finite-colength hypothesis. Integer Koszul Euler devissage
then retains all ambient minimal primes, including lower-dimensional ones with
their proved Euler contribution. Primes outside the full inverse-image support
have zero localized module. Nilpotent and inseparable exterior multiplicities
are retained. No identification with a separately constructed remaining
correspondence incidence is asserted here.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The full inverse image of the actual original image-point closure. -/
abbrev correspondenceRightRemainingImageComponent
    (t : correspondenceIncidence g h i w v) : ((correspondenceRightIntermediateImageProduct f g h
      i z w v)).IdealSheafData :=
  (integralComponentAt ((correspondenceIncidenceMap g h i w v).toImage t)).comap
    (correspondenceRightImageExteriorProjection f g h i z w v)


/-- The coefficient ring retains the full scheme-theoretic exterior of the image component. -/
abbrev correspondenceRightRemainingImageComponentStalk
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v) :=
  (correspondenceRightRemainingImageStalk f g h i z w v x) ⧸ (IdealSheafData.stalk
    (correspondenceRightRemainingImageComponent f g h i z w v t)
    (correspondenceRightImageIncidenceInclusion f g h i z w v x))

/-- Every ambient minimal prime containing the actual component ideal gives an actual generic
point of that full component exterior. The point identification is proved from native stalk
specialization and minimal-prime comparison. -/
theorem exists_correspondenceRightRemainingImageComponentGenericLabel
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    (p : {p : PrimeSpectrum (correspondenceRightRemainingImageStalk f g h i z w v x) // IsMin p})
      (hp : (IdealSheafData.stalk (correspondenceRightRemainingImageComponent f g h i z w v t)
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)) ≤ p.1.asIdeal) :
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let D := correspondenceRightRemainingImageComponent f g h i z w v t
    ∃ y : genericPoints (D).subscheme, (D).subschemeι y.1 = (T).fromSpecStalk x₀ p.1 := by
  dsimp only
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let D := correspondenceRightRemainingImageComponent f g h i z w v t
  let I := IdealSheafData.stalk D x₀
  have hmin : p.1.asIdeal ∈ (I).minimalPrimes := by
    refine ⟨⟨p.1.2, hp⟩, ?_⟩
    intro J hJ hJp
    exact p.2 (show (⟨J, hJ.1⟩ : PrimeSpectrum R) ≤ p.1 from hJp)
  have hmax := (fromSpecStalk_mem_componentGenericPointsThrough_iff D x₀ p.1).mpr hmin
  obtain ⟨y, hy⟩ := exists_subschemeι_eq_fromSpecStalk D x₀ p.1 hp
  have hgen : y ∈ genericPoints (D).subscheme := by
    apply (mem_genericPoints_iff_isMax (D).subscheme y).mpr
    intro y' hyy'
    have hy' : (D).subschemeι y' ∈ ((D).support : Set T) := by
      rw [← (D).range_subschemeι]
      exact ⟨y', rfl⟩
    have heq : (D).subschemeι y' = (D).subschemeι y := by
      apply (hmax.2.2 _ hy' ?_).trans hy.symm
      rw [← hy]
      exact (Scheme.le_iff_specializes.mp hyy').map (D).subschemeι.continuous
    exact le_of_eq ((D).subschemeι.isClosedEmbedding.injective heq)
  exact ⟨⟨y, hgen⟩, hy⟩

/-- The canonical label is selected from the proved actual-point identification. -/
def correspondenceRightRemainingImageComponentGenericLabel
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    (p : {p : PrimeSpectrum (correspondenceRightRemainingImageStalk f g h i z w v x) // IsMin p})
      (hp : (IdealSheafData.stalk (correspondenceRightRemainingImageComponent f g h i z w v t)
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)) ≤ p.1.asIdeal) :
    let D := correspondenceRightRemainingImageComponent f g h i z w v t
    genericPoints (D).subscheme := by
  dsimp only
  exact (exists_correspondenceRightRemainingImageComponentGenericLabel f g h i z w v x t p
    hp).choose

/-- The component label maps to the literal original local prime, without a reindexing premise. -/
theorem correspondenceRightRemainingImageComponentGenericLabel_spec
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    (p : {p : PrimeSpectrum (correspondenceRightRemainingImageStalk f g h i z w v x) // IsMin p})
      (hp : (IdealSheafData.stalk (correspondenceRightRemainingImageComponent f g h i z w v t)
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)) ≤ p.1.asIdeal) :
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let D := correspondenceRightRemainingImageComponent f g h i z w v t
    (D).subschemeι (correspondenceRightRemainingImageComponentGenericLabel
      f g h i z w v x t p hp).1 = (T).fromSpecStalk x₀ p.1 := by
  dsimp only
  exact (exists_correspondenceRightRemainingImageComponentGenericLabel f g h i z w v x t p
    hp).choose_spec

/-- Native 02S5's stalk comparison reads the actual localized quotient length as the full
nonreduced image-component exterior multiplicity. -/
theorem length_correspondenceRightRemainingImageComponentStalk_eq_componentMultiplicity
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    (p : {p : PrimeSpectrum (correspondenceRightRemainingImageStalk f g h i z w v x) // IsMin p})
      (hp : (IdealSheafData.stalk (correspondenceRightRemainingImageComponent f g h i z w v t)
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)) ≤ p.1.asIdeal) :
    let D := correspondenceRightRemainingImageComponent f g h i z w v t
    ((Module.length (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule p.1.asIdeal.primeCompl
        (correspondenceRightRemainingImageComponentStalk f g h i z w v x t))).toNat : ℤ) =
      componentMultiplicity (D).subschemeι
        (correspondenceRightRemainingImageComponentGenericLabel f g h i z w v x t p hp) := by
  dsimp only
  let D := correspondenceRightRemainingImageComponent f g h i z w v t
  exact length_localizedModule_quotient_idealStalk_eq_componentMultiplicity D p.1
    (correspondenceRightRemainingImageComponentGenericLabel f g h i z w v x t p hp)
    (correspondenceRightRemainingImageComponentGenericLabel_spec f g h i z w v x t p hp).symm

/-- The actual component multiplicity is a finite length in the locally Noetherian Cor scope.
This certificate is established before using its natural-number truncation as a weight. -/
theorem length_correspondenceRightRemainingImageComponentStalk_ne_top
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w v)]
    (p : {p : PrimeSpectrum (correspondenceRightRemainingImageStalk f g h i z w v x) // IsMin p})
      (hp : (IdealSheafData.stalk (correspondenceRightRemainingImageComponent f g h i z w v t)
      (correspondenceRightImageIncidenceInclusion f g h i z w v x)) ≤ p.1.asIdeal) :
    Module.length (Localization.AtPrime p.1.asIdeal)
      (LocalizedModule p.1.asIdeal.primeCompl
        (correspondenceRightRemainingImageComponentStalk f g h i z w v x t)) ≠ ⊤ := by
  let D := correspondenceRightRemainingImageComponent f g h i z w v t
  let y := correspondenceRightRemainingImageComponentGenericLabel f g h i z w v x t p hp
  have : IsLocallyNoetherian (D).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D).subschemeι
  let := generic_stalk_artinian y
  rw [length_localizedModule_quotient_idealStalk_eq_length_stalk D p.1 y.1
    (correspondenceRightRemainingImageComponentGenericLabel_spec f g h i z w v x t p hp).symm]
  exact Module.length_ne_top

open Classical in
/-- Genuine integer remaining Euler for the full image-component exterior, indexed by all
ambient minimal primes and carrying their actual nonreduced component multiplicities. -/
theorem seqEuler_correspondenceRightRemainingImageComponentStalk
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    [IsSeparated g] [IsLocallyNoetherian (correspondenceRightIntermediateImageProduct f g h i z w
      v)]
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)) = Ideal.span (Set.range s)) :
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let D := correspondenceRightRemainingImageComponent f g h i z w v t
    let I := IdealSheafData.stalk D x₀
    Koszul.seqEuler
      (fun j => correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x (s j))
      (correspondenceRightRemainingImageComponentStalk f g h i z w v x t) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        if hp : I ≤ p.1.asIdeal then
          componentMultiplicity (D).subschemeι
            (correspondenceRightRemainingImageComponentGenericLabel f g h i z w v x t p hp) *
              Koszul.seqEuler
                (fun j => correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x (s j))
                (R ⧸ p.1.asIdeal)
        else 0 := by
  dsimp only
  let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let R := correspondenceRightRemainingImageStalk f g h i z w v x
  let D := correspondenceRightRemainingImageComponent f g h i z w v t
  let I := IdealSheafData.stalk D x₀
  classical
  rw [Koszul.seqEuler_eq_finsum_minimalPrimes _ _
    (isIdealOfDefinition_correspondenceRightRemainingImageMiddleList f g h i z w v ⟨x, hx⟩ s hs)]
  apply finsum_congr
  intro p
  by_cases hp : I ≤ p.1.asIdeal
  · rw [dite_eq_left hp,
      length_correspondenceRightRemainingImageComponentStalk_eq_componentMultiplicity
        f g h i z w v x t p hp]
  · rw [dite_eq_right hp]
    have hnot : p.1 ∉ Module.support R
        (correspondenceRightRemainingImageComponentStalk f g h i z w v x t) := by
      rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
      simpa only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] using hp
    have hzero : Module.length (Localization.AtPrime p.1.asIdeal)
        (LocalizedModule p.1.asIdeal.primeCompl
          (correspondenceRightRemainingImageComponentStalk f g h i z w v x t)) = 0 :=
      Module.length_eq_zero_iff.mpr (Module.notMem_support_iff.mp hnot)
    simp only [hzero, ENat.toNat_zero, Nat.cast_zero, zero_mul]

end Stacks.Chow
