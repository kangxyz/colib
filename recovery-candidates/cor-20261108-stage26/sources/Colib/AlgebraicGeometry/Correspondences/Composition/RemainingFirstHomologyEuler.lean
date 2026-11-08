/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingOriginalList
public import Colib.RingTheory.Koszul.GenericEuler
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Remaining Euler devissage of the actual first-stage homology modules

Every first Koszul homology module carries the proved action of the full
first-stage exterior stalk. Its finiteness follows from the actual exterior
closed immersion, native finite Koszul homology, and restriction of scalars
along the actual quotient map. There is no assumed action comparison.

The literal image of the original remaining-diagonal list generates the
remaining ideal, proved to be an ideal of definition at a generic triple
intersection. Native integer Euler devissage is applied to each actual first
homology module before summing with its original higher-degree sign. All
minimal primes of the unreduced first-stage local ring occur, including
lower-dimensional terms with their proved zero Euler contribution.

This local formula does not yet identify the localized first-homology weights
with original pair coefficients under exterior flat base change, nor assemble
the finite-image residue degrees. Those comparisons remain separate obligations.
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

/-- The actual full exterior stalk is finite over the actual sixfold stalk,
by surjectivity of the original closed-immersion stalk map. -/
instance finite_correspondenceTripleIncidenceSupportStalkModule
    (x : correspondenceTripleIncidence f g h i z w v) :
    Module.Finite (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x) := by
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
  let φ := (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x))).hom ≫
      (correspondenceTripleSupportProductInclusion f g h i z w v).stalkMap
        (correspondenceTripleIncidenceToTripleSupport f g h i z w v x)).hom
  have hφ : Function.Surjective φ :=
    (SurjectiveOnStalks.stalkMap_surjective
      (correspondenceTripleSupportProductInclusion f g h i z w v)
      (correspondenceTripleIncidenceToTripleSupport f g h i z w v x)).comp
      (ConcreteCategory.bijective_of_isIso
        ((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
          (Inseparable.of_eq
            (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x))).hom).2
  let L : A →ₗ[A] M :=
    { toFun := φ
      map_add' := φ.map_add
      map_smul' := fun a b => φ.map_mul a b }
  exact Module.Finite.of_surjective L hφ

/-- The actual first Koszul homology, viewed over the full first-stage local
ring through the already proved quotient action. The carrier is unchanged. -/
abbrev correspondenceRemainingFirstKoszulModule [IsSeparated g]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) : ModuleCat (correspondenceRemainingOriginalStalk f g h i z w v x) :=
  letI := correspondenceTripleIncidenceFirstKoszulModule f g h i z w v x t hr ht n
  ModuleCat.of (correspondenceRemainingOriginalStalk f g h i z w v x)
    ((Koszul.seqComplexTensor t.get
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n)

/-- The actual first homology is finite over its actual first-stage stalk.
The scalar tower is derived from the original stalk map, not hypothesized. -/
instance finite_correspondenceRemainingFirstKoszulModule [IsSeparated g]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) :
    Module.Finite (correspondenceRemainingOriginalStalk f g h i z w v x)
      (correspondenceRemainingFirstKoszulModule f g h i z w v x t hr ht n) := by
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
  let R := correspondenceRemainingOriginalStalk f g h i z w v x
  let H := (Koszul.seqComplexTensor t.get
    (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n
  let := correspondenceTripleIncidenceFirstKoszulModule f g h i z w v x t hr ht n
  let := (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x).toAlgebra
  let := correspondenceTripleIncidenceFirstKoszulScalarTower f g h i z w v x t hr ht n
  exact Module.Finite.of_restrictScalars_finite A R H

/-- Apply native Euler devissage to each genuine first-stage homology module.
Finite colength comes from the actual generic remaining intersection. -/
theorem correspondenceRemainingFirstHomologyEuler_eq_finsum [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v))
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList t)
    (hs : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList s)
    (n : ℕ) :
    let R := correspondenceRemainingOriginalStalk f g h i z w v x.1
    let b := s.map (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1)
    let H := correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t hr ht n
    Koszul.seqEuler b.get H =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        ((Module.length (Localization.AtPrime p.1.asIdeal)
          (LocalizedModule p.1.asIdeal.primeCompl H)).toNat : ℤ) *
            Koszul.seqEuler b.get (R ⧸ p.1.asIdeal) := by
  let := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceLeftIntermediateAmbientInclusion f g h i z w v)
  exact Koszul.seqEuler_eq_finsum_minimalPrimes _ _
    (isIdealOfDefinition_correspondenceRemainingOriginalList f g h i z w v x s hs)

/-- The signed generic weights are computed from the actual first homology in
every degree before summing; they are not replaced by the fundamental cycle. -/
theorem sum_signed_correspondenceRemainingFirstHomologyEuler_eq_finsum
    [IsSeparated g] [IsSeparated h]
    [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
    (x : genericPoints (correspondenceTripleIncidence f g h i z w v))
    (t s : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x.1) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList t)
    (hs : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x.1) = Ideal.ofList s)
    (J : Finset ℕ) :
    let R := correspondenceRemainingOriginalStalk f g h i z w v x.1
    let b := s.map (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x.1)
    let H := fun n => correspondenceRemainingFirstKoszulModule f g h i z w v x.1 t hr ht n
    ∑ n ∈ J, (-1 : ℤ) ^ n * Koszul.seqEuler b.get (H n) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        (∑ n ∈ J, (-1 : ℤ) ^ n *
          ((Module.length (Localization.AtPrime p.1.asIdeal)
            (LocalizedModule p.1.asIdeal.primeCompl (H n))).toNat : ℤ)) *
              Koszul.seqEuler b.get (R ⧸ p.1.asIdeal) := by
  let := LocallyOfFiniteType.isLocallyNoetherian
    (correspondenceLeftIntermediateAmbientInclusion f g h i z w v)
  exact Koszul.sum_signed_seqEuler_eq_finsum_minimalPrimes _ _
    (isIdealOfDefinition_correspondenceRemainingOriginalList f g h i z w v x s hs) J

end Stacks.Chow
