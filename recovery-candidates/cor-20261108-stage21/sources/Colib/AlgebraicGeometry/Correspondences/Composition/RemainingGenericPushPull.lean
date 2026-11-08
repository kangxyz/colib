/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingExteriorGrade
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingImageGenericStalk

/-!
# Native finite push-pull retains the original exterior generic labels

Over an image-exterior generic point, the actual finite exterior fibre consists
entirely of generic points of the full source exterior. This is proved from
native generic specialization and discreteness of a finite fibre. Reindexing
native 02RG along this actual bijection and applying the proved dimension grade
replaces source weights by their full closed-fibre lengths. Original labels and
residue degrees are retained, including collisions. The image-side multiplicity
remains the native full flat-pullback weight.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable (K : Type u) [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

local notation3 (prettyPrint := false) "C" => fieldChowSituation K
local notation3 (prettyPrint := false) "E" =>
  correspondenceLeftIntermediateSupportProduct f g h i z w v
local notation3 (prettyPrint := false) "T" =>
  correspondenceLeftIntermediateImageProduct f g h i z w v
local notation3 (prettyPrint := false) "q" => (correspondenceIncidenceMap f g h z w).toImage
local notation3 (prettyPrint := false) "q'" =>
  correspondenceLeftIntermediateImageMap f g h i z w v
local notation3 (prettyPrint := false) "π" => correspondenceLeftExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "π'" =>
  correspondenceLeftImageExteriorProjection f g h i z w v
local notation3 (prettyPrint := false) "sJ" => correspondenceIntermediateImageTarget f g h z w ≫ h
local notation3 (prettyPrint := false) "sV" =>
  (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)
local notation3 (prettyPrint := false) "sI" => q ≫ sJ
local notation3 (prettyPrint := false) "sE" => π ≫ sI
local notation3 (prettyPrint := false) "sT" => π' ≫ sJ

/-- Every point in the actual finite fibre over an image generic point is an original exterior
generic label. No component is discarded by restricting this fibre to generic points. -/
theorem correspondenceLeftIntermediateImageMap_preimage_generic [IsSeparated h]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (p : genericPoints T) (a : E) (ha : q' a = p.1) : a ∈ genericPoints E := by
  let := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
  obtain ⟨η, hη, hηa⟩ := exists_mem_genericPoints_specializes a
  have hs : q' η ⤳ p.1 := ha ▸ hηa.map (q').continuous
  have he : q' η = p.1 := (hs.antisymm (genericPoint_isMax p.1 p.2 hs)).eq
  have hea : η = a :=
    ((q').isDiscrete_preimage_singleton p.1).eq_of_specializes hηa he ha
  exact hea ▸ hη

/-- The original image-stalk minimal prime gives the actual image-exterior generic point.
This uses its native fromSpecStalk map, without substituting a different generic label. -/
theorem correspondenceRemainingImageStalk_minimal_generic
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (p : {p : PrimeSpectrum (correspondenceRemainingImageStalk f g h i z w v x) // IsMin p}) :
    (T).fromSpecStalk (correspondenceLeftImageIncidenceInclusion f g h i z w v x) p.1 ∈
      genericPoints T := by
  have hp : p.1 ∈ genericPoints (Spec (correspondenceRemainingImageStalk f g h i z w v x)) := by
    apply (mem_genericPoints_iff_isMax _ _).mpr
    intro b hb
    apply Scheme.le_iff_specializes.mpr
    apply (PrimeSpectrum.le_iff_specializes _ _).mp
    apply p.2
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr (Scheme.le_iff_specializes.mp hb)
  exact ((T).fromSpecStalk
    (correspondenceLeftImageIncidenceInclusion f g h i z w v x)).mem_genericPoints_of_flat hp

open Classical in
/-- Fixed-original-label native 02RG, now literally summed over all original exterior generic
labels above the chosen image generic point, with the true full fibre length and residue degree. -/
theorem correspondenceLeftImage_fixedLabel_genericPushPull
    [IsSeparated h] [LocallyOfFiniteType sJ] [LocallyOfFiniteType sV]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (t : correspondenceIncidence f g h z w) (p : genericPoints T) (hp : π' p.1 = q t) :
    letI := isFinite_correspondenceIncidenceToImage f g h z w hz hw
    letI := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
    ((q).residueDegree t : ℤ) * flatPullbackWeight C sT π'
      (relativeDimension (C).dimensionFunction sI t +
        (correspondenceThirdSupportDimension K h i v : ℤ)) p.1 =
      ∑ᶠ η : {η : genericPoints E // q' η.1 = p.1},
        if π η.1.1 = t then
          (correspondenceLeftExteriorFiberLength f g h i z w v η.1.1 : ℤ) *
            ((q').residueDegree η.1.1 : ℤ)
        else 0 := by
  classical
  let := isFinite_correspondenceIncidenceToImage f g h z w hz hw
  let := isFinite_correspondenceLeftIntermediateImageMap f g h i z w v hz hw
  refine (correspondenceLeftImage_fixedLabel_pushPull K f g h i z w v hz hw t p.1 hp).trans ?_
  let j := relativeDimension (C).dimensionFunction sI t +
    (correspondenceThirdSupportDimension K h i v : ℤ)
  let F : E → ℤ := fun a => if π a = t then
    flatPullbackWeight C sE π j a * ((q').residueDegree a : ℤ) else 0
  let e : {a : E // q' a = p.1} ≃ {η : genericPoints E // q' η.1 = p.1} :=
    { toFun := fun a => ⟨⟨a.1, correspondenceLeftIntermediateImageMap_preimage_generic
          K f g h i z w v hz hw p a.1 a.2⟩, a.2⟩
      invFun := fun η => ⟨η.1.1, η.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (∑ᶠ a ∈ {a : E | q' a = p.1}, F a) = _
  rw [← finsum_subtype_eq_finsum_cond (f := F)]
  apply finsum_eq_of_bijective e e.bijective
  intro a
  dsimp only [F, e]
  by_cases ha : π a.1 = t
  · rw [ite_eq_left ha, ite_eq_left ha]
    congr 1
    have hwgt := flatPullbackWeight_correspondenceLeftExterior_originalGrade
      K f g h i z w v hz hw
      ⟨a.1, correspondenceLeftIntermediateImageMap_preimage_generic
        K f g h i z w v hz hw p a.1 a.2⟩
    simpa only [ha] using hwgt
  · rw [ite_eq_right ha, ite_eq_right ha]

end Stacks.Chow
