/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingExteriorGrade
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageGenericStalk
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

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

/-- Every point in the actual finite fibre over an image generic point is an original exterior
generic label. No component is discarded by restricting this fibre to generic points. -/
theorem correspondenceRightIntermediateImageMap_preimage_generic [IsSeparated i]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (p : genericPoints (correspondenceRightIntermediateImageProduct f g h i z w v)) (a :
      (correspondenceRightIntermediateSupportProduct f g h i z w v)) (ha :
      (correspondenceRightIntermediateImageMap f g h i z w v) a = p.1) :
    let E := correspondenceRightIntermediateSupportProduct f g h i z w v
    a ∈ genericPoints E := by
  dsimp only
  let E := correspondenceRightIntermediateSupportProduct f g h i z w v
  let q' := correspondenceRightIntermediateImageMap f g h i z w v
  let := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
  apply (mem_genericPoints_iff_isMax E a).mpr
  intro η hη
  have hηa : η ⤳ a := Scheme.le_iff_specializes.mp hη
  have hs : q' η ⤳ p.1 := ha ▸ hηa.map (q').continuous
  have he : q' η = p.1 := (hs.antisymm (genericPoint_isMax p.1 p.2 hs)).eq
  have hea : η = a :=
    ((q').isDiscrete_preimage_singleton p.1).eq_of_specializes hηa he ha
  exact hea.le

/-- The original image-stalk minimal prime gives the actual image-exterior generic point.
This uses its native fromSpecStalk map, without substituting a different generic label. -/
theorem correspondenceRightRemainingImageStalk_minimal_generic
    (x : correspondenceRightImageIncidence f g h i z w v)
    (p : {p : PrimeSpectrum (correspondenceRightRemainingImageStalk f g h i z w v x) // IsMin p}) :
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    (T).fromSpecStalk (correspondenceRightImageIncidenceInclusion f g h i z w v x) p.1 ∈
      genericPoints T := by
  dsimp only
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  have hp : p.1 ∈ genericPoints
      (Spec (correspondenceRightRemainingImageStalk f g h i z w v x)) := by
    apply (mem_genericPoints_iff_isMax _ _).mpr
    intro b hb
    apply Scheme.le_iff_specializes.mpr
    apply (PrimeSpectrum.le_iff_specializes _ _).mp
    apply p.2
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr (Scheme.le_iff_specializes.mp hb)
  let := flat_fromSpecStalk T (correspondenceRightImageIncidenceInclusion f g h i z w v x)
  exact ((T).fromSpecStalk
    (correspondenceRightImageIncidenceInclusion f g h i z w v x)).mem_genericPoints_of_flat hp

open Classical in
/-- Fixed-original-label native 02RG, now literally summed over all original exterior generic
labels above the chosen image generic point, with the true full fibre length and residue degree. -/
theorem correspondenceRightImage_fixedLabel_genericPushPull
    [IsSeparated i] [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w v).imageι ≫
      pullback.fst g i) ≫ g)] [LocallyOfFiniteType ((((integralComponentAt z).subschemeι ≫
      pullback.snd f g) ≫ g))]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (t : correspondenceIncidence g h i w v) (p : genericPoints
      (correspondenceRightIntermediateImageProduct f g h i z w v)) (hp :
      (correspondenceRightImageExteriorProjection f g h i z w v) p.1 =
      ((correspondenceIncidenceMap g h i w v).toImage) t) :
    let C := fieldChowSituation K
    let E := correspondenceRightIntermediateSupportProduct f g h i z w v
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let π := correspondenceRightExteriorProjection f g h i z w v
    let π' := correspondenceRightImageExteriorProjection f g h i z w v
    let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
    let sI := q ≫ sJ
    let sT := π' ≫ sJ
    letI := isFinite_correspondenceIncidenceToImage g h i w v hw hv
    letI := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
    ((q).residueDegree t : ℤ) * flatPullbackWeight C sT π'
      (relativeDimension (C).dimensionFunction sI t +
        (correspondenceFirstSupportDimension K f g z : ℤ)) p.1 =
      ∑ᶠ η : {η : genericPoints E // q' η.1 = p.1},
        if π η.1.1 = t then
          (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ) *
            ((q').residueDegree η.1.1 : ℤ)
        else 0 := by
  dsimp only
  let C := fieldChowSituation K
  let E := correspondenceRightIntermediateSupportProduct f g h i z w v
  let q := (correspondenceIncidenceMap g h i w v).toImage
  let q' := correspondenceRightIntermediateImageMap f g h i z w v
  let π := correspondenceRightExteriorProjection f g h i z w v
  let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
  let sI := q ≫ sJ
  let sE := π ≫ sI
  classical
  let := isFinite_correspondenceIncidenceToImage g h i w v hw hv
  let := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
  refine (correspondenceRightImage_fixedLabel_pushPull K f g h i z w v hw hv t p.1 hp).trans ?_
  let j := relativeDimension (C).dimensionFunction sI t +
    (correspondenceFirstSupportDimension K f g z : ℤ)
  let F : E → ℤ := fun a => if π a = t then
    flatPullbackWeight C sE π j a * ((q').residueDegree a : ℤ) else 0
  let e : {a : E // q' a = p.1} ≃ {η : genericPoints E // q' η.1 = p.1} :=
    { toFun := fun a => ⟨⟨a.1, correspondenceRightIntermediateImageMap_preimage_generic
          K f g h i z w v hw hv p a.1 a.2⟩, a.2⟩
      invFun := fun η => ⟨η.1.1, η.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  change (∑ᶠ a ∈ {a : E | q' a = p.1}, F a) = _
  rw [← finsum_subtype_eq_finsum_cond (f := F)]
  apply finsum_eq_of_bijective e e.bijective
  intro a
  change (if π a.1 = t then flatPullbackWeight C sE π j a.1 *
      ((q').residueDegree a.1 : ℤ) else 0) =
    (if π a.1 = t then (correspondenceRightExteriorFiberLength f g h i z w v a.1 : ℤ) *
      ((q').residueDegree a.1 : ℤ) else 0)
  by_cases ha : π a.1 = t
  · rw [ite_eq_left ha, ite_eq_left ha]
    congr 1
    have hwgt := flatPullbackWeight_correspondenceRightExterior_originalGrade
      K f g h i z w v hw hv
      ⟨a.1, correspondenceRightIntermediateImageMap_preimage_generic
        K f g h i z w v hw hv p a.1 a.2⟩
    change flatPullbackWeight C sE π
      (relativeDimension C.dimensionFunction sI (π a.1) +
        (correspondenceFirstSupportDimension K f g z : ℤ)) a.1 = _ at hwgt
    simpa only [ha, j] using hwgt
  · rw [ite_eq_right ha, ite_eq_right ha]

end Stacks.Chow
