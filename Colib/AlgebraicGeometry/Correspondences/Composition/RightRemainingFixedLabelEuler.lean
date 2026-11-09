/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImageComponentWeight
public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingGenericPushPull

/-!
# Remaining Euler after genuine fixed-original-label finite push-pull

For one original incidence point `t`, its original residue degree times the
remaining Euler characteristic of the full image-component exterior equals the
sum over all original exterior generic labels lying over it. Every summand
retains its actual closed-fibre length and finite-map residue degree. The image
exterior multiplicity is absorbed by the full nonreduced quotient Euler formula,
not cancelled or assumed to be one. Native 02RG, the proved point-grade formula,
and actual component Euler devissage supply the equality.

The outer index is every minimal prime of the actual image-exterior local ring.
The grouping condition is proved from the actual Cartesian square. In particular,
terms outside the image-component support vanish because no original exterior
label in that group exists, not by an assumed regrouping equation.
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

/-- The actual component-support condition at an ambient minimal prime is exactly the
specified original image label, not merely membership in its closure. -/
theorem correspondenceRightRemainingImageComponent_stalk_le_iff_projection
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    (p : {p : PrimeSpectrum (correspondenceRightRemainingImageStalk f g h i z w v x) // IsMin p}) :
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let π' := correspondenceRightImageExteriorProjection f g h i z w v
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let D := correspondenceRightRemainingImageComponent f g h i z w v t
    let I := IdealSheafData.stalk D x₀
    I ≤ p.1.asIdeal ↔ π' ((T).fromSpecStalk x₀ p.1) = q t := by
  dsimp only
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let q := (correspondenceIncidenceMap g h i w v).toImage
  let π' := correspondenceRightImageExteriorProjection f g h i z w v
  let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let D := correspondenceRightRemainingImageComponent f g h i z w v t
  constructor
  · exact correspondenceRightRemainingImageComponentGenericLabel_projection K f g h i z w v x t p
  · intro hp
    apply (le_iff_fromSpecStalk_mem_support D x₀ p.1).mpr
    change (T).fromSpecStalk x₀ p.1 ∈
      (((integralComponentAt (q t)).comap π').support : Set T)
    rw [Scheme.IdealSheafData.support_comap]
    change π' ((T).fromSpecStalk x₀ p.1) ∈ ((integralComponentAt (q t)).support : Set _)
    rw [hp, coe_support_integralComponentAt]
    exact subset_closure (Set.mem_singleton _)

open Classical in
/-- Genuine fixed-original-label weighted remaining Euler on the full image schemes.
The full image-exterior multiplicity is retained inside the left quotient Euler. -/
theorem residueDegree_mul_seqEuler_correspondenceRightRemainingImageComponentStalk
    (x : correspondenceRightImageIncidence f g h i z w v)
    (t : correspondenceIncidence g h i w v)
    [IsSeparated g] [IsSeparated i] [LocallyOfFiniteType (((correspondenceIncidenceMap g h i w
      v).imageι ≫ pullback.fst g i) ≫ g)] [LocallyOfFiniteType ((((integralComponentAt
      z).subschemeι ≫ pullback.snd f g) ≫ g))]
    (hw : IsFiniteCorrespondencePoint g h w) (hv : IsFiniteCorrespondencePoint h i v)
    (hx : x ∈ genericPoints (correspondenceRightImageIncidence f g h i z w v)) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)))
    (hs : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceRightImageMiddlePair f g h i z w v
        (correspondenceRightImageIncidenceInclusion f g h i z w v x)) = Ideal.span (Set.range s)) :
    let E := correspondenceRightIntermediateSupportProduct f g h i z w v
    let T := correspondenceRightIntermediateImageProduct f g h i z w v
    let q := (correspondenceIncidenceMap g h i w v).toImage
    let q' := correspondenceRightIntermediateImageMap f g h i z w v
    let π := correspondenceRightExteriorProjection f g h i z w v
    let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    ((q).residueDegree t : ℤ) * Koszul.seqEuler (fun j => α (s j))
      (correspondenceRightRemainingImageComponentStalk f g h i z w v x t) =
      ∑ᶠ p : {p : PrimeSpectrum R // IsMin p},
        (∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          if π η.1.1 = t then
            (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ) *
              ((q').residueDegree η.1.1 : ℤ)
          else 0) * Koszul.seqEuler (fun j => α (s j)) (R ⧸ p.1.asIdeal) := by
  dsimp only
  let E := correspondenceRightIntermediateSupportProduct f g h i z w v
  let T := correspondenceRightIntermediateImageProduct f g h i z w v
  let q := (correspondenceIncidenceMap g h i w v).toImage
  let q' := correspondenceRightIntermediateImageMap f g h i z w v
  let π := correspondenceRightExteriorProjection f g h i z w v
  let π' := correspondenceRightImageExteriorProjection f g h i z w v
  let sJ := ((correspondenceIncidenceMap g h i w v).imageι ≫ pullback.fst g i) ≫ g
  let x₀ := correspondenceRightImageIncidenceInclusion f g h i z w v x
  let D := correspondenceRightRemainingImageComponent f g h i z w v t
  let I := IdealSheafData.stalk D x₀
  classical
  let := isFinite_correspondenceIncidenceToImage g h i w v hw hv
  let := isFinite_correspondenceRightIntermediateImageMap f g h i z w v hw hv
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian (π' ≫ sJ)
  rw [seqEuler_correspondenceRightRemainingImageComponentStalk f g h i z w v x t hx s hs,
    mul_finsum]
  apply finsum_congr
  intro p
  let p' : genericPoints T :=
    ⟨(T).fromSpecStalk x₀ p.1,
      correspondenceRightRemainingImageStalk_minimal_generic K f g h i z w v x p⟩
  by_cases hp : I ≤ p.1.asIdeal
  · rw [dite_eq_left hp, ← mul_assoc]
    congr 1
    rw [← length_correspondenceRightRemainingImageComponentStalk_eq_componentMultiplicity
      f g h i z w v x t p hp,
      length_correspondenceRightRemainingImageComponentStalk_eq_originalGradeWeight
        K f g h i z w v x t hw hv p hp]
    exact correspondenceRightImage_fixedLabel_genericPushPull K f g h i z w v hw hv t p'
      ((correspondenceRightRemainingImageComponent_stalk_le_iff_projection
        K f g h i z w v x t p).mp hp)
  · rw [dite_eq_right hp, mul_zero]
    have hzsum :
        (∑ᶠ η : {η : genericPoints E // q' η.1 = (T).fromSpecStalk x₀ p.1},
          if π η.1.1 = t then
            (correspondenceRightExteriorFiberLength f g h i z w v η.1.1 : ℤ) *
              ((q').residueDegree η.1.1 : ℤ) else 0) = 0 := by
      apply finsum_eq_zero_of_forall_eq_zero
      intro η
      have hne : π η.1.1 ≠ t := by
        intro he
        apply hp
        apply (correspondenceRightRemainingImageComponent_stalk_le_iff_projection
          K f g h i z w v x t p).mpr
        calc π' ((T).fromSpecStalk x₀ p.1) = π' (q' η.1.1) := congrArg π' η.2.symm
          _ = q (π η.1.1) := by
            simpa only [Scheme.Hom.comp_apply] using
              congrArg (fun m => m η.1.1)
                (correspondenceRightIntermediateImageMap_projection f g h i z w v)
          _ = q t := congrArg q he
      exact ite_eq_right hne
    rw [hzsum, zero_mul]

end Stacks.Chow
