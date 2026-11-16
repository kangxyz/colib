/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.IntegralOverlapGeometry

/-!
# The Laurent open in the relative projective line

The geometric intersection is a base change of the integral standard open
at the product of the two homogeneous variables.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent

namespace AlgebraicGeometry.Scheme.ProjectiveLine

universe u

variable (S : Scheme.{u})

/-- The actual relative overlap, regarded as an open of the projective line. -/
abbrev standardOverlapOpen : (projectiveSpaceOver 1 S).Opens :=
  (projectiveSpaceOver.toIntegralAtUniverse 1 S) ⁻¹ᵁ integralOverlap

/-- Both pullback definitions produce the intersection of the original opens. -/
theorem standardOverlapOpen_eq :
    standardOverlapOpen S = positiveChart S ⊓ negativeChart S := by
  rw [standardOverlapOpen, integralOverlap_eq, Scheme.Hom.preimage_inf]
  rfl

/-- The two inclusion maps from the intersection are an actual pullback. -/
theorem standardOverlapOpen_isPullback :
    IsPullback ((projectiveSpaceOver 1 S).homOfLE
        ((standardOverlapOpen_eq S).trans_le inf_le_left))
      ((projectiveSpaceOver 1 S).homOfLE ((standardOverlapOpen_eq S).trans_le inf_le_right))
      (positiveChart S).ι (negativeChart S).ι := by
  exact (isPullback_opens_inf (positiveChart S) (negativeChart S)).of_iso
    ((projectiveSpaceOver 1 S).isoOfEq (standardOverlapOpen_eq S)).symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [← cancel_mono (positiveChart S).ι])
    (by simp [← cancel_mono (negativeChart S).ι]) (by simp) (by simp)

/-- The overlap as an open of the negative chart, identified with the ambient intersection. -/
def chartOverlapIsoStandardOverlapOpen :
    (chartOverlap S).toScheme ≅ (standardOverlapOpen S).toScheme :=
  (overlap_isPullback S).isoPullback ≪≫ (standardOverlapOpen_isPullback S).isoPullback.symm

/-- Base changing an integral open in the canonical projective line and retaining its
projection to the integral open. -/
def standardOpenIntegralPullbackIso (W : (projectiveSpaceAtUniverse.{u} 1).Opens) :
    ((projectiveSpaceOver.toIntegralAtUniverse 1 S) ⁻¹ᵁ W).toScheme ≅
      pullback (terminal.from S) (terminal.from W.toScheme) :=
  (pullbackRestrictIsoRestrict (projectiveSpaceOver.toIntegralAtUniverse 1 S) W).symm ≪≫
  pullbackLeftPullbackSndIso (terminal.from S)
    (terminal.from (projectiveSpaceAtUniverse 1)) W.ι ≪≫
  pullback.congrHom rfl (terminal.comp_from W.ι)

@[reassoc]
theorem standardOpenIntegralPullbackIso_hom_fst (W : (projectiveSpaceAtUniverse.{u} 1).Opens) :
    (standardOpenIntegralPullbackIso S W).hom ≫ pullback.fst _ _ =
      ((projectiveSpaceOver.toIntegralAtUniverse 1 S) ⁻¹ᵁ W).ι ≫
        pullback.fst (terminal.from S) (terminal.from (projectiveSpaceAtUniverse 1)) := by
  simp [standardOpenIntegralPullbackIso, pullback.congrHom_hom,
    pullbackRestrictIsoRestrict_inv_fst_assoc]

@[reassoc]
theorem standardOpenIntegralPullbackIso_hom_snd (W : (projectiveSpaceAtUniverse.{u} 1).Opens) :
    (standardOpenIntegralPullbackIso S W).hom ≫ pullback.snd _ _ =
      projectiveSpaceOver.toIntegralAtUniverse 1 S ∣_ W := by
  simp [standardOpenIntegralPullbackIso, pullback.congrHom_hom, morphismRestrict]

/-- The actual inclusion in the base-changed opens commutes with both projections. -/
@[reassoc]
theorem standardOpenIntegralPullbackIso_hom_natural
    {U V : (projectiveSpaceAtUniverse.{u} 1).Opens} (h : U ≤ V) :
    (projectiveSpaceOver 1 S).homOfLE
        ((projectiveSpaceOver.toIntegralAtUniverse 1 S).preimage_mono h) ≫
      (standardOpenIntegralPullbackIso S V).hom =
    (standardOpenIntegralPullbackIso S U).hom ≫
      pullback.map (terminal.from S) (terminal.from U.toScheme)
        (terminal.from S) (terminal.from V.toScheme) (𝟙 S)
        ((projectiveSpaceAtUniverse 1).homOfLE h) (𝟙 _)
        (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, Category.comp_id, pullback.lift_fst,
      standardOpenIntegralPullbackIso_hom_fst]
    exact (projectiveSpaceOver 1 S).homOfLE_ι_assoc _ _
  · simp only [Category.assoc, pullback.map, pullback.lift_snd,
      standardOpenIntegralPullbackIso_hom_snd, standardOpenIntegralPullbackIso_hom_snd_assoc]
    rw [← cancel_mono V.ι]
    simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
    exact (projectiveSpaceOver 1 S).homOfLE_ι_assoc _ _

/-- The overlap regarded in the projective line is a base change of the integral overlap. -/
def standardOverlapIntegralPullbackIso :
    (standardOverlapOpen S).toScheme ≅
      pullback (terminal.from S) (terminal.from (integralOverlap.{u}).toScheme) :=
  standardOpenIntegralPullbackIso S integralOverlap

@[reassoc]
theorem chartOverlapIsoStandardOverlapOpen_hom_positive :
    (chartOverlapIsoStandardOverlapOpen S).hom ≫
      (projectiveSpaceOver 1 S).homOfLE ((standardOverlapOpen_eq S).trans_le inf_le_left) =
      overlapToPositive S := by
  simp [chartOverlapIsoStandardOverlapOpen]

@[reassoc]
theorem chartOverlapIsoStandardOverlapOpen_hom_negative :
    (chartOverlapIsoStandardOverlapOpen S).hom ≫
      (projectiveSpaceOver 1 S).homOfLE ((standardOverlapOpen_eq S).trans_le inf_le_right) =
      overlapToNegative S := by
  simp [chartOverlapIsoStandardOverlapOpen]

/-- The same pullback after comparison of the two integral base schemes. -/
def integralProductComparison (X : Scheme.{u}) {A B : Scheme.{u}}
    (e : A ≅ B) (q : B ⟶ Spec (.of (ULift.{u} ℤ))) :
    pullback (terminal.from X) (terminal.from A) ≅
      pullback (specULiftZIsTerminal.from X) q := by
  let t := terminalIsTerminal.uniqueUpToIso specULiftZIsTerminal.{u}
  let f := terminal.from X
  let g := terminal.from A
  let f' := specULiftZIsTerminal.from X
  have h₁ : f ≫ t.hom = 𝟙 X ≫ f' := specULiftZIsTerminal.hom_ext _ _
  have h₂ : g ≫ t.hom = e.hom ≫ q := specULiftZIsTerminal.hom_ext _ _
  let m := pullback.map f g f' q (𝟙 X) e.hom t.hom h₁ h₂
  letI : IsIso m := by
    dsimp [m]
    infer_instance
  exact asIso m

@[reassoc]
private theorem integralProductComparison_fst (X : Scheme.{u}) {A B : Scheme.{u}}
    (e : A ≅ B) (q : B ⟶ Spec (.of (ULift.{u} ℤ))) :
    (integralProductComparison X e q).hom ≫ pullback.fst _ _ = pullback.fst _ _ := by
  simp [integralProductComparison]

@[reassoc]
private theorem integralProductComparison_snd (X : Scheme.{u}) {A B : Scheme.{u}}
    (e : A ≅ B) (q : B ⟶ Spec (.of (ULift.{u} ℤ))) :
    (integralProductComparison X e q).hom ≫ pullback.snd _ _ = pullback.snd _ _ ≫ e.hom := by
  simp [integralProductComparison]

/-- The original relative chart overlap is the same Laurent product used by Bass theory. -/
def standardOverlapLaurentIso (X : QuasiCompactSchemes.{u}) :
    (chartOverlap X.obj).toScheme ≅ (Relative.laurentFunctor.obj X).obj :=
  chartOverlapIsoStandardOverlapOpen X.obj ≪≫ standardOverlapIntegralPullbackIso X.obj ≪≫
    integralProductComparison X.obj integralOverlapLaurentIso
      (PolynomialLaurent.laurentProjection (.of (ULift.{u} ℤ)))

private theorem standardChartPolynomialIso_eq (X : QuasiCompactSchemes.{u}) (i : Fin 2) :
    standardChartPolynomialIso X i =
      standardOpenIntegralPullbackIso X.obj (integralChart i) ≪≫
        integralProductComparison X.obj (integralChartPolynomialIso i)
          (PolynomialLaurent.polynomialProjection (.of (ULift.{u} ℤ))) := rfl

private theorem standardOverlapLaurentIso_leg
    (X : QuasiCompactSchemes.{u}) (i : Fin 2) (h : integralOverlap ≤ integralChart i)
    (ℓ : (chartOverlap X.obj).toScheme ⟶ (standardChart X.obj i).toScheme)
    (hℓ : (chartOverlapIsoStandardOverlapOpen X.obj).hom ≫
      (projectiveSpaceOver 1 X.obj).homOfLE
        ((projectiveSpaceOver.toIntegralAtUniverse 1 X.obj).preimage_mono h) = ℓ)
    (f : Spec (.of (LaurentPolynomial (ULift.{u} ℤ))) ⟶
      Spec (.of (Polynomial (ULift.{u} ℤ))))
    (hf : f ≫ PolynomialLaurent.polynomialProjection (.of (ULift.{u} ℤ)) =
      PolynomialLaurent.laurentProjection (.of (ULift.{u} ℤ)))
    (hcoord : (projectiveSpaceAtUniverse 1).homOfLE h ≫ (integralChartPolynomialIso i).hom =
      integralOverlapLaurentIso.hom ≫ f) :
    ℓ ≫ (standardChartPolynomialIso X i).hom =
      (standardOverlapLaurentIso X).hom ≫
        (baseProductTransformation _ _ f hf).app X.obj := by
  rw [← hℓ, standardChartPolynomialIso_eq]
  let e := (chartOverlapIsoStandardOverlapOpen X.obj).hom
  let k := (projectiveSpaceOver 1 X.obj).homOfLE
    ((projectiveSpaceOver.toIntegralAtUniverse 1 X.obj).preimage_mono h)
  let a := (standardOpenIntegralPullbackIso X.obj integralOverlap).hom
  let v := (standardOpenIntegralPullbackIso X.obj (integralChart i)).hom
  let p := (integralProductComparison X.obj integralOverlapLaurentIso
    (PolynomialLaurent.laurentProjection (.of (ULift.{u} ℤ)))).hom
  let q := (integralProductComparison X.obj (integralChartPolynomialIso i)
    (PolynomialLaurent.polynomialProjection (.of (ULift.{u} ℤ)))).hom
  let t := (baseProductTransformation _ _ f hf).app X.obj
  change (e ≫ k) ≫ (v ≫ q) = (e ≫ (a ≫ p)) ≫ t
  suffices he : k ≫ v ≫ q = a ≫ p ≫ t by
    exact (Category.assoc e k (v ≫ q)).trans
      ((congrArg (fun m => e ≫ m) he).trans
        (((Category.assoc e (a ≫ p) t).trans
          (congrArg (fun m => e ≫ m) (Category.assoc a p t))).symm))
  dsimp only [k, v]
  rw [standardOpenIntegralPullbackIso_hom_natural_assoc X.obj h]
  apply pullback.hom_ext
  · dsimp only [a, p, q, t]
    simp [baseProductTransformation, baseProductFunctor, integralProductComparison_fst]
  · dsimp only [a, p, q, t]
    simp [baseProductTransformation, baseProductFunctor, integralProductComparison_snd,
      integralProductComparison_snd_assoc, hcoord]

/-- The actual positive overlap map is the plus map of the relative Bass construction. -/
theorem overlapToPositive_polynomial (X : QuasiCompactSchemes.{u}) :
    overlapToPositive X.obj ≫ (standardChartPolynomialIso X 0).hom =
      (standardOverlapLaurentIso X).hom ≫ (Relative.plus.app X).hom := by
  exact standardOverlapLaurentIso_leg X 0 (integralOverlap_eq.trans_le inf_le_left)
    (overlapToPositive X.obj) (chartOverlapIsoStandardOverlapOpen_hom_positive X.obj)
    _ (laurentToPolynomial_projection _) integralOverlapToPositive_polynomial

/-- The actual negative overlap map is the minus map of the relative Bass construction. -/
theorem overlapToNegative_polynomial (X : QuasiCompactSchemes.{u}) :
    overlapToNegative X.obj ≫ (standardChartPolynomialIso X 1).hom =
      (standardOverlapLaurentIso X).hom ≫ (Relative.minus.app X).hom := by
  exact standardOverlapLaurentIso_leg X 1 (integralOverlap_eq.trans_le inf_le_right)
    (overlapToNegative X.obj) (chartOverlapIsoStandardOverlapOpen_hom_negative X.obj)
    _ (laurentMinus_projection _) integralOverlapToNegative_polynomial

end AlgebraicGeometry.Scheme.ProjectiveLine
