/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveLine.DerivedCechTriangle
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineProjModel
public import StacksFrontier.AlgebraicGeometry.ProjTwistChain.MY
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Local
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.CechComparison.OverlapRing

/-! # The standard overlap of the projective line over its coefficient ring

The intersection of the two native standard charts is identified over the base
with the spectrum of the Laurent polynomial ring. The isomorphism is obtained
from the actual open immersion onto the standard open (D_+(X_0 X_1)).
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open Stacks.ProjectiveSpace.CechComparison
open MvPolynomial

universe u

namespace AlgebraicGeometry.projectiveSpaceOver

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] projectiveSpaceAtUniverse

variable (R : CommRingCat.{u})

private theorem polynomialComparison_preimage_chart (i : Fin 2) :
    (polynomialComparison R 1).iso.inv ⁻¹ᵁ standardChart 1 (Spec R) i =
      Proj.basicOpen (polyGrading R 1) (X i) := by
  unfold standardChart
  let e := polynomialComparison R 1
  let U : (projectiveSpaceAtUniverse.{u} 1).Opens :=
    Proj.basicOpen (Stacks.SectionsToProjectiveSpace.coordGrading.{u} 1) (X i)
  change e.iso.inv ⁻¹ᵁ (toIntegralAtUniverse 1 (Spec R) ⁻¹ᵁ U) = _
  rw [← Scheme.Hom.comp_preimage e.iso.inv (toIntegralAtUniverse 1 (Spec R)) U]
  have he : e.iso.inv ≫ toIntegralAtUniverse 1 (Spec R) =
      coordinateProjMap R 1 e.coordinateMap e.domain_eq_top :=
    (congrArg (fun f ↦ e.iso.inv ≫ f) e.toIntegral.symm).trans
      (Iso.inv_hom_id_assoc _ _)
  rw [he]
  unfold coordinateProjMap
  rw [Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_preimage_basicOpen
      _ _ e.coordinateMap (X i) 1 (X_mem_one _ _ _) Nat.one_pos,
    ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage]
  have h : (Scheme.topIso _).inv ≫ (Scheme.isoOfEq _ e.domain_eq_top.symm).hom ≫
      (Stacks.AlgebraicGeometry.ProjShared.mapDomain _ _ e.coordinateMap).ι = 𝟙 _ := by
    exact Stacks.AlgebraicGeometry.RelativeProj.topIso_inv_isoOfEq_hom_ι
      _ _ e.coordinateMap e.domain_eq_top
  rw [Category.assoc, h, Scheme.Hom.id_preimage, e.coordinateMap_apply, MvPolynomial.map_X]

private def standardOverlapMap :
    Spec (.of (LaurentPolynomial R)) ⟶ line R :=
  Spec.map (CommRingCat.ofHom (overlapAlgEquivLaurent R).toRingHom) ≫
    Proj.awayι (polyGrading R 1) (projectiveLineProjOverlapElem R)
      (projectiveLineProjOverlapElem_mem R) two_pos ≫ (polynomialComparison R 1).iso.inv

private instance : IsOpenImmersion (standardOverlapMap R) := by
  unfold standardOverlapMap
  let : IsIso (CommRingCat.ofHom (overlapAlgEquivLaurent R).toRingHom) :=
    (overlapAlgEquivLaurent R).toRingEquiv.toCommRingCatIso.isIso_hom
  infer_instance

private theorem standardOverlapMap_opensRange :
    (standardOverlapMap R).opensRange = lineChartZero R ⊓ lineChartOne R := by
  let e := polynomialComparison R 1
  let U := lineChartZero R ⊓ lineChartOne R
  have hpre : e.iso.inv ⁻¹ᵁ U =
      Proj.basicOpen (polyGrading R 1) (projectiveLineProjOverlapElem R) := by
    change e.iso.inv ⁻¹ᵁ (standardChart 1 (Spec R) 0 ⊓ standardChart 1 (Spec R) 1) = _
    rw [Scheme.Hom.preimage_inf, polynomialComparison_preimage_chart R 0,
      polynomialComparison_preimage_chart R 1, projectiveLineProjOverlapElem, Proj.basicOpen_mul]
  let a := Spec.map (CommRingCat.ofHom (overlapAlgEquivLaurent R).toRingHom)
  let b := Proj.awayι (polyGrading R 1) (projectiveLineProjOverlapElem R)
    (projectiveLineProjOverlapElem_mem R) two_pos
  let : IsIso (CommRingCat.ofHom (overlapAlgEquivLaurent R).toRingHom) :=
    (overlapAlgEquivLaurent R).toRingEquiv.toCommRingCatIso.isIso_hom
  let : IsIso a := inferInstanceAs (IsIso (Spec.map _))
  have he : e.iso.inv ''ᵁ b.opensRange = U := by
    rw [show b.opensRange = _ from Proj.opensRange_awayι _ _ _ _,
      ← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Hom.opensRange_of_isIso, top_inf_eq]
  calc
    (standardOverlapMap R).opensRange = ((a ≫ b) ≫ e.iso.inv).opensRange :=
      TopologicalSpace.Opens.ext (by
        change Set.range (standardOverlapMap R) = Set.range ((a ≫ b) ≫ e.iso.inv)
        exact congrArg (fun f : Spec (.of (LaurentPolynomial R)) ⟶ line R ↦
          Set.range f) (Category.assoc _ _ _).symm)
    _ = e.iso.inv ''ᵁ (a ≫ b).opensRange := Scheme.Hom.opensRange_comp _ _
    _ = _ := by rw [Scheme.Hom.opensRange_comp_of_isIso, he]

/-- The intersection of the two standard charts is the punctured affine line. -/
def standardOverlapLaurentIso :
    Spec (.of (LaurentPolynomial R)) ≅ (lineChartZero R ⊓ lineChartOne R).toScheme :=
  IsOpenImmersion.isoOfRangeEq (standardOverlapMap R) (lineChartZero R ⊓ lineChartOne R).ι
    (congrArg SetLike.coe
      ((standardOverlapMap_opensRange R).trans (Scheme.Opens.opensRange_ι _).symm))

private theorem standardOverlapMap_over :
    standardOverlapMap R ≫ lineProjection R =
      Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R))) := by
  let e := polynomialComparison R 1
  have hbase : e.iso.inv ≫ lineProjection R = projToSpecCoeff R 1 := by
    change e.iso.inv ≫ pullback.fst _ _ = _
    rw [← e.toBase, Iso.inv_hom_id_assoc]
    rfl
  unfold standardOverlapMap
  rw [Category.assoc, Category.assoc]
  change _ ≫ _ ≫ e.iso.inv ≫ lineProjection R = _
  rw [hbase, projToSpecCoeff, Proj.awayι_toSpecZero_assoc,
    Spec_map_ofHom_comp_Spec_map_ofHom, Spec_map_ofHom_comp_Spec_map_ofHom]
  congr 2
  apply RingHom.ext
  intro r
  change overlapAlgEquivLaurent R
    (HomogeneousLocalization.fromZeroRingHom (polyGrading R 1)
      (Submonoid.powers (projectiveLineProjOverlapElem R))
      (GradedRing.projZeroRingHom' (polyGrading R 1) (MvPolynomial.C r))) =
    algebraMap R (LaurentPolynomial R) r
  rw [← (overlapAlgEquivLaurent R).commutes]
  congr 1
  change HomogeneousLocalization.fromZeroRingHom (polyGrading R 1)
      (Submonoid.powers (projectiveLineProjOverlapElem R))
      (GradedRing.projZeroRingHom' (polyGrading R 1) (MvPolynomial.C r)) =
    HomogeneousLocalization.fromZeroRingHom (polyGrading R 1)
      (Submonoid.powers (projectiveLineProjOverlapElem R))
      (algebraMap R ((polyGrading R 1) 0) r)
  congr 1
  apply Subtype.ext
  rw [GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply]
  change (DirectSum.decompose (polyGrading R 1) (MvPolynomial.C r) 0).1 = MvPolynomial.C r
  have hm : MvPolynomial.C r ∈ polyGrading R 1 0 := by
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).2 (MvPolynomial.isHomogeneous_C _ _)
  exact DirectSum.decompose_of_mem_same _ hm

/-- The overlap isomorphism identifies the actual morphism to the base with the coefficient map. -/
theorem standardOverlapLaurentIso_over :
    (standardOverlapLaurentIso R).hom ≫
      (lineChartZero R ⊓ lineChartOne R).ι ≫ lineProjection R =
      Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R))) := by
  rw [← Category.assoc]
  have h : (standardOverlapLaurentIso R).hom ≫
      (lineChartZero R ⊓ lineChartOne R).ι = standardOverlapMap R :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  rw [h, standardOverlapMap_over]

end AlgebraicGeometry.projectiveSpaceOver
