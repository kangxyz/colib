/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Presentation.Quadratic.IntegralEtalePositivePreimage
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.AffineGroundPresentation
public import Colib.AlgebraicGeometry.Limits.EtalePolynomialCoordinate

/-! # Preimages on the actual polynomial étale neighborhood

The integral positive-dimensional step supplies preimages on the original
polynomial étale neighborhood. `PolynomialTailSimultaneousInduction` uses
this result in its successor step.
-/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
universe u
namespace QuadraticIncidence.InfinityChart
local instance {K : Type u} [Field K] : IsAffine (base (Spec (.of K))).left :=
  inferInstanceAs (IsAffine (Spec (.of K)))

theorem exists_actual_polynomial_neighborhood_preimage
    (K E Ω : Type u) [Field K] [Field E] [Field Ω] [IsAlgClosed Ω]
    [Algebra K E] [Module.Finite K E] [Algebra.IsSeparable K E]
    (d : ℕ)
    (ξ : Spec (.of Ω) ⟶ Spec (.of (MvPolynomial (Fin (d + 1)) E)))
    (hs : letI := (fieldToResidue
      (Spec.map (CommRingCat.ofHom (algebraMap E (MvPolynomial (Fin (d + 1)) E))))
      (ξ (IsLocalRing.closedPoint Ω))).hom.toAlgebra
      Algebra.IsSeparable E ((Spec (.of (MvPolynomial (Fin (d + 1)) E))).residueField
        (ξ (IsLocalRing.closedPoint Ω))))
    (P : PresheafWithTransfers.{u + 1} K) (hP : PresheafWithTransfers.IsA1Invariant P)
    (n : ℕ)
    (hn : ∀ (V : SmoothSite (Spec (.of K)))
      (z : PresheafWithTransfers.sections P ((Cor.graphFunctor K).obj V)), (n + 1) • z = 0)
    (hnK : IsUnit ((n + 1 : ℕ) : K))
    (hLower : PolynomialTailIsomorphisms K Ω ((PresheafWithTransfers.toPresheaf K).obj P) d)
    (A : EtaleNeighborhood (SmoothSite.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin (d + 1)) E))))) ξ)
    (b : ((PresheafWithTransfers.toPresheaf K).obj P).obj
      (op ((etaleNeighborhoodToSmooth (SmoothSite.mk (Spec.map (CommRingCat.ofHom
        (algebraMap K (MvPolynomial (Fin (d + 1)) E))))) ξ).obj A))) :
    let X := SmoothSite.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin (d + 1)) E))))
    let U := (etaleNeighborhoodToSmooth X ξ).obj A
    let : IsAffine U.left := inferInstanceAs (IsAffine (Spec A.obj.left.unop))
    let η := etaleNeighborhoodMark X ξ A
    let Q := (PresheafWithTransfers.toPresheaf K).obj P
    ∃ z : etaleNeighborhoodValue (base (Spec (.of K))) (η ≫ U.hom) Q,
      etaleNeighborhoodValuePullback
        (homMk U.hom (by change U.hom ≫ 𝟙 _ = U.hom; simp) :
          U ⟶ base (Spec (.of K))) (ξ := η) rfl Q z =
        toEtaleNeighborhoodValueFromObject U η Q b := by
  let X := SmoothSite.mk (Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin (d + 1)) E))))
  let U := (etaleNeighborhoodToSmooth X ξ).obj A
  let : IsAffine U.left := inferInstanceAs (IsAffine (Spec A.obj.left.unop))
  let η := etaleNeighborhoodMark X ξ A
  let B := A.obj.left.unop
  let f : Spec B ⟶ Spec (.of (MvPolynomial (Fin (d + 1)) E)) := A.obj.hom
  let : Etale f := A.obj.prop
  obtain ⟨a, q, hsm, hq, hspec, hsep⟩ :=
    exists_etale_polynomial_coordinate_separable_mark E B Ω (d + 1) f η ξ
      (etaleNeighborhoodMark_hom X ξ A) hs
  let := a
  let : Algebra.Smooth E B := hsm
  let : Algebra K B := ((algebraMap E B).comp (algebraMap K E)).toAlgebra
  let : IsScalarTower K E B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  let : Algebra.FinitePresentation K E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Smooth K E := {}
  let : Algebra.Smooth K B := Algebra.Smooth.comp K E B
  let i : Spec (.of B) ≅ U.left := Iso.refl _
  have hi : i.hom ≫ U.hom = Spec.map (CommRingCat.ofHom (algebraMap K B)) := by
    change 𝟙 _ ≫ (f ≫ Spec.map (CommRingCat.ofHom
      (algebraMap K (MvPolynomial (Fin (d + 1)) E)))) = _
    rw [Category.id_comp, ← hspec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext k
    change q (algebraMap E (MvPolynomial (Fin (d + 1)) E) (algebraMap K E k)) = _
    rw [q.commutes]
    rfl
  let j := affineGroundPresentationIso K B U i hi
  let Q := (PresheafWithTransfers.toPresheaf K).obj P
  let g : U ⟶ base (Spec (.of K)) := homMk U.hom (by change U.hom ≫ 𝟙 _ = U.hom; simp)
  let c : originalAffineTargetSite K B ⟶ base (Spec (.of K)) :=
    homMk (originalAffineTargetSite K B).hom (by exact Category.comp_id _)
  let : IsAffine (originalAffineTargetSite K B).left :=
    inferInstanceAs (IsAffine (Spec (.of B)))
  have hcomponent := exists_etale_coordinate_original_preimage_of_polynomial_tail_iso
    K E B Ω d q hq η hsep P hP n hn hnK hLower (Q.map j.hom.op b)
  exact exists_original_preimage_of_etale_chart_preimage_at_own_base j.hom g c
    (by apply MorphismProperty.Over.Hom.ext; exact hi) η η
    (by change η ≫ 𝟙 _ = η; simp) Q b hcomponent

end QuadraticIncidence.InfinityChart
