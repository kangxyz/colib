/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Limits.FiniteSubfieldClopen
public import Colib.AlgebraicGeometry.Limits.FiniteSubfieldRationalMarking
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.Basic
public import Colib.AlgebraicGeometry.Sites.Smooth.NormalComponents
public import Colib.RingTheory.Etale.ScalarExtensionTrdeg
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Field

/-!
# Integral marked charts at actual finite subfields

The component through an original rational tensor point is an integral clopen open.
Its actual idempotent descends to a finite separable intermediate field. The canonical
localization comparison preserves the original point and the transcendence degree of
an actual etale polynomial chart. No dimension hypothesis is an input.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open CategoryTheory IntermediateField

universe u

namespace AlgebraicGeometry.Scheme

/-- The native subalgebra scalar structure fixes the intermediate-field scalar diamond. -/
local instance integralChartSubfieldAlgebra (E L : Type u) [Field E] [Field L] [Algebra E L]
    (t : Finset L) : Algebra E (adjoin E (t : Set L)) := (adjoin E (t : Set L)).toSubalgebra.algebra

/-- The actual localization and second tensor projection give the finite-stage chart map. -/
def finsetLocalizationToBase
    (E L B : Type u) [Field E] [Field L] [Algebra E L] [CommRing B] [Algebra E B]
    (t : Finset L) (e : (adjoin E (t : Set L)) ⊗[E] B) :
    Spec (.of (Localization.Away e)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (algebraMap ((adjoin E (t : Set L)) ⊗[E] B) (Localization.Away e))) ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := E) (A := adjoin E (t : Set L))
        (B := B)).toRingHom)

/-- The finite-stage chart retains its actual intermediate-field structure morphism. -/
def finsetLocalizationToField
    (E L B : Type u) [Field E] [Field L] [Algebra E L] [CommRing B] [Algebra E B]
    (t : Finset L) (e : (adjoin E (t : Set L)) ⊗[E] B) :
    Spec (.of (Localization.Away e)) ⟶ Spec (.of (adjoin E (t : Set L))) :=
  Spec.map (CommRingCat.ofHom (algebraMap (adjoin E (t : Set L)) (Localization.Away e)))

private theorem finsetTensorLocalizationMap_square
    (E L B : Type u) [Field E] [Field L] [Algebra E L] [CommRing B] [Algebra E B]
    (t : Finset L) (e : (adjoin E (t : Set L)) ⊗[E] B) :
    Spec.map (CommRingCat.ofHom (finsetTensorLocalizationMap E L B t e).toRingHom) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap ((adjoin E (t : Set L)) ⊗[E] B) (Localization.Away e))) =
    Spec.map (CommRingCat.ofHom
      (algebraMap (L ⊗[E] B) (Localization.Away (finsetTensorInclusion E L B t e)))) ≫
      Spec.map (CommRingCat.ofHom (finsetTensorInclusion E L B t).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change finsetTensorLocalizationMap E L B t e (algebraMap _ _ x) =
    algebraMap _ _ (finsetTensorInclusion E L B t x)
  simp [finsetTensorLocalizationMap, IsLocalization.Away.map]

/-- The original finite-stage chart is etale over the original affine scheme. -/
theorem etale_finsetLocalizationToBase
    (E L B : Type u) [Field E] [Field L] [Algebra E L] [Algebra.IsSeparable E L]
    [CommRing B] [Algebra E B] (t : Finset L)
    (e : (adjoin E (t : Set L)) ⊗[E] B) :
    AlgebraicGeometry.Etale (finsetLocalizationToBase E L B t e) := by
  have : Module.Finite E (adjoin E (t : Set L)) := finite_finsetAdjoinDiagram_obj E L t
  have : Algebra.Etale E (adjoin E (t : Set L)) :=
    ⟨Algebra.FormallyEtale.of_isSeparable _ _,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  have ht : (Algebra.TensorProduct.includeRight (R := E)
      (A := adjoin E (t : Set L)) (B := B)).toRingHom.Etale := by
    have h := RingHom.Etale.respectsIso.1 _
      (Algebra.TensorProduct.comm E B (adjoin E (t : Set L))).toRingEquiv
      (RingHom.etale_algebraMap.mpr
        (Algebra.Etale.baseChange E (adjoin E (t : Set L)) B))
    convert h using 1
    ext b
    simp
  have : AlgebraicGeometry.Etale (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := E)
        (A := adjoin E (t : Set L)) (B := B)).toRingHom)) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr ht
  have : AlgebraicGeometry.Etale (Spec.map
      (CommRingCat.ofHom (algebraMap ((adjoin E (t : Set L)) ⊗[E] B) (Localization.Away e)))) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
      (RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway e))
  unfold finsetLocalizationToBase
  infer_instance

private theorem finsetLocalizationToField_eq_of_square
    (E L B : Type u) [Field E] [Field L] [Algebra E L]
    [CommRing B] [Algebra E B] (t : Finset L)
    (e : (adjoin E (t : Set L)) ⊗[E] B)
    (xL : Spec (.of L) ⟶ Spec (.of (L ⊗[E] B)))
    (x₁ : Spec (.of L) ⟶ Spec (.of (Localization.Away e)))
    (hproj : x₁ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ((adjoin E (t : Set L)) ⊗[E] B) (Localization.Away e))) =
      xL ≫ Spec.map (CommRingCat.ofHom (finsetTensorInclusion E L B t).toRingHom))
    (hxL : xL ≫ Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[E] B))) = 𝟙 _) :
    x₁ ≫ finsetLocalizationToField E L B t e =
      Spec.map (CommRingCat.ofHom (adjoin E (t : Set L)).val.toRingHom) := by
  rw [finsetLocalizationToField, IsScalarTower.algebraMap_eq
    (adjoin E (t : Set L)) ((adjoin E (t : Set L)) ⊗[E] B) (Localization.Away e),
    CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, hproj,
    Category.assoc, finsetTensorInclusion, tensorSpec_map_fst, ← Category.assoc,
    hxL, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
/-- A marked etale polynomial chart has an actual finite separable integral component model.
The same canonical tensor-localization comparison gives a domain of transcendence degree
`n` over `L`. The original `L`-point, every further marking, and both structure maps are
retained as literal equalities of morphisms. -/
theorem exists_integral_marked_finsetSubfieldModel
    (E L B : Type u) [Field E] [Field L] [Algebra E L] [Algebra.IsSeparable E L]
    [CommRing B] [Algebra E B] [Algebra.Smooth E B] {n : ℕ}
    (q : MvPolynomial (Fin n) E →ₐ[E] B) (hq : q.toRingHom.Etale)
    (x : Spec (.of L) ⟶ Spec (.of B))
    (hx : x ≫ Spec.map (CommRingCat.ofHom (algebraMap E B)) =
      Spec.map (CommRingCat.ofHom (algebraMap E L)))
    {Y : Scheme.{u}} (η : Y ⟶ Spec (.of L)) (s : Finset L) :
    ∃ t : Finset L, s ⊆ t ∧ Module.Finite E (adjoin E (t : Set L)) ∧
      ∃ e : (adjoin E (t : Set L)) ⊗[E] B, IsIdempotentElem e ∧
        IsDomain (Localization.Away e) ∧
        IsDomain (L ⊗[adjoin E (t : Set L)] Localization.Away e) ∧
        Algebra.trdeg L (L ⊗[adjoin E (t : Set L)] Localization.Away e) = n ∧
        AlgebraicGeometry.Etale (finsetLocalizationToBase E L B t e) ∧
        ∃ x₁ : Spec (.of L) ⟶ Spec (.of (Localization.Away e)),
          x₁ ≫ finsetLocalizationToBase E L B t e = x ∧
          x₁ ≫ finsetLocalizationToField E L B t e =
            Spec.map (CommRingCat.ofHom (adjoin E (t : Set L)).val.toRingHom) ∧
          (η ≫ x₁) ≫ finsetLocalizationToBase E L B t e = η ≫ x ∧
          ∃ U : (Spec (.of (L ⊗[E] B))).Opens,
            IsClopen (U : Set (Spec (.of (L ⊗[E] B)))) ∧ IsIntegral U.toScheme ∧
            (U : Set (Spec (.of (L ⊗[E] B)))) = irreducibleComponent
              (rationalTensorPoint E L B x hx (IsLocalRing.closedPoint L)) ∧
            ∃ (i : U.toScheme ≅
                Spec (.of (Localization.Away (finsetTensorInclusion E L B t e))))
              (z : Spec (.of L) ⟶ U.toScheme),
              i.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (L ⊗[E] B)
                (Localization.Away (finsetTensorInclusion E L B t e)))) = U.ι ∧
              z ≫ U.ι = rationalTensorPoint E L B x hx ∧
              x₁ = z ≫ i.hom ≫ Spec.map (CommRingCat.ofHom
                (finsetTensorLocalizationMap E L B t e).toRingHom) := by
  let xL := rationalTensorPoint E L B x hx
  have hsmooth : AlgebraicGeometry.Smooth
      (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[E] B)))) :=
    (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  have : IsNormal (Spec (.of (L ⊗[E] B))) :=
    isNormal_of_isRegular _ (isRegular_of_smooth_over_field
      (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[E] B)))))
  have : IsLocallyNoetherian (Spec (.of (L ⊗[E] B))) :=
    LocallyOfFiniteType.isLocallyNoetherian
      (Spec.map (CommRingCat.ofHom (algebraMap L (L ⊗[E] B))))
  let p := xL (IsLocalRing.closedPoint L)
  let U := normalComponentOpen p
  obtain ⟨t, ht, hfin, e, he, hdom, i, hi⟩ :=
    exists_integral_clopen_finsetSubfieldModel E L B s U (isClopen_normalComponentOpen p)
  have : IsIntegral (Spec (.of (Localization.Away (finsetTensorInclusion E L B t e)))) :=
    IsIntegral.of_isIso i.hom
  have : IsDomain (Localization.Away (finsetTensorInclusion E L B t e)) :=
    (affine_isIntegral_iff (.of (Localization.Away
      (finsetTensorInclusion E L B t e)))).mp inferInstance
  let c := Algebra.TensorProduct.cancelBaseChangeAway E (adjoin E (t : Set L)) L B e
  have hbase : IsDomain (L ⊗[adjoin E (t : Set L)] Localization.Away e) := by
    have : IsDomain (Localization.Away
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom E (adjoin E (t : Set L)) L)
          (AlgHom.id E B) e)) := by
      change IsDomain (Localization.Away (finsetTensorInclusion E L B t e))
      infer_instance
    exact Function.Injective.isDomain c.toRingHom c.injective
  have hdeg : Algebra.trdeg L (L ⊗[adjoin E (t : Set L)] Localization.Away e) = n := by
    have hc : Algebra.trdeg L (Localization.Away
        (finsetTensorInclusion E L B t e)) = n :=
      Algebra.trdeg_localized_tensor_of_etale_polynomial_map E L B q hq _
    exact c.trdeg_eq.trans hc
  let a := liftToNormalComponent xL p (mem_normalComponentOpen p)
  have ha : a ≫ U.ι = xL := liftToNormalComponent_ι xL p (mem_normalComponentOpen p)
  let b := a ≫ i.hom
  have hb : b ≫ Spec.map (CommRingCat.ofHom
      (algebraMap (L ⊗[E] B) (Localization.Away (finsetTensorInclusion E L B t e)))) = xL := by
    dsimp only [b]
    rw [Category.assoc, hi]
    exact liftToNormalComponent_ι _ _ _
  let x₁ := b ≫ Spec.map (CommRingCat.ofHom
    (finsetTensorLocalizationMap E L B t e).toRingHom)
  have hproj : x₁ ≫ Spec.map (CommRingCat.ofHom
      (algebraMap ((adjoin E (t : Set L)) ⊗[E] B) (Localization.Away e))) =
      xL ≫ Spec.map (CommRingCat.ofHom (finsetTensorInclusion E L B t).toRingHom) := by
    dsimp only [x₁]
    rw [Category.assoc, finsetTensorLocalizationMap_square, ← Category.assoc, hb]
  have hx₁ : x₁ ≫ finsetLocalizationToBase E L B t e = x := by
    rw [finsetLocalizationToBase, ← Category.assoc, hproj, Category.assoc]
    simp only [finsetTensorInclusion, tensorSpec_map_snd]
    exact rationalTensorPoint_snd E L B x hx
  refine ⟨t, ht, hfin, e, he, hdom, hbase, hdeg,
    etale_finsetLocalizationToBase E L B t e, x₁, hx₁, ?_, ?_, ?_⟩
  · exact finsetLocalizationToField_eq_of_square E L B t e xL x₁ hproj
      (rationalTensorPoint_fst E L B x hx)
  · rw [Category.assoc, hx₁]
  · refine ⟨U, isClopen_normalComponentOpen p, inferInstance, rfl, i, a, hi,
      ha, ?_⟩
    exact Category.assoc _ _ _

end AlgebraicGeometry.Scheme
