/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FaceSquare
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Integral supports of the native diagonal one-simplex

The coordinate algebra is the original support's global sections with the
polynomial action induced by the actual source projection. Normalization
uses its own fraction field, and characteristic zero gives finiteness over
the same polynomial base. The forward Laurent units are pulled back from
the original ordered torus coordinates.

Adapted from Motivic `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Cohomology/Diagonal/BoundarySupport.lean:25-131`,
`Normalization/FiniteCurve/Basic.lean:37-157` and
`RelativeCurve/MilnorK/NormalizedAffineEndpointNorm.lean:23-54` under
`Motivic/Aglib/AlgebraicGeometry`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open scoped Polynomial nonZeroDivisors

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalBoundarySupport

open _root_.AlgebraicGeometry.Scheme DiagonalFiniteCyclePushforward

section Faces

variable (k : Type u) [Field k]

theorem sourceChart0_hom : (sourceChart0 k).hom = (source k 0).hom := by
  have h : (simplexChart0 k).hom = AlgebraicSimplex.structureMap k 0 := by
    change Spec.map _ = Spec.map _
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (zeroCoordinateEquiv k).symm.commutes
  change sourceSimplexProjection k 0 ≫ (simplexChart0 k).hom =
    pullback.fst (SmoothSite.base (Spec (.of k))).hom (AlgebraicSimplex.structureMap k 0) ≫
      (SmoothSite.base (Spec (.of k))).hom
  rw [h]
  exact (pullback.condition (f := (SmoothSite.base (Spec (.of k))).hom)
    (g := AlgebraicSimplex.structureMap k 0)).symm

/-- The point identifies with the original product zero simplex via its chart. -/
def pointToZero : SmoothSite.base (Spec (.of k)) ⟶ source k 0 :=
  SmoothSite.homMk (sourceChart0 k).inv (by
    change (sourceChart0 k).inv ≫ (source k 0).hom = 𝟙 (Spec (.of k))
    rw [← sourceChart0_hom, Iso.inv_hom_id])

theorem pointToZero_comp_productFst :
    pointToZero k ≫ SmoothSite.productFst (SmoothSite.base (Spec (.of k)))
      (AlgebraicSimplex.smoothSiteObj k 0) = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  change (sourceChart0 k).inv ≫ pullback.fst (𝟙 (Spec (.of k)))
    (AlgebraicSimplex.structureMap k 0) = 𝟙 _
  rw [← show (source k 0).hom = pullback.fst (𝟙 (Spec (.of k)))
      (AlgebraicSimplex.structureMap k 0) from Category.comp_id _,
    ← sourceChart0_hom, Iso.inv_hom_id]

theorem productFst_comp_pointToZero :
    SmoothSite.productFst (SmoothSite.base (Spec (.of k))) (AlgebraicSimplex.smoothSiteObj k 0) ≫
      pointToZero k = 𝟙 _ := by
  apply MorphismProperty.Over.Hom.ext
  change pullback.fst (𝟙 (Spec (.of k))) (AlgebraicSimplex.structureMap k 0) ≫
    (sourceChart0 k).inv = 𝟙 _
  rw [← show (source k 0).hom = pullback.fst (𝟙 (Spec (.of k)))
      (AlgebraicSimplex.structureMap k 0) from Category.comp_id _,
    ← sourceChart0_hom, Iso.hom_inv_id]

/-- The polynomial line's original scalar projection. -/
abbrev polynomialToField : Spec (.of k[X]) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))

theorem sourceChart1_polynomialToField :
    (sourceChart1 k).hom ≫ polynomialToField k = (source k 1).hom := by
  have h : (simplexChart1 k).hom ≫ polynomialToField k = AlgebraicSimplex.structureMap k 1 := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact RingHom.ext (oneCoordinateEquiv k).symm.commutes
  change (sourceSimplexProjection k 1 ≫ (simplexChart1 k).hom) ≫ polynomialToField k =
    pullback.fst (SmoothSite.base (Spec (.of k))).hom (AlgebraicSimplex.structureMap k 1) ≫
      (SmoothSite.base (Spec (.of k))).hom
  rw [Category.assoc, h]
  exact (pullback.condition (f := (SmoothSite.base (Spec (.of k))).hom)
    (g := AlgebraicSimplex.structureMap k 1)).symm

private theorem endpoint_polynomialToField (a : k) :
    PolynomialEndpointFiber.endpoint a ≫ polynomialToField k = 𝟙 _ := by
  have he : CommRingCat.ofHom (Polynomial.C : k →+* k[X]) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom a) = 𝟙 (CommRingCat.of k) := by
    ext b
    simp
  rw [PolynomialEndpointFiber.endpoint, polynomialToField, ← Spec.map_comp, he, Spec.map_id]

/-- The original affine evaluation point in the actual product simplex source. -/
def evaluationPoint (a : k) : SmoothSite.base (Spec (.of k)) ⟶ source k 1 :=
  SmoothSite.homMk (PolynomialEndpointFiber.endpoint a ≫ (sourceChart1 k).inv) (by
    change (PolynomialEndpointFiber.endpoint a ≫ (sourceChart1 k).inv) ≫ (source k 1).hom =
      𝟙 (Spec (.of k))
    rw [Category.assoc, ← sourceChart1_polynomialToField, Iso.inv_hom_id_assoc,
      endpoint_polynomialToField])

@[reassoc] theorem evaluationPoint_chart (a : k) :
    (evaluationPoint k a).left ≫ (sourceChart1 k).hom = PolynomialEndpointFiber.endpoint a := by
  change (PolynomialEndpointFiber.endpoint a ≫ (sourceChart1 k).inv) ≫ (sourceChart1 k).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem evaluationPoint_face (i : Fin 2) :
    evaluationPoint k (i.val : k) = pointToZero k ≫ sourceFace k i := by
  apply MorphismProperty.Over.Hom.ext
  change (evaluationPoint k (i.val : k)).left = (sourceChart0 k).inv ≫ (sourceFace k i).left
  apply (cancel_mono (sourceChart1 k).hom).mp
  rw [evaluationPoint_chart, Category.assoc, sourceFace_chart, Iso.inv_hom_id_assoc]

end Faces

/-- An admissible native prime in the actual diagonal one-simplex ambient. -/
abbrev Generator (k : Type u) [Field k] (q : ℕ) :=
  {z : ambient k 1 q // IsFiniteCorrespondencePoint (source k 1).hom (target k q).hom z}

variable {k : Type u} [Field k] {q : ℕ} (Z : Generator k q)

/-- The original integral closed support of the prime. -/
abbrev support : Scheme.{u} := (integralComponentAt Z.val).subscheme

instance supportIntegral : IsIntegral (support Z) := isIntegral_integralComponentAt Z.val

/-- The original support inclusion in the one-simplex-times-torus product. -/
abbrev inclusion : support Z ⟶ ambient k 1 q := (integralComponentAt Z.val).subschemeι

/-- The actual finite projection to the one-simplex source. -/
abbrev projection : support Z ⟶ (source k 1).left :=
  inclusion Z ≫ pullback.fst (source k 1).hom (target k q).hom

instance projectionFinite : IsFinite (projection Z) := Z.property.1

instance projectionSurjective : Surjective (projection Z) := by
  have h : Set.range (projection Z) ∈ irreducibleComponents (source k 1).left := Z.property.2
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at h
  exact ⟨Set.range_eq_univ.mp h⟩

/-- The source projection read in the actual polynomial chart. -/
abbrev polynomialProjection : support Z ⟶ Spec (.of k[X]) :=
  projection Z ≫ (sourceChart1 k).hom

instance polynomialProjectionFinite : IsFinite (polynomialProjection Z) := inferInstance

instance polynomialProjectionSurjective : Surjective (polynomialProjection Z) := inferInstance

instance supportAffine : IsAffine (support Z) := isAffine_of_isAffineHom (polynomialProjection Z)

/-- The original projection to the ordered torus. -/
abbrev targetProjection : support Z ⟶ (target k q).left :=
  inclusion Z ≫ pullback.snd (source k 1).hom (target k q).hom

/-- The literal global functions on the original support. -/
abbrev coordinateRing : CommRingCat.{u} := Γ(support Z, ⊤)

/-- The chosen affine chart is the canonical global-section chart. -/
def supportIsoSpec : support Z ≅ Spec (coordinateRing Z) := (support Z).isoSpec

/-- The actual polynomial scalar map, defined by the original source projection. -/
def scalarMap : k[X] →+* coordinateRing Z :=
  (polynomialProjection Z).appTop.hom.comp (Scheme.ΓSpecIso (.of k[X])).inv.hom

instance coordinateAlgebra : Algebra k[X] (coordinateRing Z) := (scalarMap Z).toAlgebra

instance coordinateFinite : Module.Finite k[X] (coordinateRing Z) := by
  change (scalarMap Z).Finite
  exact (polynomialProjection Z).finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k[X])).symm.commRingCatIsoToRingEquiv.surjective)

theorem scalarMap_injective : Function.Injective (scalarMap Z) := by
  let : IsSchemeTheoreticallyDominant (polynomialProjection Z) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have happ : Function.Injective (polynomialProjection Z).appTop.hom :=
    (polynomialProjection Z).app_injective ⊤
  exact happ.comp (Scheme.ΓSpecIso (.of k[X])).symm.commRingCatIsoToRingEquiv.injective

instance coordinateFaithful : FaithfulSMul k[X] (coordinateRing Z) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (scalarMap_injective Z)

instance coordinateTorsionFree : Module.IsTorsionFree k[X] (coordinateRing Z) :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr (scalarMap_injective Z)

/-- The same polynomial map in the canonical affine support chart. -/
abbrev affineBaseMap : Spec (coordinateRing Z) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (coordinateRing Z)))

@[reassoc] theorem supportIsoSpec_inv_polynomialProjection :
    (supportIsoSpec Z).inv ≫ polynomialProjection Z = affineBaseMap Z := by
  change (support Z).isoSpec.inv ≫ polynomialProjection Z = _
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

instance polynomialProjectionFlat : Flat (polynomialProjection Z) := by
  let : Module.Free k[X] (coordinateRing Z) := Module.free_of_finite_type_torsion_free'
  have : Flat (affineBaseMap Z) := Flat.SpecMap_iff.mpr (by
    change Module.Flat k[X] (coordinateRing Z)
    infer_instance)
  have h : polynomialProjection Z = (supportIsoSpec Z).hom ≫ affineBaseMap Z := by
    rw [← supportIsoSpec_inv_polynomialProjection, Iso.hom_inv_id_assoc]
  rw [h]
  infer_instance

instance projectionFlat : Flat (projection Z) := by
  have h : projection Z = polynomialProjection Z ≫ (sourceChart1 k).inv := by
    simp only [polynomialProjection, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

/-- The forward Laurent coordinate, restricted along the original torus projection. -/
def coordinateUnit (i : Fin q) : (coordinateRing Z)ˣ :=
  Units.map ((targetProjection Z ≫
    (SmoothSite.torusCoordinate (Spec (.of k)) q i).left).appTop).hom.toMonoidHom
      (multiplicativeGroupBaseChangeCoordinate (Spec (.of k)))

/-- The normalization is taken in the original support's fraction field. -/
abbrev normalizationRing : Type u :=
  integralClosure (coordinateRing Z) (FractionRing (coordinateRing Z))

instance normalizationFractionRing :
    IsFractionRing (normalizationRing Z) (FractionRing (coordinateRing Z)) :=
  integralClosure.isFractionRing_of_finite_extension
    (FractionRing (coordinateRing Z)) (FractionRing (coordinateRing Z))

theorem fractionPolynomialScalar_injective :
    Function.Injective (algebraMap k[X] (FractionRing (coordinateRing Z))) := by
  rw [IsScalarTower.algebraMap_eq k[X] (coordinateRing Z) (FractionRing (coordinateRing Z))]
  exact (IsFractionRing.injective (coordinateRing Z) _).comp (scalarMap_injective Z)

/-- The rational parameter extends the original polynomial scalar map. -/
instance fractionRatFuncAlgebra : Algebra (RatFunc k) (FractionRing (coordinateRing Z)) :=
  (IsFractionRing.lift (K := RatFunc k) (fractionPolynomialScalar_injective Z)).toAlgebra

instance fractionRatFuncTower :
    IsScalarTower k[X] (RatFunc k) (FractionRing (coordinateRing Z)) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (IsFractionRing.lift_algebraMap (K := RatFunc k)
    (fractionPolynomialScalar_injective Z) a).symm

instance fractionRatFuncFinite : FiniteDimensional (RatFunc k) (FractionRing (coordinateRing Z)) :=
  Module.Finite.of_isLocalization k[X] (coordinateRing Z) (nonZeroDivisors k[X])

theorem normalization_isIntegralClosure_base :
    IsIntegralClosure (normalizationRing Z) k[X] (FractionRing (coordinateRing Z)) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, hx.tower_top⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact isIntegral_trans (A := coordinateRing Z) _ x.property

instance normalizationTorsionFree : Module.IsTorsionFree k[X] (normalizationRing Z) := by
  apply Module.isTorsionFree_iff_algebraMap_injective.mpr
  intro a b h
  apply fractionPolynomialScalar_injective Z
  rw [IsScalarTower.algebraMap_apply k[X] (normalizationRing Z) (FractionRing (coordinateRing Z)),
    IsScalarTower.algebraMap_apply k[X] (normalizationRing Z) (FractionRing (coordinateRing Z)), h]

instance normalizationFiniteBase [CharZero k] : Module.Finite k[X] (normalizationRing Z) := by
  let : IsIntegralClosure (normalizationRing Z) k[X] (FractionRing (coordinateRing Z)) :=
    normalization_isIntegralClosure_base Z
  exact IsIntegralClosure.finite k[X] (RatFunc k) (FractionRing (coordinateRing Z)) _

instance normalizationDedekind [CharZero k] : IsDedekindDomain (normalizationRing Z) := by
  let : IsIntegralClosure (normalizationRing Z) k[X] (FractionRing (coordinateRing Z)) :=
    normalization_isIntegralClosure_base Z
  exact IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) (FractionRing (coordinateRing Z)) _

instance normalizationFiniteSupport [CharZero k] :
    Module.Finite (coordinateRing Z) (normalizationRing Z) :=
  Module.Finite.of_restrictScalars_finite k[X] (coordinateRing Z) (normalizationRing Z)

/-- The map of spectra given by the original ring's inclusion into its normalization. -/
abbrev normalizationSpecMap : Spec (.of (normalizationRing Z)) ⟶ Spec (coordinateRing Z) :=
  Spec.map (CommRingCat.ofHom (algebraMap (coordinateRing Z) (normalizationRing Z)))

/-- The normalization map into the original support scheme. -/
def normalizationMap : Spec (.of (normalizationRing Z)) ⟶ support Z :=
  normalizationSpecMap Z ≫ (supportIsoSpec Z).inv

instance normalizationSpecMapSurjective : Surjective (normalizationSpecMap Z) := by
  let : FaithfulSMul (coordinateRing Z) (normalizationRing Z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (fun _ _ h =>
      IsFractionRing.injective (coordinateRing Z) (FractionRing (coordinateRing Z))
        (congrArg Subtype.val h))
  exact ⟨Algebra.IsIntegral.comap_surjective (coordinateRing Z) (normalizationRing Z)⟩

instance normalizationMapSurjective : Surjective (normalizationMap Z) :=
  inferInstanceAs (Surjective (normalizationSpecMap Z ≫ (supportIsoSpec Z).inv))

instance normalizationSpecMapFinite [CharZero k] : IsFinite (normalizationSpecMap Z) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance normalizationMapFinite [CharZero k] : IsFinite (normalizationMap Z) :=
  inferInstanceAs (IsFinite (normalizationSpecMap Z ≫ (supportIsoSpec Z).inv))

/-- The normalization retains the same polynomial parameter. -/
abbrev normalizationBaseMap : Spec (.of (normalizationRing Z)) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (algebraMap k[X] (normalizationRing Z)))

instance normalizationBaseMapFinite [CharZero k] : IsFinite (normalizationBaseMap Z) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance normalizationBaseMapFlat [CharZero k] : Flat (normalizationBaseMap Z) := by
  let : Module.Free k[X] (normalizationRing Z) := Module.free_of_finite_type_torsion_free'
  exact Flat.SpecMap_iff.mpr (by
    change (algebraMap k[X] (normalizationRing Z)).Flat
    exact RingHom.flat_algebraMap_iff.mpr inferInstance)

@[reassoc] theorem normalizationMap_polynomialProjection :
    normalizationMap Z ≫ polynomialProjection Z = normalizationBaseMap Z := by
  rw [normalizationMap, Category.assoc, supportIsoSpec_inv_polynomialProjection]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1

/-- The original coordinate units transported to the normalization ring. -/
def normalizedCoordinateUnit (i : Fin q) : (normalizationRing Z)ˣ :=
  Units.map (algebraMap (coordinateRing Z) (normalizationRing Z)).toMonoidHom (coordinateUnit Z i)

end AlgebraicGeometry.MotivicCohomology.DiagonalBoundarySupport
