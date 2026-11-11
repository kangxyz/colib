/-
Copyright (c) 2026 Motivic Cohomology contributors and Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PointNorm
public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Chow.IntegralFundamental
public import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenTowerSeparable
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Transport

/-!
# Evaluation of an actual finite field point in the diagonal torus

The canonical integral component at the image point supplies its original support field.
The geometric pushforward coefficient is the degree over that field. Transitivity and
the restriction formula for the native Milnor norm evaluate the point in its full
original field, with its signed cycle coefficient.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin TopologicalSpace

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalFinitePointEvaluation

open _root_.AlgebraicGeometry.Scheme
open DiagonalPointNorm

/-- The actual ambient of a point-to-torus correspondence. -/
abbrev ambient (k : Type u) [Field k] (q : ℕ) : Scheme.{u} :=
  pullback (𝟙 (Spec (.of k))) (SmoothSite.torusPower (Spec (.of k)) q).hom

/-- The specified torus coordinate on the original ambient. -/
def ambientCoordinate (k : Type u) [Field k] (q : ℕ) (i : Fin q) :
    ambient k q ⟶ (SmoothSite.multiplicativeGroupObject (Spec (.of k))).left :=
  pullback.snd _ _ ≫ (SmoothSite.torusCoordinate (Spec (.of k)) q i).left

variable {k : Type u} [Field k] {q : ℕ}

/-- Each coordinate pulls back the native forward unit to global sections. -/
def schemeCoordinateUnit {T : Scheme.{u}} (j : T ⟶ ambient k q) (i : Fin q) : Γ(T, ⊤)ˣ :=
  Units.map ((j ≫ ambientCoordinate k q i).appTop).hom.toMonoidHom
    (multiplicativeGroupBaseChangeCoordinate (Spec (.of k)))

/-- Pullback along the actual source map preserves every ordered coordinate. -/
theorem schemeCoordinateUnit_comp {T U : Scheme.{u}} (f : T ⟶ U)
    (j : U ⟶ ambient k q) (i : Fin q) :
    schemeCoordinateUnit (f ≫ j) i =
      Units.map f.appTop.hom.toMonoidHom (schemeCoordinateUnit j i) := by
  apply Units.ext
  change (((f ≫ j) ≫ ambientCoordinate k q i).appTop)
    (multiplicativeGroupBaseChangeCoordinate (Spec (.of k))).val = _
  rw [Category.assoc, Scheme.Hom.comp_appTop]
  rfl

/-- The affine pullback reads the actual unit in the source ring. -/
def affineCoordinateUnit {R : Type u} [CommRing R] (j : Spec (.of R) ⟶ ambient k q)
    (i : Fin q) : Rˣ :=
  Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom (schemeCoordinateUnit j i)

/-- The projection formula on the native homogeneous group, at the unit in degree zero. -/
theorem norm_restriction (M E : Type u) [Field M] [Field E] [Algebra M E]
    [Module.Finite M E] (q : ℕ) (x : MilnorKTheory M q) :
    milnorKNorm M E q (milnorKTransport (algebraMap M E) q x) =
      (Module.finrank M E : ℤ) • x := by
  apply Subtype.ext
  simpa only [coe_milnorKNorm, milnorKTransport_coe, AddSubgroup.coe_zsmul] using
    milnorKNormRing_milnorKRingMap (K := M) (L := E) (x : MilnorKRing M)

private theorem residueDegree_specMap {M E : Type u} [Field M] [Field E] [Algebra M E]
    (x : Spec (.of E)) :
    (Spec.map (CommRingCat.ofHom (algebraMap M E))).residueDegree x = Module.finrank M E := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap M E))
  let R := (Spec (.of E)).residueField x
  let : Algebra M R := Algebra.compHom R
    (((Spec (.of E)).Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of M)).inv ≫ f.appTop).hom)
  let e : E ≃+* R := (Spec.residueFieldIsoOfField x).symm.commRingCatIsoToRingEquiv
  have h : (algebraMap M R) = e.toRingHom.comp (algebraMap M E) := by
    have hcat : (Scheme.ΓSpecIso (.of M)).inv ≫ f.appTop ≫ (Spec (.of E)).Γevaluation x =
        CommRingCat.ofHom (algebraMap M E) ≫ (Spec.residueFieldIsoOfField x).inv := by
      rw [Spec.residueFieldIsoOfField_inv, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    exact congrArg CommRingCat.Hom.hom hcat
  refine (f.residueDegree_eq_finrank x).trans
    (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl M) e ?_).symm
  ext r
  exact RingHom.congr_fun h r

section FinitePoint

variable {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]
  (j : Spec (.of E) ⟶ ambient k q) [IsFinite j]
  (hj : j ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap k E)))

private theorem genericComponent_spec_eq_bot :
    integralComponentAt (genericPoint (Spec (.of E))) = ⊥ := by
  have hcl : Closeds.closure ({genericPoint (Spec (.of E))} : Set (Spec (.of E))) = ⊤ :=
    Closeds.ext (genericPoint_spec (Spec (.of E))).def
  rw [integralComponentAt, hcl, Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot]

local instance genericComponent_spec_isIso :
    IsIso (integralComponentAt (genericPoint (Spec (.of E)))).subschemeι :=
  (Scheme.isIso_subschemeι_iff_eq_bot _).2 (genericComponent_spec_eq_bot (E := E))

/-- The image point with its actual integral component and admissibility. -/
def imageGenerator : Generator k q := by
  let x := genericPoint (Spec (.of E))
  letI : IsFinite (j ≫ pullback.fst _ _) := by
    rw [hj]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  refine ⟨j x, isFiniteCorrespondencePoint_finiteMap _ _ j x ?_ ?_⟩
  · rw [Category.assoc]
    infer_instance
  · have : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
    have hsurj : Function.Surjective (((integralComponentAt x).subschemeι ≫ j) ≫
        pullback.fst (𝟙 (Spec (.of k))) (SmoothSite.torusPower (Spec (.of k)) q).hom) :=
      Function.surjective_to_subsingleton _
    rw [Set.range_eq_univ.mpr hsurj, irreducibleComponents_eq_singleton, Set.mem_singleton_iff]

/-- The native restriction of the map to the component at its image point. -/
def imageFactor : Spec (.of E) ⟶ support (imageGenerator j hj) :=
  inv (integralComponentAt (genericPoint (Spec (.of E)))).subschemeι ≫
    integralComponentMap j (genericPoint (Spec (.of E)))

@[reassoc] theorem imageFactor_inclusion :
    imageFactor j hj ≫ (integralComponentAt (imageGenerator j hj).val).subschemeι = j := by
  let x := genericPoint (Spec (.of E))
  change (inv (integralComponentAt x).subschemeι ≫ integralComponentMap j x) ≫
      (integralComponentAt (j x)).subschemeι = j
  rw [Category.assoc, integralComponentMap_subschemeι, IsIso.inv_hom_id_assoc]

/-- The action of the original support field on the source comes from global pullback. -/
def imageScalarMap : coordinateRing (imageGenerator j hj) →+* E :=
  (Scheme.ΓSpecIso (.of E)).hom.hom.comp (imageFactor j hj).appTop.hom

instance imageAlgebra : Algebra (coordinateRing (imageGenerator j hj)) E :=
  (imageScalarMap j hj).toAlgebra

private theorem imageFactor_projection :
    imageFactor j hj ≫ projection (imageGenerator j hj) =
      Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  rw [projection, imageFactor_inclusion_assoc, hj]

instance imageScalarTower : IsScalarTower k (coordinateRing (imageGenerator j hj)) E := by
  apply IsScalarTower.of_algebraMap_eq'
  symm
  have h : (imageFactor j hj ≫ projection (imageGenerator j hj)).appTop ≫
      (Scheme.ΓSpecIso (.of E)).hom =
      (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k E) := by
    rw [imageFactor_projection, Scheme.ΓSpecIso_naturality]
  rw [Scheme.Hom.comp_appTop] at h
  have h' := congrArg (fun g => (Scheme.ΓSpecIso (.of k)).inv ≫ g) h
  simp only [Iso.inv_hom_id_assoc] at h'
  exact congrArg CommRingCat.Hom.hom h'

instance imageFinite : Module.Finite (coordinateRing (imageGenerator j hj)) E :=
  Module.Finite.of_restrictScalars_finite k _ _

/-- Pullback from the support field gives the original coordinate in the full source field. -/
theorem imageScalarMap_coordinateUnit (i : Fin q) :
    Units.map (algebraMap (coordinateRing (imageGenerator j hj)) E).toMonoidHom
      (coordinateUnit (imageGenerator j hj) i) = affineCoordinateUnit j i := by
  have h : coordinateUnit (imageGenerator j hj) i =
      schemeCoordinateUnit (integralComponentAt (imageGenerator j hj).val).subschemeι i := by
    simp only [coordinateUnit, targetProjection, schemeCoordinateUnit, ambientCoordinate,
      Category.assoc]
  calc
    _ = affineCoordinateUnit
        (imageFactor j hj ≫ (integralComponentAt (imageGenerator j hj).val).subschemeι) i := by
      rw [h, affineCoordinateUnit, schemeCoordinateUnit_comp]
      rfl
    _ = _ := by rw [imageFactor_inclusion]

/-- The canonical affine chart expresses the geometric component map by its global pullback. -/
theorem imageFactor_isoSpec :
    imageFactor j hj ≫ (supportIsoSpec (imageGenerator j hj)).hom =
      Spec.map (CommRingCat.ofHom (imageScalarMap j hj)) := by
  have h := Scheme.isoSpec_hom_naturality (imageFactor j hj)
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp] at h
  exact h.symm

/-- The native pushforward coefficient is the degree over the actual support field. -/
theorem residueDegree_eq_image_finrank (x : Spec (.of E)) :
    j.residueDegree x = Module.finrank (coordinateRing (imageGenerator j hj)) E := by
  calc
    j.residueDegree x = (imageFactor j hj).residueDegree x := by
      have h := congrArg (fun f : Spec (.of E) ⟶ ambient k q => f.residueDegree x)
        (imageFactor_inclusion j hj)
      simpa only [residueDegree_comp, residueDegree_eq_one_of_isClosedImmersion, one_mul]
        using h.symm
    _ = (Spec.map (CommRingCat.ofHom (imageScalarMap j hj))).residueDegree x := by
      have h := congrArg (fun f : Spec (.of E) ⟶ Spec (coordinateRing (imageGenerator j hj)) =>
        f.residueDegree x) (imageFactor_isoSpec j hj)
      simpa only [residueDegree_comp, residueDegree_eq_one_of_isPreimmersion, one_mul] using h
    _ = _ := residueDegree_specMap x

variable [Algebra.IsSeparable k E]

/-- A signed prime pushed from the full field evaluates to its full norm, in every weight. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/FinitePointEvaluation.lean:230-256" "adaptation"
  "The actual image residue degree and ordered coordinates in the original finite field"]
theorem cycleValue_single_image (n : ℤ) :
    cycleValue k q (singleFiniteCorrespondence _ _ (imageGenerator j hj).val
      (imageGenerator j hj).property (n * (j.residueDegree (genericPoint (Spec (.of E))) : ℤ))) =
      n • milnorKNorm k E q (milnorKTupleSymbol (affineCoordinateUnit j)) := by
  rw [cycleValue_single, mul_smul]
  apply congrArg (fun x : MilnorKTheory k q => n • x)
  rw [residueDegree_eq_image_finrank j hj, generatorValue, ← map_zsmul, ← norm_restriction,
    milnorKNorm_tower_of_isSeparable, milnorKTransport_tupleSymbol]
  exact congrArg (fun a : Fin q → Eˣ => milnorKNorm k E q (milnorKTupleSymbol a))
    (funext (imageScalarMap_coordinateUnit j hj))

include hj in
/-- Equality of actual fundamental cycles identifies the norm in the full original field. -/
theorem cycleValue_eq_norm_of_finite_fundamental
    (α : finiteCorrespondences (𝟙 (Spec (.of k))) (SmoothSite.torusPower (Spec (.of k)) q).hom)
    (hα : α.val = finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle (Spec (.of E)))) :
    cycleValue k q α = milnorKNorm k E q (milnorKTupleSymbol (affineCoordinateUnit j)) := by
  rw [AlgebraicCycle.fundamentalCycle_eq_single_genericPoint, finiteCyclePushforward_single] at hα
  have h : α = singleFiniteCorrespondence _ _ (imageGenerator j hj).val
      (imageGenerator j hj).property (1 * (j.residueDegree (genericPoint (Spec (.of E))) : ℤ)) :=
    Subtype.ext hα
  rw [h, cycleValue_single_image, one_zsmul]

end FinitePoint

end AlgebraicGeometry.MotivicCohomology.DiagonalFinitePointEvaluation
