/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.FieldCycleEvaluation
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.PointNormDictionary

/-!
# Genuine raw weight-one cycle and graph classes

Classes live in the homology of the original signed raw transfer complex.
The zero-simplex projection is the literal geometric projection. No abstract
unit-group isomorphism is used to define graph classes or signed point classes.

Adapted from Motivic/Cohomology/WeightOne/HomologyNorm.lean:82-121 and
Equivalence.lean:43-95 at revision a6805c4a87cdfd7717dd7a94039246a167f15380.
The norm-on-homology identification is deliberately a separate obligation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite AlgebraicSimplex

universe w u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- There is no raw weight-one term in cochain degree two. -/
theorem isZero_raw_X_two : IsZero ((motivicRawBaseComplex k 1).X 2) := by
  let E := toPresheaf k ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))
  change IsZero (E.obj ((singularCochainComplex (reducedTorus k 1) 0).X 1))
  exact E.map_isZero (isZero_singularCochainComplex_X (reducedTorus k 1) 0 1 (by decide))

/-- The outgoing differential from the actual top raw term is zero. -/
theorem raw_outgoing_d_zero : (motivicRawBaseComplex k 1).d 1 2 = 0 :=
  (isZero_raw_X_two k).eq_of_tgt _ _

/-- The actual class map from the top raw term. -/
def rawClass : (motivicRawBaseComplex k 1).X 1 ⟶
    (motivicRawBaseComplex k 1).homology 1 :=
  ((motivicRawBaseComplex k 1).iCyclesIso 1 2 ((ComplexShape.up ℤ).next_eq' rfl)
    (raw_outgoing_d_zero k)).inv ≫ (motivicRawBaseComplex k 1).homologyπ 1

/-- Every raw homology class has an actual top-term representative. -/
theorem rawClass_surjective : Function.Surjective (rawClass k) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mp
  unfold rawClass
  infer_instance

/-- The class map kills precisely the actual preceding differential as a composite. -/
theorem differential_rawClass :
    (motivicRawBaseComplex k 1).d 0 1 ≫ rawClass k = 0 := by
  rw [rawClass, ← (motivicRawBaseComplex k 1).toCycles_i 0 1]
  simp only [Category.assoc, HomologicalComplex.iCyclesIso_hom_inv_id_assoc,
    HomologicalComplex.toCycles_comp_homologyπ]

/-- Every genuine signed raw boundary has zero class. -/
theorem rawClass_boundary (x : (motivicRawBaseComplex k 1).X 0) :
    rawClass k ((motivicRawBaseComplex k 1).d 0 1 x) = 0 :=
  ConcreteCategory.congr_hom (differential_rawClass k) x

/-- The exact chain-zero term identifies with the actual top raw class map. -/
def singularClass : sections (reducedTorus k 1) (Cor.simplexProduct (point k) 0) →+
    (motivicRawBaseComplex k 1).homology 1 :=
  (rawClass k).hom.comp (motivicRawBaseComplexXIso k 1 0).inv.hom

/-- The zero-simplex source projection is the actual graph of the relative projection. -/
def zeroSimplexProjection : Cor.simplexProduct (point k) 0 ⟶ point k :=
  (Cor.graphFunctor k).map (productFst (base (Spec (.of k))) (smoothSiteObj k 0))

/-- Actual signed correspondences give classes by the original quotient and projection. -/
def cycleClass : (point k ⟶ pointTarget k) →+ (motivicRawBaseComplex k 1).homology 1 :=
  (singularClass k).comp
    (((toReducedTorus k 1).hom.app (op (Cor.simplexProduct (point k) 0))).hom.comp
      ((AddEquiv.ulift : ULift.{u + 1}
          (Cor.simplexProduct (point k) 0 ⟶ pointTarget k) ≃+
            (Cor.simplexProduct (point k) 0 ⟶ pointTarget k)).symm.toAddMonoidHom.comp
        (Preadditive.leftComp (pointTarget k) (zeroSimplexProjection k))))

/-- The class of the literal rational unit graph, not the inverse of a chosen equivalence. -/
def graphUnitClass (a : kˣ) : (motivicRawBaseComplex k 1).homology 1 :=
  cycleClass k ((Cor.graphFunctor k).map (rationalPoint k a))

/-- The graph-class notation retains its actual geometric representative. -/
theorem cycleClass_graph (a : kˣ) :
    cycleClass k ((Cor.graphFunctor k).map (rationalPoint k a)) = graphUnitClass k a := rfl

/-- Signed sums of point cycles keep their original integer coefficients in raw homology. -/
theorem cycleClass_zsmul (m : ℤ) (z : point k ⟶ pointTarget k) :
    cycleClass k (m • z) = m • cycleClass k z := map_zsmul (cycleClass k) m z

/-- The raw weight-one differential retains the actual negative shift sign. -/
theorem raw_d_zero_one :
    (motivicRawBaseComplex k 1).d 0 1 =
      -((motivicRawBaseComplexXIso k 1 1).hom ≫
        (singularObj (reducedTorus k 1) (point k)).d 1 0 ≫
          (motivicRawBaseComplexXIso k 1 0).inv) := by
  let E := toPresheaf k ⋙ (evaluation _ AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))
  simp only [motivicRawBaseComplex, CochainComplex.shiftFunctor_obj_d',
    Units.smul_def, Int.negOnePow_neg, Int.coe_negOnePow_natCast,
    pow_one, neg_one_zsmul]
  apply congrArg Neg.neg
  change E.map (((singularComplex (reducedTorus k 1)).extend
    (ComplexShape.embeddingUpIntLE 0)).d (-1) 0) = _
  rw [(singularComplex (reducedTorus k 1)).extend_d_eq
    (ComplexShape.embeddingUpIntLE 0) (i := 1) (j := 0) (by rfl) (by rfl),
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rfl

/-- Every original singular boundary vanishes, including the canonical weight-one minus sign. -/
theorem singularClass_boundary
    (s : sections (reducedTorus k 1) (Cor.simplexProduct (point k) 1)) :
    singularClass k ((singularObj (reducedTorus k 1) (point k)).d 1 0 s) = 0 := by
  have h := rawClass_boundary k ((motivicRawBaseComplexXIso k 1 1).inv s)
  rw [raw_d_zero_one] at h
  change rawClass k (-((motivicRawBaseComplexXIso k 1 0).inv
    ((singularObj (reducedTorus k 1) (point k)).d 1 0
      ((motivicRawBaseComplexXIso k 1 1).hom
        ((motivicRawBaseComplexXIso k 1 1).inv s))))) = 0 at h
  rw [Iso.inv_hom_id_apply, map_neg, neg_eq_zero] at h
  exact h

variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Integral motivic point classes use the actual derived/raw evaluation comparison. -/
def integralCycleClass : (point k ⟶ pointTarget k) →+
    motivicCohomology k 1 1 (base (Spec (.of k))) :=
  (motivicRawBaseEvaluationComparison k 1 1).symm.toAddMonoidHom.comp (cycleClass k)

/-- The actual integral graph class, preserving the raw representative. -/
def integralGraphUnitClass (a : kˣ) : motivicCohomology k 1 1 (base (Spec (.of k))) :=
  (motivicRawBaseEvaluationComparison k 1 1).symm (graphUnitClass k a)

/-- Integral and raw graph classes agree through the specified evaluation comparison. -/
@[simp] theorem integralGraphUnitClass_comparison (a : kˣ) :
    motivicRawBaseEvaluationComparison k 1 1 (integralGraphUnitClass k a) =
      graphUnitClass k a := (motivicRawBaseEvaluationComparison k 1 1).apply_symm_apply _

/-- The integral signed-cycle map uses precisely the same rational graph. -/
theorem integralCycleClass_graph (a : kˣ) :
    integralCycleClass k ((Cor.graphFunctor k).map (rationalPoint k a)) =
      integralGraphUnitClass k a := rfl

end AlgebraicGeometry.MotivicCohomology.WeightOne
