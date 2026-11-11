/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.NormalizedEndpointNorm
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.ReducedPointNorm

/-!
# Milnor evaluation on the original diagonal cycle quotient

The zero-simplex chart identifies reduced zero-chains with sections at the
base field. The degree-one faces give the original endpoint point norms.
Normalized endpoint comparison in characteristic zero gives their equality.
Evaluation descends through the actual singular boundary to the original
raw and derived diagonal groups.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe w u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalMilnorBoundaryDescent

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers DiagonalTopDegree DiagonalCycleSymbols DiagonalReducedPointNorm
open DiagonalBoundarySupport (pointToZero pointToZero_comp_productFst
  evaluationPoint evaluationPoint_face)
open DiagonalFiniteCyclePushforward (sourceFace)

variable (k : Type u) [Field k]

/-- The inverse of the original zero-simplex projection is its actual chart graph. -/
def zeroSimplexInv : point k ⟶ Cor.simplexProduct (point k) 0 :=
  (Cor.graphFunctor k).map (pointToZero k)

/-- The inverse chart graph followed by the original projection is the identity. -/
theorem zeroSimplexInv_comp_projection :
    zeroSimplexInv k ≫ WeightOne.zeroSimplexProjection k = 𝟙 (point k) := by
  let X := SmoothSite.base (Spec (.of k))
  let f := SmoothSite.productFst X (AlgebraicSimplex.smoothSiteObj k 0)
  let F := Cor.graphFunctor k
  calc
    _ = F.map (pointToZero k ≫ f) := (F.map_comp (pointToZero k) f).symm
    _ = F.map (𝟙 X) := congrArg (fun g : X ⟶ X => F.map g) (pointToZero_comp_productFst k)
    _ = _ := F.map_id X

variable (q : ℕ)

/-- The zero-simplex norm is the point evaluator transferred along the actual chart. -/
def degreeZeroNorm : chains k q 0 →+ MilnorKTheory k q :=
  (reducedNorm k q).comp (transfer (reducedTorus k q) (zeroSimplexInv k)).hom

/-- A represented zero-chain retains the signed norm of its underlying point cycle. -/
theorem degreeZeroNorm_quotient
    (α : Cor.simplexProduct (point k) 0 ⟶ target k q) :
    degreeZeroNorm k q ((toReducedTorus k q).hom.app
      (op (Cor.simplexProduct (point k) 0)) (ULift.up α)) =
      DiagonalPointNorm.cycleValue k q (zeroSimplexInv k ≫ α) :=
  (congrArg (reducedNorm k q) (reducedTorus_transfer_apply k q (zeroSimplexInv k) α)).trans
    (reducedNorm_quotient k q (zeroSimplexInv k ≫ α))

/-- Each actual reduced product coface gives the corresponding signed endpoint norm. -/
theorem degreeZeroNorm_face_quotient (i : Fin 2)
    (α : Cor.simplexProduct (point k) 1 ⟶ target k q) :
    degreeZeroNorm k q
      (transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ (n := 0) i)
        ((toReducedTorus k q).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α))) =
      DiagonalPointNorm.cycleValue k q
        ((Cor.graphFunctor k).map (evaluationPoint k (i.val : k)) ≫ α) := by
  let δ : Cor.simplexProduct (point k) 0 ⟶ Cor.simplexProduct (point k) 1 :=
    (Cor.simplexProductCosimplicial (point k)).δ (n := 0) i
  have hδ : δ = (Cor.graphFunctor k).map (sourceFace k i) :=
    Cor.simplexProductCosimplicial_δ (point k) (n := 0) i
  have hface : zeroSimplexInv k ≫ δ =
      (Cor.graphFunctor k).map (evaluationPoint k (i.val : k)) := by
    rw [hδ, zeroSimplexInv, ← Functor.map_comp, ← evaluationPoint_face]
  calc
    _ = degreeZeroNorm k q ((toReducedTorus k q).hom.app
        (op (Cor.simplexProduct (point k) 0)) (ULift.up (δ ≫ α))) :=
      congrArg (degreeZeroNorm k q) (reducedTorus_transfer_apply k q δ α)
    _ = DiagonalPointNorm.cycleValue k q (zeroSimplexInv k ≫ δ ≫ α) :=
      degreeZeroNorm_quotient k q (δ ≫ α)
    _ = _ := by rw [← Category.assoc, hface]

variable [CharZero k]

/-- The two actual point norms agree, so evaluation kills the alternating boundary. -/
theorem degreeZeroNorm_boundary
    (s : chains k q 1) : degreeZeroNorm k q (boundary k q s) = 0 := by
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective k q (Cor.simplexProduct (point k) 1) s
  let rep : chains k q 1 :=
    (toReducedTorus k q).hom.app (op (Cor.simplexProduct (point k) 1)) (ULift.up α)
  let d (i : Fin 2) : chains k q 0 :=
    transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ (n := 0) i) rep
  let value (t : k) := DiagonalPointNorm.cycleValue k q
    ((Cor.graphFunctor k).map (evaluationPoint k t) ≫ α)
  have he (i : Fin 2) : degreeZeroNorm k q (d i) = value (i.val : k) :=
    degreeZeroNorm_face_quotient k q i α
  have hz : ((0 : Fin 2).val : k) = 0 := Nat.cast_zero
  have ho : ((1 : Fin 2).val : k) = 1 := Nat.cast_one
  calc
    _ = degreeZeroNorm k q (d 0 - d 1) :=
      congrArg (degreeZeroNorm k q) (boundary_eq_endpoints k q rep)
    _ = degreeZeroNorm k q (d 0) - degreeZeroNorm k q (d 1) := map_sub (degreeZeroNorm k q) _ _
    _ = value 0 - value 1 := congrArg₂ (· - ·)
      ((he 0).trans (congrArg value hz)) ((he 1).trans (congrArg value ho))
    _ = 0 := sub_eq_zero.mpr
      (DiagonalBoundarySupport.cycleValue_endpoint_eq (k := k) (q := q) α)

/-- The raw top-term evaluator retains the actual signed complex's term identification. -/
def rawTermNorm : (motivicRawBaseComplex k q).X q →+ MilnorKTheory k q :=
  (degreeZeroNorm k q).comp (topTermIso k q).hom.hom

/-- The raw differential is annihilated with its original shift sign. -/
theorem rawTermNorm_differential (s : (motivicRawBaseComplex k q).X ((q : ℤ) - 1)) :
    rawTermNorm k q ((motivicRawBaseComplex k q).d ((q : ℤ) - 1) q s) = 0 := by
  rw [raw_d_top]
  change degreeZeroNorm k q ((topTermIso k q).hom
    ((-1 : ℤ) ^ q • (topTermIso k q).inv (boundary k q ((previousTermIso k q).hom s)))) = 0
  rw [map_zsmul, Iso.inv_hom_id_apply, map_zsmul, degreeZeroNorm_boundary, smul_zero]

/-- Evaluation of actual reduced zero-cycles modulo the original boundaries. -/
def quotientNorm : zeroHomology k q →+ MilnorKTheory k q :=
  QuotientAddGroup.lift (boundary k q).range (degreeZeroNorm k q) (by
    rintro _ ⟨s, rfl⟩
    exact degreeZeroNorm_boundary k q s)

/-- Each quotient class has the value of its literal representative. -/
@[simp] theorem quotientNorm_mk (s : chains k q 0) :
    quotientNorm k q (QuotientAddGroup.mk s) = degreeZeroNorm k q s := rfl

/-- The descended evaluator on the original signed raw homology. -/
def rawNorm : (motivicRawBaseComplex k q).homology q →+ MilnorKTheory k q :=
  (quotientNorm k q).comp (quotientToRawEquiv k q).symm.toAddMonoidHom

/-- The raw norm of an actual singular class gives the zero-chain norm. -/
@[simp] theorem rawNorm_singularClass (s : chains k q 0) :
    rawNorm k q (singularClass k q s) = degreeZeroNorm k q s := by
  let e := quotientToRawEquiv k q
  have he : e (QuotientAddGroup.mk s) = singularClass k q s := quotientToRawEquiv_mk k q s
  calc
    _ = rawNorm k q (e (QuotientAddGroup.mk s)) :=
      congrArg (rawNorm k q) he.symm
    _ = quotientNorm k q (QuotientAddGroup.mk s) :=
      congrArg (quotientNorm k q) (e.symm_apply_apply _)
    _ = _ := quotientNorm_mk k q s

/-- The descended evaluation on point classes keeps the original signed point norm. -/
theorem rawNorm_cycleClass (α : point k ⟶ target k q) :
    rawNorm k q (cycleClass k q α) = DiagonalPointNorm.cycleValue k q α := by
  rw [cycleClass_apply, rawNorm_singularClass, degreeZeroNorm_quotient,
    ← Category.assoc, zeroSimplexInv_comp_projection, Category.id_comp]

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Evaluation on the originally defined derived diagonal motivic cohomology. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/MilnorBoundaryDescent.lean:54-128"
  "adaptation" "Evaluation on the actual raw cycle quotient and derived base comparison"]
def motivicNorm : motivicCohomology k q q (SmoothSite.base (Spec (.of k))) →+
    MilnorKTheory k q :=
  (rawNorm k q).comp (motivicRawBaseEvaluationComparison k q q).toAddMonoidHom

/-- Derived and raw evaluation commute with the original base comparison. -/
theorem motivicNorm_comparison
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicNorm k q x =
      rawNorm k q (motivicRawBaseEvaluationComparison k q q x) := rfl

end AlgebraicGeometry.MotivicCohomology.DiagonalMilnorBoundaryDescent
