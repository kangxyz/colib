/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.IntegralSource
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.TopDegree
public import Colib.AlgebraicGeometry.Sites.Smooth.Contraction.Geometry
public import Colib.AlgebraicGeometry.Sites.Smooth.Simplex.GeometricallyIntegral
public import Colib.RingTheory.KTheory.MilnorK.Symbols.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeZero

/-!
# Weight-zero motivic cohomology of a field

In weight zero the reduced transfer presheaf is the base representable. On
each integral simplex the structural graph freely generates the actual
correspondence group. Both endpoints preserve this graph, so the incoming
differential at cochain degree zero vanishes. The derived evaluation
comparison identifies the native empty Milnor symbol with the class of this
graph and gives every cycle its integer coefficient.

Adapted from `Motivic/Cohomology/Diagonal/WeightZero.lean` at
`motivic_source_a6805c4`, using the native Stacks correspondence and Milnor groups.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Chow
open scoped Simplicial

universe w u

namespace AlgebraicGeometry.MotivicCohomology.WeightZero

open _root_.AlgebraicGeometry.Scheme SmoothSite SmoothSite.Contraction PresheafWithTransfers
open DiagonalTopDegree

variable (k : Type u) [Field k]

/-- The source of the original singular chains on the base field. -/
abbrev simplexSource (r : ℕ) : SmoothSite (Spec (.of k)) :=
  (Cor.simplexProduct (point k) r).toSmoothSite

instance simplexSource_integral (r : ℕ) : IsIntegral (simplexSource k r).left := by
  change IsIntegral (pullback (𝟙 (Spec (.of k))) (AlgebraicSimplex.structureMap k r))
  exact AlgebraicSimplex.integral_product k (𝟙 (Spec (.of k))) r

local instance (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    IsIntegral ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsIntegral X.left)

/-- The weight-zero quotient retains the actual correspondences to the base. -/
def sectionsCorrespondenceEquiv (X : SmoothSite (Spec (.of k))) :
    sections (reducedTorus k 0) (Cor.mk X) ≃+ (Cor.mk X ⟶ point k) :=
  ((PresheafWithTransfers.forget.mapIso (reducedTorusZeroIso k)).app
    (op (Cor.mk X))).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift

/-- The weight-zero section represented by the actual structure morphism graph. -/
def graphSection (X : SmoothSite (Spec (.of k))) :
    sections (reducedTorus k 0) (Cor.mk X) :=
  (toReducedTorus k 0).hom.app (op (Cor.mk X))
    (ULift.up ((Cor.graphFunctor k).map (toBase X)))

private theorem graphSection_transfer {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    transfer (reducedTorus k 0) ((Cor.graphFunctor k).map f) (graphSection k Y) =
      graphSection k X := by
  let α : Cor.mk X ⟶ Cor.mk Y := (Cor.graphFunctor k).map f
  let β : Cor.mk Y ⟶ Cor.mk (torusPower (Spec (.of k)) 0) :=
    (Cor.graphFunctor k).map (toBase Y)
  have h : (Cor.graphFunctor k).map f ≫ (Cor.graphFunctor k).map (toBase Y) =
      (Cor.graphFunctor k).map (toBase X) := by
    rw [← Functor.map_comp, comp_toBase]
  calc
    _ = (toReducedTorus k 0).hom.app (op (Cor.mk X)) (ULift.up (α ≫ β)) :=
      reducedTorus_transfer_apply k 0 α β
    _ = _ := congrArg
      (fun γ : Cor.mk X ⟶ Cor.mk (torusPower (Spec (.of k)) 0) =>
        (toReducedTorus k 0).hom.app (op (Cor.mk X)) (ULift.up γ)) h

/-- The literal weight-zero singular chains have the structural graph coefficient as degree. -/
def chainEquiv (r : ℕ) : chains k 0 r ≃+ ℤ :=
  (sectionsCorrespondenceEquiv k (simplexSource k r)).trans
    (structureCorrespondenceEquiv (simplexSource k r).hom)

/-- A represented correspondence has its literal coefficient at the structural graph point. -/
theorem chainEquiv_toReduced (r : ℕ) (a : Cor.mk (simplexSource k r) ⟶ point k) :
    chainEquiv k r ((toReducedTorus k 0).hom.app (op (Cor.mk (simplexSource k r))) (ULift.up a)) =
      structureCorrespondenceCoeff (simplexSource k r).hom a :=
  congrArg (structureCorrespondenceCoeff (simplexSource k r).hom)
    ((sectionsCorrespondenceEquiv k (simplexSource k r)).apply_symm_apply a)

/-- The original weight-zero section represented by the actual structural graph. -/
def graphChain (r : ℕ) : chains k 0 r :=
  graphSection k (simplexSource k r)

/-- The structural graph has degree one in each genuine singular chain group. -/
@[simp] theorem chainEquiv_graphChain (r : ℕ) : chainEquiv k r (graphChain k r) = 1 := by
  let X := simplexSource k r
  let : IsIntegral X.left := simplexSource_integral k r
  have h : (Cor.graphFunctor k).map (toBase X) = structureGraphCorrespondence X.hom :=
    graphCorrespondenceOfComponents_structure X.hom (Cor.finite_genericPoints k (Cor.mk X))
  exact (chainEquiv_toReduced k r ((Cor.graphFunctor k).map (toBase X))).trans
    ((congrArg (structureCorrespondenceCoeff X.hom) h).trans
      (structureCorrespondenceCoeff_graph X.hom))

/-- Each endpoint of the actual simplex restricts the structural graph to the structural graph. -/
theorem graphChain_face (i : Fin 2) :
    transfer (reducedTorus k 0) ((Cor.simplexProductCosimplicial (point k)).δ (n := 0) i)
      (graphChain k 1) = graphChain k 0 := by
  rw [Cor.simplexProductCosimplicial_δ]
  exact graphSection_transfer k (X := simplexSource k 0) (Y := simplexSource k 1)
    (SmoothSite.productMap (𝟙 (base (Spec (.of k))))
      ((AlgebraicSimplex.cosimplicialSmoothSite k).δ (n := 0) i))

/-- The two endpoints cancel in the original alternating boundary. -/
theorem boundary_eq_zero : boundary k 0 = 0 := by
  apply AddMonoidHom.ext
  intro x
  change boundary k 0 x = 0
  have hx : x = chainEquiv k 1 x • graphChain k 1 := by
    apply (chainEquiv k 1).injective
    rw [map_zsmul, chainEquiv_graphChain, zsmul_eq_mul, mul_one, Int.cast_id]
  rw [boundary_eq_endpoints, hx]
  simp only [map_zsmul, graphChain_face, sub_self]

/-- There are no nonzero boundaries in singular degree zero. -/
theorem boundary_range_eq_bot : (boundary k 0).range = ⊥ := by
  rw [boundary_eq_zero, AddMonoidHom.range_zero]

/-- The original top-cycle quotient has the degree of its representative. -/
def quotientEquiv : zeroHomology k 0 ≃+ ℤ :=
  (QuotientAddGroup.quotientAddEquivOfEq (boundary_range_eq_bot k)).trans
    (QuotientAddGroup.quotientBot.trans (chainEquiv k 0))

/-- The quotient equivalence reads off the degree of an actual zero-cycle. -/
theorem quotientEquiv_mk (x : chains k 0 0) :
    quotientEquiv k (QuotientAddGroup.mk x) = chainEquiv k 0 x := rfl

variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The integral class of a literal zero-cycle through the original homology projection. -/
def integralCycleClass : chains k 0 0 →+
    motivicCohomology k 0 0 (base (Spec (.of k))) :=
  (quotientToMotivicEquiv k 0).toAddMonoidHom.comp (QuotientAddGroup.mk' _)

/-- The derived/raw evaluation comparison takes the class to its original singular class. -/
theorem integralCycleClass_comparison (x : chains k 0 0) :
    motivicRawBaseEvaluationComparison k 0 0 (integralCycleClass k x) = singularClass k 0 x :=
  quotientToMotivicEquiv_mk k 0 x

/-- Actual integral weight-zero motivic cohomology of any field is its integer cycle degree. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/WeightZero.lean:54-205,224-235"
  "adaptation" "Integer degree on the native structural graph through the original raw evaluation"]
def motivicEquiv : motivicCohomology k 0 0 (base (Spec (.of k))) ≃+ ℤ :=
  (quotientToMotivicEquiv k 0).symm.trans (quotientEquiv k)

/-- The derived class of a literal zero-cycle has its actual integer degree. -/
@[colib_tag "COL-1023"]
theorem motivicEquiv_integralCycleClass (x : chains k 0 0) :
    motivicEquiv k (integralCycleClass k x) = chainEquiv k 0 x :=
  congrArg (quotientEquiv k) ((quotientToMotivicEquiv k 0).symm_apply_apply _)

/-- The derived class of the literal structural graph. -/
def graphClass : motivicCohomology k 0 0 (base (Spec (.of k))) :=
  integralCycleClass k (graphChain k 0)

/-- The derived structural graph has degree one. -/
@[simp] theorem motivicEquiv_graphClass : motivicEquiv k (graphClass k) = 1 := by
  rw [graphClass, motivicEquiv_integralCycleClass, chainEquiv_graphChain]

/-- Native degree-zero Milnor K-theory and integral motivic cohomology have the same degree. -/
@[colib_tag "COL-1023",
  colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/WeightZero.lean:238-262"
  "adaptation" "Native degree-zero Milnor group and the actual derived structural graph class"]
def milnorEquiv : MilnorKTheory k 0 ≃+
    motivicCohomology k 0 0 (base (Spec (.of k))) :=
  (milnorKTheoryZeroAddEquiv k).trans (motivicEquiv k).symm

/-- An integer in the native degree-zero Milnor group gives that multiple of the graph class. -/
@[colib_tag "COL-1023"]
theorem milnorEquiv_zeroMap (z : ℤ) :
    milnorEquiv k (milnorKZeroMap k z) = z • graphClass k := by
  have hdegree : motivicEquiv k (z • graphClass k) = z := by
    rw [map_zsmul, motivicEquiv_graphClass, zsmul_eq_mul, mul_one, Int.cast_id]
  calc
    milnorEquiv k (milnorKZeroMap k z) =
        (motivicEquiv k).symm (milnorKTheoryZeroAddEquiv k (milnorKZeroMap k z)) :=
      AddEquiv.trans_apply (milnorKTheoryZeroAddEquiv k) (motivicEquiv k).symm _
    _ = (motivicEquiv k).symm z :=
      congrArg (motivicEquiv k).symm (milnorKTheoryZeroAddEquiv_milnorKZeroMap k z)
    _ = (motivicEquiv k).symm (motivicEquiv k (z • graphClass k)) :=
      congrArg (motivicEquiv k).symm hdegree.symm
    _ = z • graphClass k := (motivicEquiv k).symm_apply_apply _

/-- The actual empty Milnor symbol is the structural graph class. -/
@[colib_tag "COL-1023"]
theorem milnorEquiv_symbol (a : Fin 0 → kˣ) :
    milnorEquiv k (milnorKTupleSymbol a) = graphClass k := by
  have ha : milnorKTupleSymbol a = milnorKZeroMap k 1 := by
    apply Subtype.ext
    change milnorKSymbolProd k (List.ofFn a) =
      (milnorKSteinbergIdeal k).ringCon.mk' (algebraMap ℤ (MilnorKTensorAlgebra k) 1)
    simp only [List.ofFn_zero, milnorKSymbolProd_nil, map_one]
  calc
    _ = milnorEquiv k (milnorKZeroMap k 1) := congrArg (milnorEquiv k) ha
    _ = (1 : ℤ) • graphClass k := milnorEquiv_zeroMap k 1
    _ = graphClass k := one_zsmul _

end AlgebraicGeometry.MotivicCohomology.WeightZero
