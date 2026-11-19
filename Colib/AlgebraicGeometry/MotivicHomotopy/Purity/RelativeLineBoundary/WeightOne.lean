/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReducedTorusObject
public import Colib.AlgebraicGeometry.MotivicHomotopy.ReducedMotivicProduct.Coordinate
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.WeightOne
import Colib.AlgebraicGeometry.Correspondences.Cancellation.TorusChart
import all Colib.AlgebraicGeometry.MotivicHomotopy.ReducedMotivicProduct.Coordinate
import all Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.WeightOne
import all Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus

/-!
# The positive Laurent coordinate of the native reduced torus

The base target-unit quotient sends the original identity graph to the
weight-one reduced graph. The zero-simplex normalization retains the forward
Laurent coordinate.

The elementary quotient comparison follows the Colib Coniveau draft
`Uniformizer.lean`, blob `8345ef73325dbaa1ccfbe02130dfc0f4dd82f385`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction

universe u w w' w''

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "S(" K ")" => Spec (CommRingCat.of K)
local notation "B(" K ")" => SmoothSite.base S(K)
local notation "G(" K ")" => SmoothSite.multiplicativeGroupObject S(K)
local notation "R(" K ")" => representableLarge K

private abbrev pointedTorusProjection :
    (R(k)).obj (Cor.mk G(k)) ⟶ pointedTorusCokernel k :=
  ⟨cokernel.π (torusOneRepresentable k).hom⟩

private theorem toReducedTorus_one_comp :
    toReducedTorus k 1 ≫ (reducedTorusOneIso k).hom =
      (torusRepresentableOneIso k).hom ≫ pointedTorusProjection k := by
  apply ObjectProperty.hom_ext
  change cokernel.π (torusRelation k 1) ≫ (reducedTorusOneIso k).hom.hom =
    (torusRepresentableOneIso k).hom.hom ≫ cokernel.π (torusOneRepresentable k).hom
  unfold reducedTorusOneIso
  exact cokernel.π_desc _ _ _

set_option maxHeartbeats 1100000 in
-- Cancel the original map of cokernels on its ambient quotient.
private theorem toTorusCancellationCoefficients_base_pointed :
    toTorusCancellationCoefficients k (Cor.mk B(k)) ≫
        ((torusCancellationBaseWeightOneIso k) ≪≫ reducedTorusOneIso k).hom =
      (R(k)).map ((Cor.graphFunctor k).map (SmoothSite.productSnd B(k) G(k))) ≫
        pointedTorusProjection k := by
  let V : PresheafWithTransfers.{u + 1} k ⥤ (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    PresheafWithTransfers.forget
  let R := Cor.graphFunctor k ⋙ R(k)
  let f := R.map (SmoothSite.productMap (𝟙 B(k)) (SmoothSite.torusOne S(k)))
  let g := R.map (SmoothSite.torusOne S(k))
  let a := R.mapIso (baseProductSndIso k B(k))
  let b := R.mapIso (baseProductSndIso k G(k))
  have h : V.map f ≫ (V.mapIso b).hom = (V.mapIso a).hom ≫ V.map g := by
    change (R ⋙ V).map (SmoothSite.productMap (𝟙 B(k)) (SmoothSite.torusOne S(k))) ≫
      (R ⋙ V).map (baseProductSndIso k G(k)).hom =
        (R ⋙ V).map (baseProductSndIso k B(k)).hom ≫ (R ⋙ V).map (SmoothSite.torusOne S(k))
    exact ((R ⋙ V).map_comp _ _).symm.trans
      (((R ⋙ V).congr_map (baseProductSndIso_unit k)).trans ((R ⋙ V).map_comp _ _))
  let c := cokernel.mapIso (V.map f) (V.map g) (V.mapIso a) (V.mapIso b) h
  let z := PreservesCokernel.iso V f ≪≫ c
  let V₀ := Functor.FullyFaithful.ofFullyFaithful V
  let r : torusCancellationCoefficients k (Cor.mk B(k)) ≅ pointedTorusCokernel k :=
    V₀.preimageIso z
  have hr : ((torusCancellationBaseWeightOneIso k) ≪≫ reducedTorusOneIso k).hom = r.hom := by
    let e := reducedTorusOneIso k
    calc
      _ = (r.hom ≫ e.inv) ≫ e.hom := rfl
      _ = r.hom := (Category.assoc _ _ _).trans
        ((congrArg (r.hom ≫ ·) e.inv_hom_id).trans (Category.comp_id _))
  rw [hr]
  apply V.map_injective
  have hv : V.map r.hom = z.hom :=
    V₀.map_preimage (X := torusCancellationCoefficients k (Cor.mk B(k)))
      (Y := pointedTorusCokernel k) z.hom
  change V.map (cokernel.π f ≫ r.hom) = V.map (b.hom ≫ pointedTorusProjection k)
  rw [V.map_comp, V.map_comp, hv]
  change V.map (cokernel.π f) ≫ (PreservesCokernel.iso V f).hom ≫ c.hom =
    V.map b.hom ≫ cokernel.π (V.map g)
  rw [PreservesCokernel.π_iso_hom_assoc]
  exact cokernel.π_desc _ _ _

/-- The coefficient quotient of the actual torus representable sends the
identity graph to the forward weight-one graph. -/
def torusCoordinateGraphQuotient :
    (R(k)).obj (Cor.mk G(k)) ⟶ reducedTorus k 1 :=
  (torusRepresentableOneIso k).inv ≫ toReducedTorus k 1

set_option maxHeartbeats 650000 in
-- Retain the sign of the defining weight-one quotient projection.
private theorem toTorusCancellationCoefficients_base_weightOne :
    toTorusCancellationCoefficients k (Cor.mk B(k)) ≫ (torusCancellationBaseWeightOneIso k).hom =
      (R(k)).map ((Cor.graphFunctor k).map (SmoothSite.productSnd B(k) G(k))) ≫
        torusCoordinateGraphQuotient k := by
  let f := (R(k)).map ((Cor.graphFunctor k).map (SmoothSite.productSnd B(k) G(k)))
  let d := torusRepresentableOneIso k
  let e := reducedTorusOneIso k
  have h : (f ≫ d.inv ≫ toReducedTorus k 1) ≫ e.hom = f ≫ pointedTorusProjection k := by
    rw [Category.assoc, Category.assoc, toReducedTorus_one_comp, Iso.inv_hom_id_assoc]
  apply (cancel_mono e.hom).mp
  calc
    _ = toTorusCancellationCoefficients k (Cor.mk B(k)) ≫
        ((torusCancellationBaseWeightOneIso k) ≪≫ e).hom := Category.assoc _ _ _
    _ = _ := (toTorusCancellationCoefficients_base_pointed k).trans h.symm

/-- Evaluation at the identity of the native torus is precisely the
positive reduced Laurent graph. -/
theorem torusCoordinateGraphQuotient_identity :
    (torusCoordinateGraphQuotient k).hom.app (op (Cor.mk G(k))) (ULift.up (𝟙 _)) =
      MotivicCohomology.WeightOne.reducedTorusGraphSection k (𝟙 G(k)) := by
  change (toReducedTorus k 1).hom.app (op (Cor.mk G(k)))
      (((R(k)).map ((Cor.graphFunctor k).map (SmoothSite.torusPowerOneIso S(k)).inv)).hom.app
        (op (Cor.mk G(k))) (ULift.up (𝟙 _))) = _
  rw [representableLarge_map_app_apply, Category.id_comp]
  unfold MotivicCohomology.WeightOne.reducedTorusGraphSection
  rw [Category.id_comp]

end AlgebraicGeometry.PresheafWithTransfers

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers
open MotivicCohomology.WeightOne

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (LargeSheaves k)]
  [HasDerivedCategory.{w''} AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]

local notation "S(" K ")" => Spec (CommRingCat.of K)
local notation "B(" K ")" => SmoothSite.base S(K)
local notation "G(" K ")" => SmoothSite.multiplicativeGroupObject S(K)
local notation "R(" K ")" => representableLarge K
local notation "Q(" K ")" => singularEffectiveMotiveFunctor K
local notation "E(" K ")" => effectiveSmoothMotive K

/-- The unshifted weight-one object of the native reduced torus, using the
original base target-unit quotient. -/
def effectiveReducedTorusWeightOneIso :
    effectiveReducedTorusMotive k ≅ (Q(k)).obj (reducedTorus k 1) :=
  effectiveReducedTorusTensorRepresentableIso k (Cor.mk B(k)) ≪≫
    (Q(k)).mapIso (torusCancellationBaseWeightOneIso k)

set_option maxHeartbeats 1100000 in
-- Compute the original quotient after cancelling the torus-base product comparison.
/-- The native reduced torus projection is the actual positive coordinate
graph on the weight-one coefficient. -/
theorem torusReducedProjection_weightOne :
    torusReducedProjection k ≫ (effectiveReducedTorusWeightOneIso k).hom =
      (Q(k)).map (torusCoordinateGraphQuotient k) := by
  let Y := Cor.mk B(k)
  let t := torusBaseProduct (k := k)
  let e := effectiveReducedTorusTensorRepresentableIso k Y
  let r := toTorusCancellationCoefficients k Y
  let s := (torusCancellationBaseWeightOneIso k).hom
  let q := torusCoordinateGraphQuotient k
  let F := Cor.graphFunctor k ⋙ R(k)
  let Q := Q(k)
  have h : r ≫ s = F.map t.hom ≫ q :=
    toTorusCancellationCoefficients_base_weightOne k
  change (Q.map (F.map t.inv) ≫ Q.map r ≫ e.inv) ≫
    (e.hom ≫ Q.map s) = Q.map q
  calc
    _ = Q.map (F.map t.inv) ≫ Q.map r ≫ Q.map s := by
      simp only [Category.assoc, e.inv_hom_id_assoc]
    _ = Q.map (F.map t.inv) ≫ Q.map (r ≫ s) := by rw [Q.map_comp]
    _ = Q.map (F.map t.inv ≫ F.map t.hom ≫ q) :=
      (congrArg (Q.map (F.map t.inv) ≫ ·) (Q.congr_map h)).trans (Q.map_comp _ _).symm
    _ = _ := by rw [← Category.assoc (F.map t.inv), ← F.map_comp,
        t.inv_hom_id, F.map_id, Category.id_comp]

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory (LargeSheaves k)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})] in
/-- In singular degree zero the original projection of the identity graph,
pulled back along the actual zero-simplex projection, is the coordinate
section already used by the geometric weight-one comparison. -/
theorem torusCoordinateGraphQuotient_zeroSimplex :
    let G := G(k)
    let P := (rawReducedSingular k).X 0
    (toSheafify (SmoothSite.nisnevichTopology S(k)) P).app (op G)
        (((torusCoordinateGraphQuotient k) ≫ singularTermUnit (reducedTorus k 1) 0).hom.app
          (op (Cor.mk G)) (ULift.up (𝟙 _))) =
      torusCoordinateGraphZeroSection k := by
  intro G P
  let f := SmoothSite.productFst G (AlgebraicSimplex.smoothSiteObj k 0)
  let a := (torusCoordinateGraphQuotient k).hom.app (op (Cor.mk G))
  let J := SmoothSite.nisnevichTopology S(k)
  change (toSheafify J P).app (op G) ((rawReducedTorus k).map f.op (a (ULift.up (𝟙 _)))) =
    torusCoordinateGraphZeroSection k
  have h := reducedTorusGraphSection_pullback k f (𝟙 G)
  rw [Category.comp_id] at h
  rw [torusCoordinateGraphQuotient_identity k]
  exact congrArg (fun x => (toSheafify J P).app (op G) x) h

end AlgebraicGeometry.MotivicHomotopy
