/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.CoordinateReduced
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.GraphNormalization
import Colib.AlgebraicGeometry.Correspondences.Cancellation.TorusChart
import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.ChainNormalization

/-!
# The torus coordinate as a reduced singular graph

In the ordinary reduced singular complex the torus suspension class is
represented by the identity graph pulled back along the zero-simplex
projection. Its norm is the forward Laurent coordinate. The signed
placement comparison preserves this class in bidegree (1,1).
-/

@[expose] public noncomputable section

set_option maxRecDepth 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.PointedSimplicialPresheaf Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers AlgebraicGeometry.MotivicCohomology.WeightOne
open Stacks.Cohomology.FreeYonedaUnivLE

universe d u

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k]

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "Jₖ" => SmoothSite.nisnevichTopology Sₖ
local notation "Gₘ" => multiplicativeGroupObject Sₖ
local notation "Uₖ" => largeUnitsSheaf Sₖ
set_option quotPrecheck false in
local notation "L" =>
  (AlgebraicSimplex.sheafifiedSingularChainsFunctor k Jₖ).obj (rawReducedTorus k)
local notation "e" => ComplexShape.embeddingUpIntLE 0

/-- Ordinary Nisnevich sheaves in the universe of the motivic coefficients. -/
abbrev TorusSheaves (k : Type u) [Field k] :=
  Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}

/-- The relative free source of the original multiplicative unit. -/
abbrev TorusSource (k : Type u) [Field k] :=
  relativeSource.{u + 1} (SmoothSite.nisnevichTopology (Spec (.of k)))
    (torusOne (Spec (.of k)))

private abbrev zeroProjection (X : SmoothSite Sₖ) :=
  productFst X (AlgebraicSimplex.smoothSiteObj k 0)

/-- The zero-simplex term of the sheafified singular torus contains the literal
identity graph pulled back along the simplex projection. -/
@[no_expose]
def torusCoordinateGraphZeroSection : ((L).X 0).obj.obj (op Gₘ) :=
  (toSheafify Jₖ ((rawReducedSingular k).X 0)).app (op Gₘ)
    (reducedTorusGraphSection k (zeroProjection k Gₘ))

private theorem torusOne_pullback_coordinateGraphZero :
    ((L).X 0).obj.map (torusOne Sₖ).op (torusCoordinateGraphZeroSection k) = 0 := by
  let P := (rawReducedSingular k).X 0
  let z := reducedTorusGraphSection k (zeroProjection k Gₘ)
  have hn := NatTrans.naturality_apply (toSheafify Jₖ P) (torusOne Sₖ).op z
  change (sheafify Jₖ P).map (torusOne Sₖ).op ((toSheafify Jₖ P).app (op Gₘ) z) = 0
  let a : product (base Sₖ) (AlgebraicSimplex.smoothSiteObj k 0) ⟶
      product Gₘ (AlgebraicSimplex.smoothSiteObj k 0) :=
    SmoothSite.productMap (torusOne Sₖ) (𝟙 _)
  let b := zeroProjection k (base Sₖ)
  have h : a ≫ zeroProjection k Gₘ = b ≫ torusOne Sₖ :=
    SmoothSite.productMap_fst _ _
  have hz : (rawReducedTorus k).map a.op z = 0 := by
    calc
      _ = reducedTorusGraphSection k (a ≫ zeroProjection k Gₘ) :=
        reducedTorusGraphSection_pullback k a _
      _ = reducedTorusGraphSection k (b ≫ torusOne Sₖ) :=
        congrArg (reducedTorusGraphSection k) h
      _ = (rawReducedTorus k).map b.op (reducedTorusGraphSection k (torusOne Sₖ)) :=
        (reducedTorusGraphSection_pullback k b _).symm
      _ = 0 := by rw [reducedTorusGraphSection_torusOne, map_zero]
  exact hn.symm.trans ((congrArg (fun x => (toSheafify Jₖ P).app (op (base Sₖ)) x) hz).trans
    (map_zero _))

private def torusCoordinateGraphHom : (freeYoneda.{u + 1} Jₖ).obj Gₘ ⟶ (L).X 0 :=
  (sectionsAddEquiv.{u + 1} Gₘ ((L).X 0)).symm (torusCoordinateGraphZeroSection k)

private theorem torusOne_torusCoordinateGraphHom :
    (freeYoneda.{u + 1} Jₖ).map (torusOne Sₖ) ≫ torusCoordinateGraphHom k = 0 := by
  apply (sectionsAddEquiv.{u + 1} (base Sₖ) ((L).X 0)).injective
  rw [map_zero, sectionsAddEquiv_apply, sectionsEquiv_naturality_left]
  change ((L).X 0).obj.map (torusOne Sₖ).op
    (sectionsAddEquiv.{u + 1} Gₘ ((L).X 0) (torusCoordinateGraphHom k)) = 0
  rw [torusCoordinateGraphHom, AddEquiv.apply_symm_apply]
  exact torusOne_pullback_coordinateGraphZero k

/-- The original graph of the torus coordinate in the relative singular term. -/
@[no_expose]
def torusCoordinateRelativeGraph : (TorusSource k) ⟶ (L).X 0 :=
  cokernel.desc ((freeYoneda.{u + 1} Jₖ).map (torusOne Sₖ))
    (torusCoordinateGraphHom k) (torusOne_torusCoordinateGraphHom k)

private abbrev unitsProjection : (L).X 0 ⟶ Uₖ :=
  (weightOneSheafChainComparison k).f 0 ≫
    (HomologicalComplex.singleObjXSelf (.down ℕ) 0 Uₖ).hom

/-- The geometric weight-one norm of the relative graph is the actual
forward coordinate, with no change of orientation. -/
@[reassoc]
theorem torusCoordinateRelativeGraph_comp_unitsProjection :
    torusCoordinateRelativeGraph k ≫ (weightOneSheafChainComparison k).f 0 ≫
      (HomologicalComplex.singleObjXSelf (.down ℕ) 0 Uₖ).hom =
        torusCoordinateRelativeUnit k := by
  apply (cancel_epi (relativeSourceπ.{u + 1} Jₖ (torusOne Sₖ))).mp
  have hp : relativeSourceπ.{u + 1} Jₖ (torusOne Sₖ) ≫ torusCoordinateRelativeGraph k =
      torusCoordinateGraphHom k :=
    cokernel.π_desc ((freeYoneda.{u + 1} Jₖ).map (torusOne Sₖ)) _ _
  rw [← Category.assoc, hp]
  apply (sectionsAddEquiv.{u + 1} Gₘ Uₖ).injective
  rw [sectionsAddEquiv_relativeSourceπ_torusCoordinateRelativeUnit,
    sectionsAddEquiv_apply, sectionsEquiv_naturality]
  change (unitsProjection k).hom.app (op Gₘ)
    (sectionsAddEquiv.{u + 1} Gₘ ((L).X 0) (torusCoordinateGraphHom k)) =
      torusCoordinateUnitSection k
  rw [torusCoordinateGraphHom, AddEquiv.apply_symm_apply, torusCoordinateGraphZeroSection]
  have h := ConcreteCategory.congr_hom (rawChainComparison_zero_pullback k Gₘ)
    (reducedTorusGraphSection k (𝟙 Gₘ))
  change (unitsProjection k).hom.app (op Gₘ)
    ((toSheafify Jₖ ((rawReducedSingular k).X 0)).app (op Gₘ)
      ((rawReducedTorus k).map (zeroProjection k Gₘ).op
        (reducedTorusGraphSection k (𝟙 Gₘ)))) =
    (reducedNorm k).app (op Gₘ) (reducedTorusGraphSection k (𝟙 Gₘ)) at h
  rw [reducedTorusGraphSection_pullback, Category.comp_id] at h
  rw [h]
  let chart := NativeTorusPolynomial.torusFieldChart (k := k)
  let : IsAffine (Gₘ).left := IsAffine.of_isIso chart.inv
  let : IsIntegral (Gₘ).left := IsIntegral.of_isIso chart.hom
  have hn := reducedNorm_reducedTorusGraphSection k (𝟙 Gₘ)
  change (reducedNorm k).app (op Gₘ) (reducedTorusGraphSection k (𝟙 Gₘ)) =
    (largeUnitsPresheaf Sₖ).map (𝟙 Gₘ).op (torusCoordinateUnitSection k) at hn
  rw [hn, op_id]
  exact ConcreteCategory.congr_hom ((largeUnitsPresheaf Sₖ).map_id (op Gₘ))
    (torusCoordinateUnitSection k)

local notation "T" => CochainComplex.singleFunctor (TorusSheaves k) 0

private abbrev unitsComparison : (L).extend e ⟶ (T).obj Uₖ :=
  HomologicalComplex.extendMap (weightOneSheafChainComparison k) e ≫
    (HomologicalComplex.extendSingleIso e Uₖ 0 0 rfl).hom

/-- The literal relative graph represents a cochain map in unshifted degree zero. -/
@[no_expose]
def torusCoordinateGraphCochain : (T).obj (TorusSource k) ⟶ (L).extend e :=
  HomologicalComplex.mkHomFromSingle
    (torusCoordinateRelativeGraph k ≫ ((L).extendXIso e (i := 0) (i' := 0) rfl).inv)
    (fun i hi => by
      have h : ∀ j, (ComplexShape.embeddingUpIntLE 0).f j ≠ i := by
        intro j hj
        change (0 : ℤ) - j = i at hj
        change (0 : ℤ) + 1 = i at hi
        omega
      exact ((L).isZero_extend_X e i h).eq_of_tgt _ _)

private theorem torusCoordinateGraphCochain_comp_unitsComparison :
    torusCoordinateGraphCochain k ≫ unitsComparison k =
      (T).map (torusCoordinateRelativeUnit k) := by
  apply HomologicalComplex.from_single_hom_ext
  have h := HomologicalComplex.extendMap_f (weightOneSheafChainComparison k)
    e (i := 0) (i' := 0) rfl
  simp only [torusCoordinateGraphCochain, unitsComparison, HomologicalComplex.comp_f,
    HomologicalComplex.mkHomFromSingle_f, h, HomologicalComplex.extendSingleIso_hom_f,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (torusCoordinateRelativeGraph k) ((weightOneSheafChainComparison k).f 0),
    ← Category.assoc (torusCoordinateRelativeGraph k ≫ (weightOneSheafChainComparison k).f 0)]
  simp only [Category.assoc, torusCoordinateRelativeGraph_comp_unitsProjection_assoc]
  exact (HomologicalComplex.single_map_f_self (.up ℤ) 0 (torusCoordinateRelativeUnit k)).symm

section Derived

variable [HasDerivedCategory.{d} (TorusSheaves k)]

local notation "D" => DerivedCategory (TorusSheaves k)
local notation "S" => shiftFunctor D (1 : ℤ)
local notation "K" => motivicSheafComplex k 1

private def cancelDerivedPlacement (M : CochainComplex (TorusSheaves k) ℤ) :
    (DerivedCategory.Q.obj (M⟦(-1 : ℤ)⟧))⟦(1 : ℤ)⟧ ≅ DerivedCategory.Q.obj M :=
  hypercohomologyShiftTargetIso.{d, u + 1} Jₖ M (-1) 1 ≪≫
    (shiftFunctorZero (DerivedCategory (TorusSheaves k)) ℤ).app (DerivedCategory.Q.obj M)

private theorem cancelDerivedPlacement_naturality {M N : CochainComplex (TorusSheaves k) ℤ}
    (f : M ⟶ N) :
    (S).map (DerivedCategory.Q.map (f⟦(-1 : ℤ)⟧')) ≫ (cancelDerivedPlacement k N).hom =
      (cancelDerivedPlacement k M).hom ≫ DerivedCategory.Q.map f := by
  let s := S
  let t := shiftFunctor (DerivedCategory (TorusSheaves k)) (-1 : ℤ)
  let Q : CochainComplex (TorusSheaves k) ℤ ⥤ D := DerivedCategory.Q
  let a := Q.commShiftIso (-1 : ℤ)
  let b := shiftFunctorAdd (DerivedCategory (TorusSheaves k)) (-1 : ℤ) 1
  let z := shiftFunctorZero (DerivedCategory (TorusSheaves k)) ℤ
  let s₀ := shiftFunctor D (0 : ℤ)
  have ha : Q.map (f⟦(-1 : ℤ)⟧') ≫ a.hom.app N = a.hom.app M ≫ t.map (Q.map f) :=
    a.hom.naturality f
  have hb : s.map (t.map (Q.map f)) ≫ b.inv.app (Q.obj N) =
      b.inv.app (Q.obj M) ≫ s₀.map (Q.map f) :=
    b.inv.naturality (Q.map f)
  have hz : s₀.map (Q.map f) ≫ z.hom.app (Q.obj N) =
      z.hom.app (Q.obj M) ≫ Q.map f := z.hom.naturality (Q.map f)
  change s.map (Q.map (f⟦(-1 : ℤ)⟧')) ≫
      (s.map (a.hom.app N) ≫ b.inv.app (Q.obj N)) ≫ z.hom.app (Q.obj N) =
    ((s.map (a.hom.app M) ≫ b.inv.app (Q.obj M)) ≫ z.hom.app (Q.obj M)) ≫ Q.map f
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  rw [ha, Functor.map_comp, Category.assoc, reassoc_of% hb, hz]

/-- The ordinary signed placement of the singular complex, shifted back to degree zero. -/
@[no_expose]
def coordinatePlacementIso :
    (DerivedCategory.Q.obj K)⟦(1 : ℤ)⟧ ≅ DerivedCategory.Q.obj ((L).extend e) :=
  (S).mapIso (DerivedCategory.Q.mapIso (motivicSheafComplexOrdinaryShiftIso k 1)) ≪≫
    cancelDerivedPlacement k ((L).extend e)

/-- The cochain representative of the original reduced coordinate class
is the zero-simplex relative identity graph. -/
theorem torusCoordinateReducedMotivicClass_eq_graphCochain :
    torusCoordinateReducedMotivicClass.{d} k =
      (torusReducedDerivedChainsIso.{d} k).hom ≫
        (DerivedCategory.singleFunctorIsoCompQ.{d} (TorusSheaves k) 0).hom.app (TorusSource k) ≫
        DerivedCategory.Q.map (torusCoordinateGraphCochain k) ≫ (coordinatePlacementIso k).inv := by
  let i := (torusReducedDerivedChainsIso.{d} k).hom
  let j := (DerivedCategory.singleFunctorIsoCompQ.{d} (TorusSheaves k) 0)
  let g := torusCoordinateGraphCochain k
  let a := unitsComparison k
  let b := coordinatePlacementIso k
  let x := torusCoordinateRelativeUnit k
  let ν := weightOneDerivedUnitsIso.{d} k
  have hb : b.hom ≫ DerivedCategory.Q.map a ≫ j.inv.app Uₖ = ν.hom := by
    let c := (motivicSheafComplexOrdinaryShiftIso k 1).hom
    have hn := cancelDerivedPlacement_naturality k a
    have he : (weightOneDerivedUnitsIso.{d} k).hom =
        (S).map (DerivedCategory.Q.map (weightOneSheafComparison k)) ≫
          (cancelDerivedPlacement k ((T).obj Uₖ)).hom ≫ j.inv.app Uₖ := by
      simp only [weightOneDerivedUnitsIso, cancelDerivedPlacement, Iso.trans_hom,
        Functor.mapIso_hom, asIso_hom, Iso.symm_hom, Category.assoc]
      rfl
    have hb' : b.hom =
        (S).map (DerivedCategory.Q.map c) ≫ (cancelDerivedPlacement k ((L).extend e)).hom := by
      simp only [b, coordinatePlacementIso, Iso.trans_hom, Functor.mapIso_hom]
      rfl
    change b.hom ≫ DerivedCategory.Q.map a ≫ j.inv.app Uₖ =
      (weightOneDerivedUnitsIso.{d} k).hom
    rw [hb', Category.assoc, he]
    have hc : weightOneSheafComparison k = c ≫ a⟦(-1 : ℤ)⟧' := rfl
    rw [hc]
    simp only [Category.assoc, DerivedCategory.Q.map_comp, (S).map_comp, reassoc_of% hn]
  apply (cancel_mono ν.hom).mp
  rw [torusCoordinateReducedMotivicClass_comp_weightOneDerivedUnitsIso]
  have hn : (DerivedCategory.singleFunctor.{d} (TorusSheaves k) 0).map x ≫ j.hom.app Uₖ =
      j.hom.app (TorusSource k) ≫ DerivedCategory.Q.map ((T).map x) :=
    j.hom.naturality x
  change i ≫ (DerivedCategory.singleFunctor.{d} (TorusSheaves k) 0).map x =
    (i ≫ j.hom.app (TorusSource k) ≫ DerivedCategory.Q.map g ≫ b.inv) ≫ ν.hom
  rw [← hb]
  have hg : g ≫ a = (T).map x := torusCoordinateGraphCochain_comp_unitsComparison k
  have h := congrArg (fun f => i ≫ f ≫ j.inv.app Uₖ) hn
  rw [Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
    ← DerivedCategory.Q.map_comp_assoc, hg]
  have hj := j.hom_inv_id_app Uₖ
  simpa only [Category.assoc, hj, Category.comp_id] using
    (show (i ≫ (DerivedCategory.singleFunctor.{d} (TorusSheaves k) 0).map x) ≫
        (j.hom.app Uₖ ≫ j.inv.app Uₖ) = _ from by
      simpa only [Category.assoc] using h)

end Derived

end AlgebraicGeometry.MotivicHomotopy

attribute [colib_tag "COL-1034"]
  AlgebraicGeometry.MotivicHomotopy.torusCoordinateReducedMotivicClass_eq_graphCochain
