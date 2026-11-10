/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.RemainingDiagonal
public import Colib.AlgebraicGeometry.Correspondences.Exterior.CoefficientAmbient
public import Colib.AlgebraicGeometry.Correspondences.Exterior.QuotientIncidence
public import Colib.AlgebraicGeometry.Correspondences.Exterior.ParameterStalkQuotient
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.RegularOpenIndependence

/-!
# One remaining Y-diagonal family at the actual native incidence

SOURCE ONLY, UNCOMPILED. One list is chosen in the actual Y-diagonal ideal.
Its ambient image is regular and generates the actual remaining ambient kernel.
Its coefficient image is literally the image of the original coefficient list
under the flat parameter-forgetting map. The two coefficient lists generate the
actual incidence kernels, but no coefficient regularity is asserted or assumed.
Thus their Koszul homology, including positive degrees, remains available.

The ambient quotient is the stalk of the actual exterior triple product. The
coefficient quotients are the actual original and exterior incidence stalks.
All maps retain the native point transports; no reduction or radical is taken.

Native inputs are Stacks smooth-section regularity (067R), its actual stalk
kernel generators, public ordered-list flat transport, and ideal-sheaf stalk
base change. Exact pinned source locators are in the separate report.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open AlgebraicGeometry.Scheme

universe u
namespace Stacks.Chow

variable {k : Type u} [Field k] (X Y T : SmoothSite (Spec (.of k)))
  [GeometricallyIntegral T.hom]
  (z : pullback (C := Scheme) X.hom Y.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (Z : SmoothSite (Spec (.of k)))
  (w : pullback (C := Scheme) Y.hom Z.hom)
  (hw : IsFiniteCorrespondencePoint Y.hom Z.hom w)

local notation3 (prettyPrint := false) "f" => (SmoothSite.product X T).hom
local notation3 (prettyPrint := false) "g" => (SmoothSite.product Y T).hom
local notation3 (prettyPrint := false) "h" => (SmoothSite.product Z T).hom
local notation3 (prettyPrint := false) "I'" => nativeExteriorIncidence X Y Z T z w hz hw
local notation3 (prettyPrint := false) "I₀" =>
  correspondenceIncidence X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "P₀" =>
  correspondenceSupportProduct X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "Q" => nativeExteriorParameterDiagonal X Y T z hz Z w hw
local notation3 (prettyPrint := false) "QA" => exteriorAmbientParameterQuotient X Y Z T
local notation3 (prettyPrint := false) "iQ" =>
  nativeExteriorCoefficientQuotientInclusion X Y T z hz Z w hw
local notation3 (prettyPrint := false) "c" =>
  nativeExteriorIncidenceToCoefficientQuotient X Y Z T z w hz hw
local notation3 (prettyPrint := false) "q" =>
  nativeExteriorCoefficientQuotientProjection X Y T z hz Z w hw
local notation3 (prettyPrint := false) "π" => nativeExteriorIncidenceOriginal X Y Z T z w hz hw
local notation3 (prettyPrint := false) "b₀" =>
  correspondenceIncidenceToSupportProduct X.hom Y.hom Z.hom z w
local notation3 (prettyPrint := false) "r₀" => nativeOriginalCoefficientMiddlePair X Y z Z w
local notation3 (prettyPrint := false) "r" => exteriorAmbientRemainingPair X Y Z T
local notation3 (prettyPrint := false) "l" => exteriorAmbientRemainingInclusion X Y Z T
local notation3 (prettyPrint := false) "v" => correspondenceIncidenceInclusion f g h
  (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)
local notation3 (prettyPrint := false) "δ" => pullback.diagonal Y.hom

/-- The actual original incidence is the Y-diagonal inverse image in its support product. -/
theorem nativeOriginalCoefficientDiagonal_isPullback :
    IsPullback
      (correspondenceIncidenceInclusion X.hom Y.hom Z.hom z w ≫
        correspondenceTripleMiddle X.hom Y.hom Z.hom)
      b₀ δ r₀ := by
  let a := exteriorSupportTargetProjection X Y (integralComponentAt z)
  let b := exteriorSupportSourceProjection Y Z (integralComponentAt w)
  let mu := pullback.map (a ≫ Y.hom) (b ≫ Y.hom) Y.hom Y.hom
    a b (𝟙 (Spec (.of k))) (Category.comp_id _) (Category.comp_id _)
  have hmu : mu = nativeOriginalCoefficientMiddlePair X Y z Z w := by
    apply pullback.hom_ext («f» := Y.hom) («g» := Y.hom)
    · simpa only [mu, pullback.map, pullback.lift_fst, a, b] using
        (nativeOriginalCoefficientMiddlePair_fst X Y z Z w).symm
    · simpa only [mu, pullback.map, pullback.lift_snd, a, b] using
        (nativeOriginalCoefficientMiddlePair_snd X Y z Z w).symm
  have htop :
      correspondenceIncidenceInclusion X.hom Y.hom Z.hom z w ≫
        correspondenceTripleMiddle X.hom Y.hom Z.hom =
      pullback.fst a b ≫ a := by
    dsimp only [correspondenceTripleMiddle]
    rw [← Category.assoc, correspondenceIncidenceInclusion_fst, Category.assoc]
  have hs := pullback_map_diagonal_isPullback a b Y.hom
  change IsPullback (pullback.fst a b ≫ a)
    (correspondenceIncidenceToSupportProduct X.hom Y.hom Z.hom z w)
    (pullback.diagonal Y.hom) mu at hs
  rw [hmu, ← htop] at hs
  exact hs

/-- Its kernel is the full diagonal inverse image, not the reduced incidence ideal. -/
theorem nativeOriginalCoefficientDiagonal_ker : (b₀).ker = (δ).ker.comap r₀ := by
  let sq := (nativeOriginalCoefficientDiagonal_isPullback X Y z Z w).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The actual exterior coefficient incidence is the remaining Y-diagonal inverse image. -/
theorem nativeExteriorRemainingCoefficient_isPullback :
    IsPullback
      (π ≫ correspondenceIncidenceInclusion X.hom Y.hom Z.hom z w ≫
        correspondenceTripleMiddle X.hom Y.hom Z.hom)
      c δ (iQ ≫ r) := by
  rw [nativeExteriorCoefficientQuotientInclusion_remainingPair]
  exact (nativeExteriorIncidenceQuotient_isPullback X Y Z T z w hz hw).paste_horiz
    (nativeOriginalCoefficientDiagonal_isPullback X Y z Z w)

/-- The coefficient kernel has the same remaining diagonal ideal through the actual inclusion. -/
theorem nativeExteriorRemainingCoefficient_ker : (c).ker = (δ).ker.comap (iQ ≫ r) := by
  let sq := (nativeExteriorRemainingCoefficient_isPullback X Y T z hz Z w hw).flip
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- The actual incidence maps have the same point in the ambient parameter quotient. -/
@[reassoc]
theorem nativeExteriorRemainingIncidence_ambient : c ≫ iQ = v ≫ l := by
  apply (cancel_mono (exteriorAmbientParameterInclusion X Y Z T)).mp
  simpa only [Category.assoc, nativeExteriorCoefficientQuotientInclusion_ambient,
    nativeExteriorIncidenceToCoefficientQuotient_inclusion_assoc,
    exteriorAmbientRemainingInclusion_parameterInclusion] using
    (correspondenceIncidence_ambient_comm f g h
      (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw)).symm

/-- The true point equality for the ambient quotient stalk. -/
theorem nativeExteriorRemaining_ambientPoint (x : I') : iQ (c x) = l (v x) :=
  congrArg (fun m : I' ⟶ QA => m x)
    (nativeExteriorRemainingIncidence_ambient X Y T z hz Z w hw)

/-- The actual ambient map onto the exterior triple stalk, with only its point equality cast. -/
def nativeExteriorRemainingAmbientStalkMap (x : I') :
    (QA).presheaf.stalk (iQ (c x)) ⟶ (correspondenceTripleProduct f g h).presheaf.stalk (v x) :=
  ((QA).presheaf.stalkCongr
    (.of_eq (nativeExteriorRemaining_ambientPoint X Y T z hz Z w hw x))).hom ≫
      (l).stalkMap (v x)

/-- The ambient source point is the one used by the parameter change-of-rings square. -/
theorem nativeExteriorRemainingAmbientStalkMap_ker (x : I') :
    RingHom.ker (nativeExteriorRemainingAmbientStalkMap X Y T z hz Z w hw x).hom =
      Ideal.map ((r).stalkMap (iQ (c x))).hom
        (IdealSheafData.stalk (δ).ker (r (iQ (c x)))) := by
  have hker : ∀ (a : QA) (e : a = l (v x)),
      RingHom.ker (((QA).presheaf.stalkCongr (.of_eq e)).hom ≫ (l).stalkMap (v x)).hom =
        IdealSheafData.stalk (l).ker a := by
    intro a e
    subst a
    simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] using ker_stalkMap_eq_idealStalk_ker l (v x)
  rw [nativeExteriorRemainingAmbientStalkMap,
    hker _ (nativeExteriorRemaining_ambientPoint X Y T z hz Z w hw x),
    exteriorAmbientRemainingInclusion_ker, IdealSheafData.stalk_comap]

/-- Surjectivity is inherited from the actual closed-immersion stalk map. -/
theorem nativeExteriorRemainingAmbientStalkMap_surjective (x : I') :
    Function.Surjective (nativeExteriorRemainingAmbientStalkMap X Y T z hz Z w hw x).hom := by
  let e := (QA).presheaf.stalkCongr
    (.of_eq (nativeExteriorRemaining_ambientPoint X Y T z hz Z w hw x))
  exact ((l).stalkMap_surjective (v x)).comp e.commRingCatIsoToRingEquiv.surjective

/-- Both actual routes give the same base point for the Y-diagonal equations. -/
theorem nativeExteriorRemaining_basePoint (x : I') : r (iQ (c x)) = r₀ (q (c x)) :=
  congrArg (fun m => m (c x))
    (nativeExteriorCoefficientQuotientInclusion_remainingPair X Y T z hz Z w hw)

/-- The original coefficient action with the precise remaining-diagonal base-point cast. -/
def nativeExteriorRemainingOriginalStalkMap (x : I') :
    (pullback Y.hom Y.hom).presheaf.stalk (r (iQ (c x))) ⟶ (P₀).presheaf.stalk (q (c x)) :=
  ((pullback Y.hom Y.hom).presheaf.stalkCongr
    (.of_eq (nativeExteriorRemaining_basePoint X Y T z hz Z w hw x))).hom ≫
      (r₀).stalkMap (q (c x))

/-- The literal scalar square, including the base-point equality, preserves every equation. -/
theorem nativeExteriorRemaining_stalkSquare (x : I') :
    nativeExteriorRemainingOriginalStalkMap X Y T z hz Z w hw x ≫ (q).stalkMap (c x) =
      (r).stalkMap (iQ (c x)) ≫ (iQ).stalkMap (c x) := by
  simpa only [nativeExteriorRemainingOriginalStalkMap, Scheme.Hom.stalkMap_comp,
    Category.assoc] using
    (Scheme.Hom.stalkMap_congr_hom (iQ ≫ r) (q ≫ r₀)
      (nativeExteriorCoefficientQuotientInclusion_remainingPair X Y T z hz Z w hw) (c x)).symm

/-- The original incidence quotient map at the original point determined by the parameter map. -/
def nativeExteriorRemainingOriginalIncidenceStalkMap (x : I') :
    (P₀).presheaf.stalk (q (c x)) ⟶ (I₀).presheaf.stalk (π x) :=
  ((P₀).presheaf.stalkCongr
    (.of_eq (nativeExteriorIncidenceQuotient_point X Y Z T z w hz hw x).symm)).hom ≫
      (b₀).stalkMap (π x)

/-- The original and exterior incidence quotient maps commute with the actual projection. -/
theorem nativeExteriorRemainingIncidence_stalkSquare (x : I') :
    nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x ≫ (π).stalkMap x =
      (q).stalkMap (c x) ≫ (c).stalkMap x := by
  simpa only [nativeExteriorRemainingOriginalIncidenceStalkMap, Scheme.Hom.stalkMap_comp,
    Category.assoc] using
    (Scheme.Hom.stalkMap_congr_hom (c ≫ q) (π ≫ b₀)
      (nativeExteriorIncidenceToCoefficientQuotient_projection X Y Z T z w hz hw) x).symm

/-- Point transport retains the original full incidence kernel. -/
theorem nativeExteriorRemainingOriginalIncidenceStalkMap_ker (x : I') :
    RingHom.ker (nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x).hom =
      Ideal.map (nativeExteriorRemainingOriginalStalkMap X Y T z hz Z w hw x).hom
        (IdealSheafData.stalk (δ).ker (r (iQ (c x)))) := by
  have hker : ∀ (a : P₀) (e : a = b₀ (π x)),
      RingHom.ker (((P₀).presheaf.stalkCongr (.of_eq e)).hom ≫ (b₀).stalkMap (π x)).hom =
        IdealSheafData.stalk (b₀).ker a := by
    intro a e
    subst a
    simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] using ker_stalkMap_eq_idealStalk_ker b₀ (π x)
  rw [nativeExteriorRemainingOriginalIncidenceStalkMap,
    hker _ (nativeExteriorIncidenceQuotient_point X Y Z T z w hz hw x).symm]
  have hmap : ∀ (a : pullback (C := Scheme) Y.hom Y.hom) (e : a = r₀ (q (c x))),
      IdealSheafData.stalk (b₀).ker (q (c x)) =
        Ideal.map (((pullback Y.hom Y.hom).presheaf.stalkCongr (.of_eq e)).hom ≫
          (r₀).stalkMap (q (c x))).hom (IdealSheafData.stalk (δ).ker a) := by
    intro a e
    subst a
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp]
    rw [nativeOriginalCoefficientDiagonal_ker, IdealSheafData.stalk_comap]
  exact hmap _ (nativeExteriorRemaining_basePoint X Y T z hz Z w hw x)

/-- The actual original incidence map is still onto after its point identification. -/
theorem nativeExteriorRemainingOriginalIncidenceStalkMap_surjective (x : I') :
    Function.Surjective
      (nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x).hom := by
  let e := (P₀).presheaf.stalkCongr
    (.of_eq (nativeExteriorIncidenceQuotient_point X Y Z T z w hz hw x).symm)
  exact ((b₀).stalkMap_surjective (π x)).comp e.commRingCatIsoToRingEquiv.surjective

/-- One chosen Y-diagonal list and its actual ambient image.
There is deliberately no field asserting coefficient regularity. -/
structure NativeExteriorRemainingStalkFamily (x : I') where
  /-- The only chosen list, in the original Y self-product stalk. -/
  baseList : List ((pullback Y.hom Y.hom).presheaf.stalk (r (iQ (c x))))
  /-- Smoothness of Y supplies regularity of the diagonal list. -/
  base_regular : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk (r (iQ (c x)))) baseList
  /-- Generation of the full Y-diagonal ideal, with no radical. -/
  base_ideal : Ideal.ofList baseList = IdealSheafData.stalk (δ).ker (r (iQ (c x)))
  /-- Flat ambient transport preserves this exact ordered list. -/
  ambient_regular : IsRegular ((QA).presheaf.stalk (iQ (c x)))
    (baseList.map ((r).stalkMap (iQ (c x))).hom)
  /-- Its actual quotient is the exterior triple stalk. -/
  ambient_kernel :
    RingHom.ker (nativeExteriorRemainingAmbientStalkMap X Y T z hz Z w hw x).hom =
      Ideal.ofList (baseList.map ((r).stalkMap (iQ (c x))).hom)

/-- Construct the actual family; no common-list or regular-coefficient assumption is an input. -/
def nativeExteriorRemainingStalkFamily (x : I') :
    NativeExteriorRemainingStalkFamily X Y T z hz Z w hw x := by
  classical
  let y := pullback.fst Y.hom T.hom (correspondenceTripleMiddle f g h (v x))
  have hy : r (iQ (c x)) = δ y := by
    rw [nativeExteriorRemaining_ambientPoint]
    exact (congrArg (fun m => m (v x))
      (exteriorAmbientRemaining_isPullback X Y Z T).w).symm
  have hex : ∃ s : List ((pullback Y.hom Y.hom).presheaf.stalk (r (iQ (c x)))),
      IsRegular ((pullback Y.hom Y.hom).presheaf.stalk (r (iQ (c x)))) s ∧
        Ideal.ofList s = IdealSheafData.stalk (δ).ker (r (iQ (c x))) := by
    rw [hy]
    obtain ⟨s, hs, hk⟩ :=
      Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_isRegular_ker_stalkMap_of_isRegularImmersion
        δ (Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section
          (pullback.fst Y.hom Y.hom) δ (pullback.diagonal_fst Y.hom)) y
    exact ⟨s, hs, hk.trans (ker_stalkMap_eq_idealStalk_ker δ y)⟩
  let s := Classical.choose hex
  have hs := (Classical.choose_spec hex).1
  have hk := (Classical.choose_spec hex).2
  have hweak : IsWeaklyRegular ((QA).presheaf.stalk (iQ (c x)))
      (s.map ((r).stalkMap (iQ (c x))).hom) :=
    Stacks.AlgebraicGeometry.isWeaklyRegular_map_of_flat
      ((r).stalkMap (iQ (c x))).hom (Flat.stalkMap r _) hs.toIsWeaklyRegular
  have hker :
      RingHom.ker (nativeExteriorRemainingAmbientStalkMap X Y T z hz Z w hw x).hom =
        Ideal.ofList (s.map ((r).stalkMap (iQ (c x))).hom) := by
    rw [nativeExteriorRemainingAmbientStalkMap_ker, ← hk, Ideal.map_ofList]
  refine ⟨s, hs, hk, ?_, hker⟩
  refine IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ (fun a ha => ?_) hweak
  apply IsLocalRing.le_maximalIdeal
    (RingHom.ker_ne_top (nativeExteriorRemainingAmbientStalkMap X Y T z hz Z w hw x).hom)
  rw [hker]
  exact Ideal.subset_span ha

namespace NativeExteriorRemainingStalkFamily

variable {X Y T z hz Z w hw}
  {x : nativeExteriorIncidence X Y Z T z w hz hw}
  (F : NativeExteriorRemainingStalkFamily X Y T z hz Z w hw x)

/-- The literal ordered list in the actual ambient parameter-quotient stalk. -/
abbrev ambientList : List ((QA).presheaf.stalk (iQ (c x))) :=
  F.baseList.map ((r).stalkMap (iQ (c x))).hom

/-- The same list on the actual exterior coefficient quotient; it need not be regular. -/
abbrev coefficientList : List ((Q).presheaf.stalk (c x)) :=
  F.ambientList.map ((iQ).stalkMap (c x)).hom

/-- The original coefficient list before flat parameter extension; it need not be regular. -/
abbrev originalCoefficientList : List ((P₀).presheaf.stalk (q (c x))) :=
  F.baseList.map (nativeExteriorRemainingOriginalStalkMap X Y T z hz Z w hw x).hom

/-- The coefficient equation list is the literal image under the actual flat projection. -/
theorem coefficientList_eq_original_image :
    F.coefficientList = F.originalCoefficientList.map ((q).stalkMap (c x)).hom := by
  simp only [coefficientList, ambientList, originalCoefficientList, List.map_map]
  congr 1
  funext a
  exact (ConcreteCategory.congr_hom
    (nativeExteriorRemaining_stalkSquare X Y T z hz Z w hw x) a).symm

/-- The full actual exterior incidence kernel is generated by this coefficient image. -/
theorem coefficient_kernel : RingHom.ker ((c).stalkMap x).hom = Ideal.ofList F.coefficientList := by
  rw [ker_stalkMap_eq_idealStalk_ker, nativeExteriorRemainingCoefficient_ker,
    IdealSheafData.stalk_comap, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    ← Ideal.map_map]
  change Ideal.map ((iQ).stalkMap (c x)).hom
    (Ideal.map ((r).stalkMap (iQ (c x))).hom
      (IdealSheafData.stalk (δ).ker (r (iQ (c x))))) = _
  rw [← F.base_ideal, Ideal.map_ofList, Ideal.map_ofList]

/-- The actual original incidence kernel is generated by the original coefficient list. -/
theorem original_kernel :
    RingHom.ker (nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x).hom =
      Ideal.ofList F.originalCoefficientList := by
  rw [nativeExteriorRemainingOriginalIncidenceStalkMap_ker, ← F.base_ideal, Ideal.map_ofList]

/-- The original and exterior coefficient images have the identical ordered index set. -/
theorem coefficientList_length : F.coefficientList.length = F.originalCoefficientList.length := by
  rw [F.coefficientList_eq_original_image, List.length_map]

/-- The ambient quotient is the actual exterior triple-product local ring. -/
def ambientQuotientEquiv :
    ((QA).presheaf.stalk (iQ (c x)) ⧸ Ideal.ofList F.ambientList) ≃+*
      (correspondenceTripleProduct
        (pullback.fst X.hom T.hom ≫ X.hom)
        (pullback.fst Y.hom T.hom ≫ Y.hom)
        (pullback.fst Z.hom T.hom ≫ Z.hom)).presheaf.stalk
          (correspondenceIncidenceInclusion
            (pullback.fst X.hom T.hom ≫ X.hom)
            (pullback.fst Y.hom T.hom ≫ Y.hom)
            (pullback.fst Z.hom T.hom ≫ Z.hom)
            (nativeExteriorPoint X Y T z hz) (nativeExteriorPoint Y Z T w hw) x) :=
  (Ideal.quotEquivOfEq F.ambient_kernel.symm).trans
    ((nativeExteriorRemainingAmbientStalkMap X Y T z hz Z w hw x).hom.quotientKerEquivOfSurjective
      (nativeExteriorRemainingAmbientStalkMap_surjective X Y T z hz Z w hw x))

/-- The coefficient quotient retains the full exterior incidence local ring. -/
def coefficientQuotientEquiv :
    ((Q).presheaf.stalk (c x) ⧸ Ideal.ofList F.coefficientList) ≃+* (I').presheaf.stalk x :=
  (Ideal.quotEquivOfEq F.coefficient_kernel.symm).trans
    (((c).stalkMap x).hom.quotientKerEquivOfSurjective ((c).stalkMap_surjective x))

/-- The original coefficient quotient retains the full original incidence local ring. -/
def originalQuotientEquiv :
    ((P₀).presheaf.stalk (q (c x)) ⧸ Ideal.ofList F.originalCoefficientList) ≃+*
      (I₀).presheaf.stalk (π x) :=
  (Ideal.quotEquivOfEq F.original_kernel.symm).trans
    ((nativeExteriorRemainingOriginalIncidenceStalkMap
      X Y T z hz Z w hw x).hom.quotientKerEquivOfSurjective
        (nativeExteriorRemainingOriginalIncidenceStalkMap_surjective X Y T z hz Z w hw x))

/-- On every ambient quotient generator the comparison is the actual stalk map. -/
@[simp]
theorem ambientQuotientEquiv_mk (a : (QA).presheaf.stalk (iQ (c x))) :
    F.ambientQuotientEquiv (Ideal.Quotient.mk _ a) =
      (nativeExteriorRemainingAmbientStalkMap X Y T z hz Z w hw x).hom a := by
  simp [ambientQuotientEquiv]

/-- On every exterior coefficient generator the comparison is the actual incidence stalk map. -/
@[simp]
theorem coefficientQuotientEquiv_mk (a : (Q).presheaf.stalk (c x)) :
    F.coefficientQuotientEquiv (Ideal.Quotient.mk _ a) = ((c).stalkMap x).hom a := by
  simp [coefficientQuotientEquiv]

/-- On original coefficient generators the comparison retains its exact point transport. -/
@[simp]
theorem originalQuotientEquiv_mk (a : (P₀).presheaf.stalk (q (c x))) :
    F.originalQuotientEquiv (Ideal.Quotient.mk _ a) =
      (nativeExteriorRemainingOriginalIncidenceStalkMap X Y T z hz Z w hw x).hom a := by
  simp [originalQuotientEquiv]

/-- The two actual quotient comparisons commute on every original coefficient generator. -/
theorem quotient_baseChange_mk (a : (P₀).presheaf.stalk (q (c x))) :
    F.coefficientQuotientEquiv (Ideal.Quotient.mk _ (((q).stalkMap (c x)).hom a)) =
      ((π).stalkMap x).hom (F.originalQuotientEquiv (Ideal.Quotient.mk _ a)) := by
  rw [F.coefficientQuotientEquiv_mk, F.originalQuotientEquiv_mk]
  exact (ConcreteCategory.congr_hom
    (nativeExteriorRemainingIncidence_stalkSquare X Y T z hz Z w hw x) a).symm

end NativeExteriorRemainingStalkFamily

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Products/Diagonal/ExteriorIdentity.lean:128-154"
  "adaptation" "Construct one Y-diagonal regular list and identify its actual ambient \
  remaining kernel; no regularity of the coefficient images is asserted"]
  nativeExteriorRemainingStalkFamily NativeExteriorRemainingStalkFamily.ambientQuotientEquiv

attribute [colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/RemainingPair.lean:121-157"
  "adaptation" "The same remaining equations act through the exact original and exterior \
  coefficient stalk maps, with their point identifications and literal ordered images"]
  nativeExteriorRemaining_stalkSquare
  NativeExteriorRemainingStalkFamily.coefficientList_eq_original_image

end Stacks.Chow
