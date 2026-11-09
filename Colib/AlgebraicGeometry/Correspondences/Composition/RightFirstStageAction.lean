/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightStageGeometry
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleFirstStageAction
public import Colib.RingTheory.Koszul.Coefficients
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Colon

/-!
# The actual right first-stage quotient acts on Z-first Koszul homology

The full right exterior is the intersection of the existing Z-Z-first diagonal
and the unchanged common coefficient support. Its actual stalk map has the sum
of those two ideal stalks as kernel, without reduction. Both ideals annihilate
every coefficient Koszul homology group, by the existing native Tor/Koszul and
coefficient-annihilator suppliers. The native quotient-module construction
therefore gives the literal right-exterior local-ring action.

Restriction along the actual ambient stalk map recovers the original sixfold
action on every element. This is neither an assumed action comparison nor a
transposition of any correspondence. The scalar construction adapts the already
selected TripleFirstStageAction to the genuine Z-first geometric intersection;
the common full support module and its proved annihilator are reused unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

private theorem ker_transport_stalkMap {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsClosedImmersion j] (y : Y) (p : X) (hp : p = j y) :
    RingHom.ker
      ((X.presheaf.stalkCongr (Inseparable.of_eq hp)).hom ≫ j.stalkMap y).hom =
        IdealSheafData.stalk j.ker p := by
  subst p
  simpa [TopCat.Presheaf.stalkCongr] using ker_stalkMap_eq_idealStalk_ker j y

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The original triple point and its first-stage image have the same sixfold image. -/
theorem correspondenceTripleIncidence_rightFirstStage_point_eq
    (x : correspondenceTripleIncidence f g h i z w v) :
    correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x =
      correspondenceRightIntermediateAmbientInclusion f g h i z w v
        (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x) := by
  exact (congrArg (fun m => m x)
    (correspondenceTripleIncidenceToRightSupportProduct_ambient f g h i z w v)).symm

/-- The original sixfold-to-first-stage stalk map, transported only along equal actual images. -/
def correspondenceTripleIncidenceRightFirstStageStalkMap
    (x : correspondenceTripleIncidence f g h i z w v) :
    correspondenceTripleIncidenceAmbientStalk f g h i z w v x →+*
      (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x) :=
  (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (Inseparable.of_eq
      (correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v x))).hom ≫
      (correspondenceRightIntermediateAmbientInclusion f g h i z w v).stalkMap
        (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x)).hom

/-- The actual first-stage stalk kernel: Z-first diagonal plus full exterior coefficient support. -/
def correspondenceTripleIncidenceRightFirstStageStalkIdeal
    (x : correspondenceTripleIncidence f g h i z w v) :
    Ideal (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) :=
  let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
  IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker p ⊔
    IdealSheafData.stalk (correspondenceTripleSupportProductInclusion f g h i z w v).ker p

/-- The first-stage stalk kernel is the exact ideal sum, with no radical. -/
theorem correspondenceTripleIncidenceRightFirstStageStalkMap_ker [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v) :
    RingHom.ker (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x) =
      correspondenceTripleIncidenceRightFirstStageStalkIdeal f g h i z w v x := by
  rw [correspondenceTripleIncidenceRightFirstStageStalkMap,
    ker_transport_stalkMap _ _ _
      (correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v x),
    correspondenceRightIntermediateAmbientInclusion_ker, IdealSheafData.stalk_sup]
  rfl

/-- The genuine first-stage stalk map is surjective. -/
theorem correspondenceTripleIncidenceRightFirstStageStalkMap_surjective [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v) :
    Function.Surjective (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x) :=
  (SurjectiveOnStalks.stalkMap_surjective
    (correspondenceRightIntermediateAmbientInclusion f g h i z w v)
    (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x)).comp
    (ConcreteCategory.bijective_of_isIso
      ((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
        (Inseparable.of_eq
          (correspondenceTripleIncidence_rightFirstStage_point_eq f g h i z w v x))).hom).2

/-- The exact first-stage ideal quotient is the full original first-stage local ring. -/
def correspondenceTripleIncidenceRightFirstStageStalkQuotientEquiv [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v) :
    (correspondenceTripleIncidenceAmbientStalk f g h i z w v x ⧸
      correspondenceTripleIncidenceRightFirstStageStalkIdeal f g h i z w v x) ≃+*
        (correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
          (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x) :=
  (Ideal.quotEquivOfEq
    (correspondenceTripleIncidenceRightFirstStageStalkMap_ker f g h i z w v x).symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (correspondenceTripleIncidenceRightFirstStageStalkMap_surjective f g h i z w v x))

/-- The first-stage quotient comparison retains the original map on every ambient germ. -/
theorem correspondenceTripleIncidenceRightFirstStageStalkQuotientEquiv_mk [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v)
    (a : correspondenceTripleIncidenceAmbientStalk f g h i z w v x) :
    correspondenceTripleIncidenceRightFirstStageStalkQuotientEquiv f g h i z w v x
      (Ideal.Quotient.mk _ a) =
        correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x a := by
  rfl

/-- Both actual first-stage defining ideals annihilate every first Koszul homology module. -/
theorem correspondenceTripleIncidenceRightFirstStageStalkIdeal_le_annihilator
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) :
    correspondenceTripleIncidenceRightFirstStageStalkIdeal f g h i z w v x ≤
      Module.annihilator (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
        ((Koszul.seqComplexTensor t.get
          (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n) := by
  let A := correspondenceTripleIncidenceAmbientStalk f g h i z w v x
  let M := correspondenceTripleIncidenceSupportStalkModule f g h i z w v x
  change _ ⊔ _ ≤ _
  apply sup_le
  · rw [ht]
    intro a ha
    let e := Koszul.torIsoHomologySeqComplexTensorOfIsRegular t.get
      (by simpa only [List.ofFn_get] using hr) (Ideal.ofList t)
      (by rw [← Ideal.ofList_ofFn, List.ofFn_get]) M n
    apply mem_annihilator_of_moduleCat_iso e
    apply mem_annihilator_tor_of_mem_annihilator (ModuleCat.of A (A ⧸ Ideal.ofList t)) M n
    simpa only [Ideal.annihilator_quotient] using ha
  · rw [← correspondenceTripleIncidenceSupportStalkModule_annihilator]
    exact Koszul.annihilator_le_annihilator_seqComplexTensor_homology t.get M n

/-- The literal full first-stage local ring acts on first coefficient Koszul homology. -/
@[instance_reducible]
def correspondenceTripleIncidenceRightFirstKoszulModule [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) :
    Module ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x))
      ((Koszul.seqComplexTensor t.get
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n) := by
  have hkill := (Module.isTorsionBySet_iff_subset_annihilator
    (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
    ((Koszul.seqComplexTensor t.get
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n)).mpr
    (correspondenceTripleIncidenceRightFirstStageStalkIdeal_le_annihilator
      f g h i z w v x t hr ht n)
  letI := hkill.module
  exact Module.compHom _
    (correspondenceTripleIncidenceRightFirstStageStalkQuotientEquiv f g h i z w v x).symm.toRingHom

/-- Restricting the first-stage action recovers the original sixfold scalar action exactly. -/
theorem correspondenceTripleIncidenceRightFirstKoszulModule_stalkMap_smul [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) (a : correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
    (m : (Koszul.seqComplexTensor t.get
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n) :
    let := correspondenceTripleIncidenceRightFirstKoszulModule f g h i z w v x t hr ht n
    correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x a • m = a • m := by
  let hkill := (Module.isTorsionBySet_iff_subset_annihilator
    (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
    ((Koszul.seqComplexTensor t.get
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n)).mpr
    (correspondenceTripleIncidenceRightFirstStageStalkIdeal_le_annihilator
      f g h i z w v x t hr ht n)
  let := hkill.module
  change (correspondenceTripleIncidenceRightFirstStageStalkQuotientEquiv
    f g h i z w v x).symm
      (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x a) • m = a • m
  rw [← correspondenceTripleIncidenceRightFirstStageStalkQuotientEquiv_mk,
    RingEquiv.symm_apply_apply]
  rfl

/-- The recovered scalar action is an actual tower over the original first-stage stalk map. -/
theorem correspondenceTripleIncidenceRightFirstKoszulScalarTower [IsSeparated h]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceSecondAmbientInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) :
    let := correspondenceTripleIncidenceRightFirstKoszulModule f g h i z w v x t hr ht n
    let := (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x).toAlgebra
    IsScalarTower (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
      ((correspondenceRightIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceTripleIncidenceToRightSupportProduct f g h i z w v x))
      ((Koszul.seqComplexTensor t.get
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n) := by
  let := correspondenceTripleIncidenceRightFirstKoszulModule f g h i z w v x t hr ht n
  let := (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x).toAlgebra
  refine ⟨fun a b m => ?_⟩
  change (correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v x a * b) • m =
    a • (b • m)
  rw [mul_smul,
    correspondenceTripleIncidenceRightFirstKoszulModule_stalkMap_smul f g h i z w v x t hr ht n]

end Stacks.Chow
