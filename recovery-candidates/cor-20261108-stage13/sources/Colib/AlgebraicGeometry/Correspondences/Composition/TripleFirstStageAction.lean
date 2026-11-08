/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleOriginalMiddleLists
public import Colib.RingTheory.Koszul.Coefficients
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Colon

/-!
# The actual first-incidence local ring acts on first Koszul homology

The full first-stage incidence times the third support is cut out in the actual sixfold
ambient by the first diagonal ideal plus the exterior coefficient ideal. The original
stalk map identifies this quotient with its full local ring, retaining nilpotents.
Both ideals annihilate first-stage coefficient Koszul homology: the diagonal ideal by
native Tor/Koszul comparison, and the exterior ideal by the existing coefficient-annihilator
theorem. Mathlib's quotient-module action therefore gives an action of that actual local ring.
The equation on every ambient scalar proves that restriction recovers the original action.

This is the ring action required for remaining-diagonal Euler devissage. It neither assumes
an action comparison nor identifies the resulting Euler weights with finite-image coefficients.
The native quotient action is `Module.IsTorsionBySet.module`; no tensor model is replaced.
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
theorem correspondenceTripleIncidence_firstStage_point_eq
    (x : correspondenceTripleIncidence f g h i z w v) :
    correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x =
      correspondenceLeftIntermediateAmbientInclusion f g h i z w v
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x) := by
  have hw := congrArg (· ≫ correspondenceFirstDiagonalInclusion f g h i)
    (correspondenceTripleIncidence_firstDiagonal_isPullback f g h i z w v).w
  simpa only [Category.assoc, Scheme.Hom.comp_apply] using congrArg (fun m => m x) hw

/-- The original sixfold-to-first-stage stalk map, transported only along equal actual images. -/
def correspondenceTripleIncidenceFirstStageStalkMap
    (x : correspondenceTripleIncidence f g h i z w v) :
    correspondenceTripleIncidenceAmbientStalk f g h i z w v x →+*
      (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x) :=
  (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_firstStage_point_eq f g h i z w v x))).hom ≫
      (correspondenceLeftIntermediateAmbientInclusion f g h i z w v).stalkMap
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x)).hom

/-- The actual first-stage stalk kernel: first diagonal plus full exterior coefficient support. -/
def correspondenceTripleIncidenceFirstStageStalkIdeal
    (x : correspondenceTripleIncidence f g h i z w v) :
    Ideal (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) :=
  let p := correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x
  IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker p ⊔
    IdealSheafData.stalk (correspondenceTripleSupportProductInclusion f g h i z w v).ker p

/-- The first-stage stalk kernel is the exact ideal sum, with no radical. -/
theorem correspondenceTripleIncidenceFirstStageStalkMap_ker [IsSeparated g]
    (x : correspondenceTripleIncidence f g h i z w v) :
    RingHom.ker (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x) =
      correspondenceTripleIncidenceFirstStageStalkIdeal f g h i z w v x := by
  rw [correspondenceTripleIncidenceFirstStageStalkMap, ker_transport_stalkMap,
    correspondenceLeftIntermediateAmbientInclusion_ker, IdealSheafData.stalk_sup]
  rfl

/-- The genuine first-stage stalk map is surjective. -/
theorem correspondenceTripleIncidenceFirstStageStalkMap_surjective [IsSeparated g]
    (x : correspondenceTripleIncidence f g h i z w v) :
    Function.Surjective (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x) :=
  (SurjectiveOnStalks.stalkMap_surjective
    (correspondenceLeftIntermediateAmbientInclusion f g h i z w v)
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x)).comp
    (ConcreteCategory.bijective_of_isIso
      ((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
        (Inseparable.of_eq
          (correspondenceTripleIncidence_firstStage_point_eq f g h i z w v x))).hom).2

/-- The exact first-stage ideal quotient is the full original first-stage local ring. -/
def correspondenceTripleIncidenceFirstStageStalkQuotientEquiv [IsSeparated g]
    (x : correspondenceTripleIncidence f g h i z w v) :
    (correspondenceTripleIncidenceAmbientStalk f g h i z w v x ⧸
      correspondenceTripleIncidenceFirstStageStalkIdeal f g h i z w v x) ≃+*
        (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x) :=
  (Ideal.quotEquivOfEq
    (correspondenceTripleIncidenceFirstStageStalkMap_ker f g h i z w v x).symm).trans
      (RingHom.quotientKerEquivOfSurjective
        (correspondenceTripleIncidenceFirstStageStalkMap_surjective f g h i z w v x))

/-- The first-stage quotient comparison retains the original map on every ambient germ. -/
@[simp]
theorem correspondenceTripleIncidenceFirstStageStalkQuotientEquiv_mk [IsSeparated g]
    (x : correspondenceTripleIncidence f g h i z w v)
    (a : correspondenceTripleIncidenceAmbientStalk f g h i z w v x) :
    correspondenceTripleIncidenceFirstStageStalkQuotientEquiv f g h i z w v x
      (Ideal.Quotient.mk _ a) =
        correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x a := by
  rfl

/-- The full exterior stalk's actual ambient annihilator is its original support ideal stalk. -/
theorem correspondenceTripleIncidenceSupportStalkModule_annihilator
    (x : correspondenceTripleIncidence f g h i z w v) :
    Module.annihilator (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x) =
        IdealSheafData.stalk (correspondenceTripleSupportProductInclusion f g h i z w v).ker
          (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) := by
  let φ := (((correspondenceSixfoldAmbient f g h i).presheaf.stalkCongr
    (Inseparable.of_eq (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x))).hom ≫
      (correspondenceTripleSupportProductInclusion f g h i z w v).stalkMap
        (correspondenceTripleIncidenceToTripleSupport f g h i z w v x)).hom
  have hk : RingHom.ker φ = _ := ker_transport_stalkMap
    (correspondenceTripleSupportProductInclusion f g h i z w v)
    (correspondenceTripleIncidenceToTripleSupport f g h i z w v x)
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x)
    (correspondenceTripleIncidence_ambient_point_eq f g h i z w v x)
  rw [← hk]
  ext a
  rw [Module.mem_annihilator, RingHom.mem_ker]
  change (∀ b, φ a * b = 0) ↔ φ a = 0
  constructor
  · intro ha
    simpa using ha 1
  · intro ha b
    rw [ha, zero_mul]

/-- Both actual first-stage defining ideals annihilate every first Koszul homology module. -/
theorem correspondenceTripleIncidenceFirstStageStalkIdeal_le_annihilator
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) :
    correspondenceTripleIncidenceFirstStageStalkIdeal f g h i z w v x ≤
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
def correspondenceTripleIncidenceFirstKoszulModule [IsSeparated g]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) :
    Module ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x))
      ((Koszul.seqComplexTensor t.get
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n) := by
  have hkill := Module.isTorsionBySet_iff_subset_annihilator.mpr
    (correspondenceTripleIncidenceFirstStageStalkIdeal_le_annihilator f g h i z w v x t hr ht n)
  letI := hkill.module
  exact Module.compHom _
    (correspondenceTripleIncidenceFirstStageStalkQuotientEquiv f g h i z w v x).symm.toRingHom

/-- Restricting the first-stage action recovers the original sixfold scalar action exactly. -/
theorem correspondenceTripleIncidenceFirstKoszulModule_stalkMap_smul [IsSeparated g]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) (a : correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
    (m : (Koszul.seqComplexTensor t.get
      (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n) :
    letI := correspondenceTripleIncidenceFirstKoszulModule f g h i z w v x t hr ht n
    correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x a • m = a • m := by
  let hkill := Module.isTorsionBySet_iff_subset_annihilator.mpr
    (correspondenceTripleIncidenceFirstStageStalkIdeal_le_annihilator f g h i z w v x t hr ht n)
  letI := hkill.module
  change (correspondenceTripleIncidenceFirstStageStalkQuotientEquiv
    f g h i z w v x).symm
      (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x a) • m = a • m
  rw [← correspondenceTripleIncidenceFirstStageStalkQuotientEquiv_mk,
    RingEquiv.symm_apply_apply]
  rfl

/-- The recovered scalar action is an actual tower over the original first-stage stalk map. -/
def correspondenceTripleIncidenceFirstKoszulScalarTower [IsSeparated g]
    (x : correspondenceTripleIncidence f g h i z w v)
    (t : List (correspondenceTripleIncidenceAmbientStalk f g h i z w v x))
    (hr : RingTheory.Sequence.IsRegular
      (correspondenceTripleIncidenceAmbientStalk f g h i z w v x) t)
    (ht : IdealSheafData.stalk (correspondenceFirstDiagonalInclusion f g h i).ker
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v x) = Ideal.ofList t)
    (n : ℕ) :
    letI := correspondenceTripleIncidenceFirstKoszulModule f g h i z w v x t hr ht n
    letI := (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x).toAlgebra
    IsScalarTower (correspondenceTripleIncidenceAmbientStalk f g h i z w v x)
      ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v x))
      ((Koszul.seqComplexTensor t.get
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v x)).homology n) := by
  letI := correspondenceTripleIncidenceFirstKoszulModule f g h i z w v x t hr ht n
  letI := (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x).toAlgebra
  refine ⟨fun a b m => ?_⟩
  change (correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v x a * b) • m =
    a • (b • m)
  rw [mul_smul, correspondenceTripleIncidenceFirstKoszulModule_stalkMap_smul]

end Stacks.Chow
