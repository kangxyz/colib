/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.FieldComparisonMap
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.RawClasses

/-!
# The actual shifted-single homology coordinates in weight one

The canonical shifted-single homology isomorphism sends a represented cycle
to its degree-one component. The native shift comparison has positive middle
component; its negative differential sign does not negate point classes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.MotivicCohomology.WeightOne
open _root_.AlgebraicGeometry.Scheme SmoothSite PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The literal degree-one coordinates of the precise shifted target. -/
def shiftedUnitsBaseXIso : (shiftedUnitsBaseComplex k).X 1 ≅
    (largeUnitsPresheaf (Spec (.of k))).obj (op (base (Spec (.of k)))) := by
  let A := (largeUnitsPresheaf (Spec (.of k))).obj (op (base (Spec (.of k))))
  let K := (CochainComplex.singleFunctor AddCommGrpCat.{u + 1} 0).obj A
  let e₁ : (shiftedUnitsBaseComplex k).X 1 ≅ (K⟦(-1 : ℤ)⟧).X 1 :=
    (HomologicalComplex.eval _ (.up ℤ) 1).mapIso (shiftedUnitsBaseComplexIso k)
  let e₂ : (K⟦(-1 : ℤ)⟧).X 1 ≅ K.X 0 := by
    change ((CochainComplex.shiftFunctor AddCommGrpCat.{u + 1} (-1)).obj K).X 1 ≅ K.X 0
    exact K.shiftFunctorObjXIso (-1) 1 0 (by decide)
  exact e₁ ≪≫ e₂ ≪≫ HomologicalComplex.singleObjXSelf (.up ℤ) 0 A

/-- Evaluation/shift/single coordinates reduce to the original single term coordinate. -/
@[simp] theorem shiftedUnitsBaseXIso_hom :
    (shiftedUnitsBaseXIso k).hom =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0
        (largeUnitsSheaf (Spec (.of k)))).hom.hom.app (op (base (Spec (.of k)))) := by
  let E := (sheafSections (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}).obj
    (op (base (Spec (.of k))))
  let A := largeUnitsSheaf (Spec (.of k))
  change (𝟙 _ ≫ ((HomologicalComplex.singleMapHomologicalComplex E (.up ℤ) 0).app A).hom.f 0) ≫
    𝟙 _ ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (E.obj A)).hom =
      E.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom
  rw [Category.id_comp, Category.id_comp, Iso.app_hom,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The native shift followed by single homology has exactly its degree-one value. -/
private theorem singleShift_homologyπ (A : AddCommGrpCat.{u + 1}) :
    let K := (CochainComplex.singleFunctor AddCommGrpCat.{u + 1} 0).obj A
    (K⟦(-1 : ℤ)⟧).homologyπ 1 ≫
        ((CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1}
          (-1) 1 0 (by decide)).app K).hom ≫
        (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).hom =
      (K⟦(-1 : ℤ)⟧).iCycles 1 ≫
        (K.shiftFunctorObjXIso (-1) 1 0 (by decide)).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom := by
  dsimp only
  let K := (CochainComplex.singleFunctor AddCommGrpCat.{u + 1} 0).obj A
  change (K⟦(-1 : ℤ)⟧).homologyπ 1 ≫
      ((CochainComplex.ShiftSequence.shiftIso AddCommGrpCat.{u + 1}
        (-1) 1 0 (by decide)).app K).hom ≫
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).hom =
    (K⟦(-1 : ℤ)⟧).iCycles 1 ≫
      (K.shiftFunctorObjXIso (-1) 1 0 (by decide)).hom ≫
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom
  have h₀ : (ComplexShape.up ℤ).next 0 = 1 :=
    (ComplexShape.up ℤ).next_eq' (by decide)
  have h₁ : (ComplexShape.up ℤ).next 1 = 2 :=
    (ComplexShape.up ℤ).next_eq' (by decide)
  have h := CochainComplex.liftCycles_shift_homologyπ K
    ((K⟦(-1 : ℤ)⟧).iCycles 1) 2 h₁ ((K⟦(-1 : ℤ)⟧).iCycles_d 1 2)
    0 (by decide) 1 h₀
  have hi : (K⟦(-1 : ℤ)⟧).liftCycles ((K⟦(-1 : ℤ)⟧).iCycles 1)
      2 h₁ ((K⟦(-1 : ℤ)⟧).iCycles_d 1 2) = 𝟙 _ := by
    apply (cancel_mono ((K⟦(-1 : ℤ)⟧).iCycles 1)).mp
    simp only [HomologicalComplex.liftCycles_i, Category.id_comp]
  rw [hi, Category.id_comp] at h
  dsimp only [Functor.shiftIso, Functor.ShiftSequence.shiftIso] at h
  rw [← Iso.app_inv] at h
  rw [h]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  rw [HomologicalComplex.singleObjCyclesSelfIso_hom]
  erw [HomologicalComplex.liftCycles_i_assoc]
  exact Category.assoc _ _ _

/-- On cycles, the fixed target homology comparison is its fixed term comparison. -/
@[reassoc] theorem homologyπ_shiftedUnitsBaseHomologyIso :
    (shiftedUnitsBaseComplex k).homologyπ 1 ≫ (shiftedUnitsBaseHomologyIso k).hom =
      (shiftedUnitsBaseComplex k).iCycles 1 ≫ (shiftedUnitsBaseXIso k).hom := by
  change (shiftedUnitsBaseComplex k).homologyπ 1 ≫
      (HomologicalComplex.homologyMap (shiftedUnitsBaseComplexIso k).hom 1 ≫ _) = _
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality, Category.assoc]
  simp only [Iso.trans_hom]
  erw [singleShift_homologyπ]
  simp only [HomologicalComplex.cyclesMap_i_assoc,
    shiftedUnitsBaseXIso, Iso.trans_hom, Functor.mapIso_hom]
  rfl

/-- The genuine raw class map is computed by the actual degree-one cochain component. -/
@[reassoc] theorem rawClass_rawWeightOneComparison :
    rawClass k ≫ (rawWeightOneHomologyIso k 1).hom ≫
        (shiftedUnitsBaseHomologyIso k).hom =
      (rawWeightOneComparison k).f 1 ≫ (shiftedUnitsBaseXIso k).hom := by
  rw [rawClass, rawWeightOneHomologyIso_hom]
  simp only [Category.assoc, HomologicalComplex.homologyπ_naturality_assoc,
    homologyπ_shiftedUnitsBaseHomologyIso, HomologicalComplex.cyclesMap_i_assoc,
    HomologicalComplex.iCyclesIso_inv_hom_id_assoc]

/-- The fixed norm map reads the same actual degree-one component in ΓSpec coordinates. -/
theorem rawComparisonNorm_rawClass (x : (motivicRawBaseComplex k 1).X 1) :
    rawComparisonNorm k (rawClass k x) =
      ((NativeTorusPolynomial.specUnitsIso (𝟙 (Spec (.of k)))).hom
        ((shiftedUnitsBaseXIso k).hom ((rawWeightOneComparison k).f 1 x))).down := by
  have h := ConcreteCategory.congr_hom (rawClass_rawWeightOneComparison k) x
  change ((NativeTorusPolynomial.specUnitsIso (𝟙 (Spec (.of k)))).hom
    ((shiftedUnitsBaseHomologyIso k).hom
      ((rawWeightOneHomologyIso k 1).hom (rawClass k x)))).down = _
  simpa only [ConcreteCategory.comp_apply] using congrArg
    (fun y => ((NativeTorusPolynomial.specUnitsIso (𝟙 (Spec (.of k)))).hom y).down) h

end AlgebraicGeometry.MotivicCohomology.WeightOne
