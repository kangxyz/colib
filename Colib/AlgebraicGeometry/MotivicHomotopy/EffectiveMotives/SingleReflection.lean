/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.InvariantUnit
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.NisnevichReflection
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.SingleCoproduct
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalSingle

/-!
# Reflection of a single transfer coefficient

The original signed singular motive of a presheaf is the effective
reflection of its sheafification placed in degree zero. The comparison
preserves the given singular augmentation.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "a" => nisnevichSheafify k
local notation "D" => DerivedCategory.Minus.ι
local notation "E" => effectiveMotivesMinusToDerived k
local notation "Sₚ" => CochainComplex.singleFunctor PST 0

/-- The original single presheaf coefficient and its sheafified single
derived coefficient have the standard exact-functor comparison. -/
def sheafificationSingleIso (P : PST) :
    (D).obj ((derivedNisnevichSheafification k).obj
      (singularPresheafDerivedCochainObj k ((Sₚ).obj P) 0)) ≅
      (DerivedCategory.singleFunctor NST 0).obj ((a).obj P) :=
  (a).mapDerivedCategory.mapIso (singularPresheafDerivedCochainToQIso k ((Sₚ).obj P) 0) ≪≫
    ((a).mapDerivedCategoryFactors.app ((Sₚ).obj P)) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (a) (.up ℤ) 0).app P)

omit [PerfectField k]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The forward comparison retains the three original maps of exact sheafification. -/
theorem sheafificationSingleIso_hom (P : PST) :
    (sheafificationSingleIso k P).hom =
      (a).mapDerivedCategory.map
        (singularPresheafDerivedCochainToQIso k ((Sₚ).obj P) 0).hom ≫
      (a).mapDerivedCategoryFactors.hom.app ((Sₚ).obj P) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (a) (.up ℤ) 0).hom.app P) := by
  unfold sheafificationSingleIso
  rfl

private def singularPresheafToEffectiveSingleIso (P : PST) :
    (singularPresheafToEffective k).obj
      (singularPresheafDerivedCochainObj k ((Sₚ).obj P) 0) ≅
        (singularEffectiveMotiveFunctor k).obj P := by
  let K := (Sₚ).obj P
  let L := (singularTotalFunctor k).obj K
  let : L.IsStrictlyLE 0 := singularTotalFunctor_obj_isStrictlyLE k K 0
  let e := (D).mapIso (singularPresheafDerivedCochainIso k K 0) ≪≫
    singularPresheafDerivedCochainToQIso k L 0
  let z := (a).mapDerivedCategory.mapIso e ≪≫ ((a).mapDerivedCategoryFactors.app L) ≪≫
    DerivedCategory.Q.mapIso (((a).mapHomologicalComplex (.up ℤ)).mapIso
      (singularTotalSingleZeroIso P))
  exact (Functor.FullyFaithful.ofFullyFaithful (E)).preimageIso z

/-- The actual degree-zero effective reflection is the original singular motive. -/
def sheafificationEffectiveReflectionSingleIso (P : PST) :
    (effectiveReflection k).obj ((derivedNisnevichSheafification k).obj
      (singularPresheafDerivedCochainObj k ((Sₚ).obj P) 0)) ≅
        (singularEffectiveMotiveFunctor k).obj P :=
  (sheafificationEffectiveReflectionIso k).app
    (singularPresheafDerivedCochainObj k ((Sₚ).obj P) 0) ≪≫
      singularPresheafToEffectiveSingleIso k P

/-- The comparison retains the literal original augmentation from the sheaf coefficient. -/
@[reassoc]
theorem sheafificationEffectiveReflectionSingleIso_unit (P : PST) :
    (D).map ((effectiveReflectionAdjunction k).unit.app ((derivedNisnevichSheafification k).obj
      (singularPresheafDerivedCochainObj k ((Sₚ).obj P) 0))) ≫
      (E).map (sheafificationEffectiveReflectionSingleIso k P).hom =
        (sheafificationSingleIso k P).hom ≫ singularDerivedUnitApp k P := by
  let K := (Sₚ).obj P
  let L := (singularTotalFunctor k).obj K
  let : L.IsStrictlyLE 0 := singularTotalFunctor_obj_isStrictlyLE k K 0
  let X := singularPresheafDerivedCochainObj k K 0
  let h := (singularPresheafDerivedUnit k).app X
  let d := singularPresheafDerivedCochainIso k K 0
  let z := (singularTotalSingleZeroIso P).hom
  let F := (a).mapDerivedCategory
  let A := (a).mapHomologicalComplex (.up ℤ)
  let t := (a).mapDerivedCategoryFactors
  let e := singularPresheafDerivedCochainToQIso k K 0
  let e' := singularPresheafDerivedCochainToQIso k L 0
  let Q := DerivedCategory.Q (C := NST)
  let s := (HomologicalComplex.singleMapHomologicalComplex (a) (.up ℤ) 0).app P
  have hu : (D).map h ≫ (D).map d.hom ≫ e'.hom =
      e.hom ≫ DerivedCategory.Q.map (singularTotalUnitApp k K) := by
    rw [← Functor.map_comp_assoc, singularPresheafDerivedCochainIso_unit]
    exact singularPresheafDerivedCochainToQIso_naturality k (singularTotalUnitApp k K) 0 0
  have ht : F.map ((D).map h) ≫ F.map ((D).map d.hom ≫ e'.hom) ≫ t.hom.app L ≫
      Q.map (A.map z) =
    F.map e.hom ≫ t.hom.app K ≫ Q.map (A.map (singularCochainUnitApp P)) := by
    let u := singularTotalUnitApp k K
    have ht' : F.map (DerivedCategory.Q.map u) ≫ t.hom.app L =
        t.hom.app K ≫ Q.map (A.map u) := t.hom.naturality u
    rw [← F.map_comp_assoc, hu, F.map_comp, Category.assoc]
    calc
      _ = F.map e.hom ≫ (F.map (DerivedCategory.Q.map u) ≫ t.hom.app L) ≫ Q.map (A.map z) :=
        congrArg (F.map e.hom ≫ ·) (Category.assoc _ _ _).symm
      _ = F.map e.hom ≫ (t.hom.app K ≫ Q.map (A.map u)) ≫ Q.map (A.map z) :=
        congrArg (fun m => F.map e.hom ≫ m ≫ Q.map (A.map z)) ht'
      _ = _ := by
        rw [Category.assoc, ← Q.map_comp, ← A.map_comp, singularTotalSingleZeroIso_unit]
  have hA := sheafificationEffectiveReflectionIso_hom_unit k X
  let V : DerivedCategory.Minus NST ⥤ DerivedCategory NST := DerivedCategory.Minus.ι
  have hA' : V.map ((effectiveReflectionAdjunction k).unit.app
        ((derivedNisnevichSheafification k).obj X)) ≫
      (E).map ((sheafificationEffectiveReflectionIso k).hom.app X) =
        F.map ((D).map h) := by
    have he := V.congr_map hA
    rw [V.map_comp] at he
    change _ = V.map (𝟙 _ ≫ (derivedNisnevichSheafification k).map h) at he
    rw [Category.id_comp] at he
    exact he
  have ha : (E).map (singularPresheafToEffectiveSingleIso k P).hom =
      F.map ((D).map d.hom ≫ e'.hom) ≫ t.hom.app L ≫ Q.map (A.map z) := by
    let Z : (E).obj ((singularPresheafToEffective k).obj X) ≅
        (E).obj ((singularEffectiveMotiveFunctor k).obj P) :=
      F.mapIso ((D).mapIso d ≪≫ e') ≪≫ t.app L ≪≫ Q.mapIso (A.mapIso
        (singularTotalSingleZeroIso P))
    let f := Functor.FullyFaithful.ofFullyFaithful (E)
    change (E).map (f.preimage Z.hom) = Z.hom
    exact f.map_preimage Z.hom
  let q := Q.map (A.map (singularCochainUnitApp P))
  calc
    _ = (V.map ((effectiveReflectionAdjunction k).unit.app
        ((derivedNisnevichSheafification k).obj X)) ≫
          (E).map ((sheafificationEffectiveReflectionIso k).hom.app X)) ≫
            (E).map (singularPresheafToEffectiveSingleIso k P).hom := by
      rw [show (sheafificationEffectiveReflectionSingleIso k P).hom =
        (sheafificationEffectiveReflectionIso k).hom.app X ≫
          (singularPresheafToEffectiveSingleIso k P).hom from rfl,
        (E).map_comp]
      exact (Category.assoc _ _ _).symm
    _ = F.map ((D).map h) ≫ (E).map (singularPresheafToEffectiveSingleIso k P).hom :=
      congrArg (· ≫ (E).map (singularPresheafToEffectiveSingleIso k P).hom) hA'
    _ = F.map e.hom ≫ t.hom.app K ≫ q :=
      (congrArg (F.map ((D).map h) ≫ ·) ha).trans ht
    _ = _ := by
      change F.map e.hom ≫ t.hom.app K ≫ q =
        (F.map e.hom ≫ t.hom.app K ≫ Q.map s.hom) ≫
          𝟙 _ ≫ Q.map (s.inv ≫ A.map (singularCochainUnitApp P))
      have hs : Q.map s.hom ≫ Q.map (s.inv ≫ A.map (singularCochainUnitApp P)) = q := by
        rw [← Q.map_comp, Iso.hom_inv_id_assoc]
      rw [Category.id_comp, Category.assoc, Category.assoc, hs]

end AlgebraicGeometry.MotivicHomotopy
