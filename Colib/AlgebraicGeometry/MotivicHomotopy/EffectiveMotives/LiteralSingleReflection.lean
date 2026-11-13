/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SingleReflection

/-!
# Effective reflection of the original single complexes

The original degree-zero coefficient, placed either in transfer
presheaves or in transfer sheaves, has the same effective reflection.
Both comparisons retain the given singular augmentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w₁ w₂

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w₁} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w₂} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "V" => DerivedCategory.Minus.ι (C := NST)
local notation "J" => effectiveMotivesMinusToDerived k
local notation "I" => effectiveMotivesMinusInclusion k
local notation "M" => effectiveReflection k
local notation "Q" => singularEffectiveMotiveFunctor k
local notation "A" => nisnevichSheafify k
local notation "a" => derivedNisnevichSheafification k
set_option quotPrecheck false in
local notation "η" => (effectiveReflectionAdjunction k).unit
local notation "sₚ" => CochainComplex.singleFunctor PST 0
local notation "sₛ" => CochainComplex.singleFunctor NST 0

omit [PerfectField k]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private def literalSingleReflectionSourceIso (P : PST) :
    (singleDerivedMinus k 0).obj P ≅
      singularPresheafDerivedCochainObj k ((sₚ).obj P) 0 :=
  (Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.Minus.ι (C := PST))).preimageIso
    (singularPresheafDerivedCochainToQIso k ((sₚ).obj P) 0).symm

/-- The reflection of the original sheafified degree-zero coefficient is
its actual singular effective motive. -/
@[no_expose]
def singleEffectiveReflectionIso (P : PST) :
    (M).obj ((a).obj ((singleDerivedMinus k 0).obj P)) ≅ (Q).obj P :=
  ((a) ⋙ M).mapIso (literalSingleReflectionSourceIso k P) ≪≫
    sheafificationEffectiveReflectionSingleIso k P

/-- The comparison retains the original augmentation of the literal presheaf single. -/
@[reassoc]
theorem singleEffectiveReflectionIso_unit (P : PST) :
    (V).map ((η).app ((a).obj ((singleDerivedMinus k 0).obj P))) ≫
        (J).map (singleEffectiveReflectionIso k P).hom =
      (A).mapDerivedCategoryFactors.hom.app ((sₚ).obj P) ≫
        DerivedCategory.Q.map (((A).mapHomologicalComplex (.up ℤ)).map
          (singularCochainUnitApp P)) := by
  let X := (singleDerivedMinus k 0).obj P
  let K := (sₚ).obj P
  let e := literalSingleReflectionSourceIso k P
  let Y := singularPresheafDerivedCochainObj k K 0
  let d := singularPresheafDerivedCochainToQIso k K 0
  let S := HomologicalComplex.singleMapHomologicalComplex (A) (.up ℤ) (0 : ℤ)
  let Qₛ := DerivedCategory.Q (C := NST)
  let p := sheafificationEffectiveReflectionSingleIso k P
  let E := (A).mapDerivedCategory
  let j := (A).mapDerivedCategoryFactors.hom.app K
  let f := ((a) ⋙ M).map e.hom
  have he : (DerivedCategory.Minus.ι (C := PST)).map e.hom = d.inv := by
    unfold e literalSingleReflectionSourceIso
    exact (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategory.Minus.ι (C := PST))).map_preimage _
  have hn := (V).congr_map ((η).naturality ((a).map e.hom))
  change (V).map ((a).map e.hom ≫ (η).app ((a).obj Y)) =
    (V).map ((η).app ((a).obj X) ≫ (I).map ((M).map ((a).map e.hom))) at hn
  rw [Functor.map_comp, Functor.map_comp] at hn
  change (V).map ((a).map e.hom) ≫ (V).map ((η).app ((a).obj Y)) =
    (V).map ((η).app ((a).obj X)) ≫ (J).map f at hn
  let m := ((A).mapHomologicalComplex (.up ℤ)).map (singularCochainUnitApp P)
  let s := S.app P
  let z := (sheafificationSingleIso k P).hom
  let u := singularDerivedUnitApp k P
  have hu : (V).map ((η).app ((a).obj Y)) ≫ (J).map p.hom = z ≫ u :=
    sheafificationEffectiveReflectionSingleIso_unit k P
  have hv : (V).map ((a).map e.hom) = E.map d.inv := E.congr_map he
  have hE : E.map d.inv ≫ E.map d.hom = 𝟙 _ :=
    (E.map_comp _ _).symm.trans ((E.congr_map d.inv_hom_id).trans (E.map_id _))
  have hS : Qₛ.map s.hom ≫ Qₛ.map s.inv = 𝟙 _ :=
    (Qₛ.map_comp _ _).symm.trans ((Qₛ.congr_map s.hom_inv_id).trans (Qₛ.map_id _))
  change (V).map ((η).app ((a).obj X)) ≫ (J).map (f ≫ p.hom) = j ≫ Qₛ.map m
  calc
    _ = ((V).map ((η).app ((a).obj X)) ≫ (J).map f) ≫ (J).map p.hom :=
      (congrArg ((V).map ((η).app ((a).obj X)) ≫ ·) ((J).map_comp _ _)).trans
        (Category.assoc _ _ _).symm
    _ = E.map d.inv ≫ z ≫ u :=
      (congrArg (· ≫ (J).map p.hom) hn.symm).trans
        ((Category.assoc _ _ _).trans
          ((congrArg ((V).map ((a).map e.hom) ≫ ·) hu).trans
            (congrArg (· ≫ z ≫ u) hv)))
    _ = _ := by
      have hz : z = E.map d.hom ≫ j ≫ Qₛ.map s.hom := sheafificationSingleIso_hom k P
      have hu' : u = Qₛ.map (s.inv ≫ m) := singularDerivedUnitApp_eq_cochain k P
      rw [hz, hu']
      simp only [Qₛ.map_comp, Category.assoc, reassoc_of% hE, reassoc_of% hS]

/-- The actual sheafified coefficient placed in degree zero reflects to
its original singular effective motive. -/
def singleSheafReflectionIso (P : PST) :
    (M).obj (DerivedCategory.Minus.ofCochainComplex ((sₛ).obj ((A).obj P)) 0) ≅ (Q).obj P := by
  let K := (sₚ).obj P
  let e := ((A).mapDerivedCategoryFactors.app K) ≪≫
    DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (A) (.up ℤ) (0 : ℤ)).app P)
  let e' : (a).obj ((singleDerivedMinus k 0).obj P) ≅
      DerivedCategory.Minus.ofCochainComplex ((sₛ).obj ((A).obj P)) 0 :=
    (Functor.FullyFaithful.ofFullyFaithful V).preimageIso e
  exact (M).mapIso e'.symm ≪≫ singleEffectiveReflectionIso k P

/-- The comparison retains the original augmentation of the literal sheaf single. -/
@[reassoc]
theorem singleSheafReflectionIso_unit (P : PST) :
    (V).map ((η).app
      (DerivedCategory.Minus.ofCochainComplex ((sₛ).obj ((A).obj P)) 0)) ≫
        (J).map (singleSheafReflectionIso k P).hom =
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex (A) (.up ℤ) (0 : ℤ)).inv.app P ≫
          ((A).mapHomologicalComplex (.up ℤ)).map (singularCochainUnitApp P)) := by
  let K := (sₚ).obj P
  let S := (HomologicalComplex.singleMapHomologicalComplex (A) (.up ℤ) (0 : ℤ)).app P
  let Qₛ := DerivedCategory.Q (C := NST)
  let e := (A).mapDerivedCategoryFactors.app K
  let f := e ≪≫ Qₛ.mapIso S
  let X := (a).obj ((singleDerivedMinus k 0).obj P)
  let Y := DerivedCategory.Minus.ofCochainComplex ((sₛ).obj ((A).obj P)) 0
  let d : X ≅ Y := (Functor.FullyFaithful.ofFullyFaithful V).preimageIso f
  have hd : (V).map d.inv = f.inv :=
    (Functor.FullyFaithful.ofFullyFaithful V).map_preimage _
  have hn := (V).congr_map ((η).naturality d.inv)
  change (V).map (d.inv ≫ (η).app X) =
    (V).map ((η).app Y ≫ (I).map ((M).map d.inv)) at hn
  rw [Functor.map_comp, Functor.map_comp, hd] at hn
  let b := (M).map d.inv
  let p := (singleEffectiveReflectionIso k P).hom
  let m := ((A).mapHomologicalComplex (.up ℤ)).map (singularCochainUnitApp P)
  change f.inv ≫ (V).map ((η).app X) = (V).map ((η).app Y) ≫ (J).map b at hn
  change (V).map ((η).app Y) ≫ (J).map (b ≫ p) = Qₛ.map (S.inv ≫ m)
  have hu : (V).map ((η).app X) ≫ (J).map p = e.hom ≫ Qₛ.map m :=
    singleEffectiveReflectionIso_unit k P
  calc
    _ = ((V).map ((η).app Y) ≫ (J).map b) ≫ (J).map p :=
      (congrArg ((V).map ((η).app Y) ≫ ·) ((J).map_comp _ _)).trans
        (Category.assoc _ _ _).symm
    _ = f.inv ≫ (e.hom ≫ Qₛ.map m) :=
      (congrArg (· ≫ (J).map p) hn.symm).trans
        ((Category.assoc _ _ _).trans (congrArg (f.inv ≫ ·) hu))
    _ = _ := by
      change (Qₛ.map S.inv ≫ e.inv) ≫ e.hom ≫ Qₛ.map m = _
      simp only [Category.assoc, e.inv_hom_id_assoc, Qₛ.map_comp]

end AlgebraicGeometry.MotivicHomotopy
