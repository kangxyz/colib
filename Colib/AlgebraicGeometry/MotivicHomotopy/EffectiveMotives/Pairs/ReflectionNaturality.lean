/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.SmoothMotive
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.LiteralSingleReflection

/-!
# Naturality of reflection on transfer coefficients

The comparison from the effective reflection of a transfer sheaf in
degree zero to its singular motive is natural in the original presheaf.
Its transpose is the original singular augmentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k]

local notation "PST(" field ")" => LargePresheaves field
local notation "NST(" field ")" => LargeSheaves field

variable [HasDerivedCategory.{w'} NST(k)]

/-- Place a transfer sheaf in degree zero in the actual bounded-above derived category. -/
def singleTransferSheafMinus : NST(k) ⥤ DerivedCategory.Minus NST(k) :=
  (DerivedCategory.TStructure.t (C := NST(k))).minus.lift (DerivedCategory.singleFunctor NST(k) 0)
    (fun F => ⟨0, inferInstanceAs ((DerivedCategory.Q.obj
      ((CochainComplex.singleFunctor NST(k) 0).obj F)).IsLE 0)⟩)

/-- Placing a transfer sheaf in degree zero preserves addition of maps. -/
instance singleTransferSheafMinus_additive : (singleTransferSheafMinus k).Additive where
  map_add {_ _} f g := by
    apply ObjectProperty.hom_ext
    exact (DerivedCategory.singleFunctor NST(k) 0).map_add

variable [PerfectField k]
  [HasDerivedCategory.{w} PST(k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "a" => nisnevichSheafify k
local notation "M" => effectiveReflection k
local notation "S" => singleTransferSheafMinus k
local notation "E" => effectiveMotivesMinusToDerived k
set_option quotPrecheck false in
local notation "V" => DerivedCategory.Minus.ι (C := NST(k))
local notation "C" => singularEffectiveMotiveFunctor k

/-- The original sheaf-single reflection comparison is natural in its transfer coefficient. -/
theorem singleSheafReflectionIso_naturality {P Q : PST(k)} (f : P ⟶ Q) :
    (M).map ((S).map ((a).map f)) ≫ (singleSheafReflectionIso k Q).hom =
      (singleSheafReflectionIso k P).hom ≫ (C).map f := by
  let P₀ := (S).obj ((a).obj P)
  let Q₀ := (S).obj ((a).obj Q)
  let eP : (M).obj P₀ ≅ (C).obj P := singleSheafReflectionIso k P
  let eQ : (M).obj Q₀ ≅ (C).obj Q := singleSheafReflectionIso k Q
  let adj := effectiveReflectionAdjunction k
  let I := effectiveMotivesMinusInclusion k
  let g : P₀ ⟶ Q₀ := (S).map ((a).map f)
  let e := HomologicalComplex.singleMapHomologicalComplex (a) (.up ℤ) (0 : ℤ)
  let A := (a).mapHomologicalComplex (.up ℤ)
  let D : CochainComplex NST(k) ℤ ⥤ DerivedCategory NST(k) := DerivedCategory.Q
  let δ : CochainComplex.singleFunctor PST(k) 0 ⟶ singularCochainFunctor 0 :=
    singularCochainUnit
  have hn : (V).map (adj.unit.app P₀) ≫ (E).map ((M).map g) =
      (V).map g ≫ (V).map (adj.unit.app Q₀) := by
    change (V).map (adj.unit.app P₀) ≫ (V).map ((I).map ((M).map g)) =
      (V).map g ≫ (V).map (adj.unit.app Q₀)
    rw [← (V).map_comp, ← (V).map_comp]
    exact (V).congr_map (adj.unit_naturality g)
  have huP : (V).map (adj.unit.app P₀) ≫ (E).map eP.hom =
      D.map (e.inv.app P ≫ A.map (δ.app P)) :=
    singleSheafReflectionIso_unit k P
  have huQ : (V).map (adj.unit.app Q₀) ≫ (E).map eQ.hom =
      D.map (e.inv.app Q ≫ A.map (δ.app Q)) :=
    singleSheafReflectionIso_unit k Q
  have he : (CochainComplex.singleFunctor NST(k) 0).map ((a).map f) ≫ e.inv.app Q =
      e.inv.app P ≫ A.map ((CochainComplex.singleFunctor PST(k) 0).map f) :=
    e.inv.naturality f
  have hδ : (CochainComplex.singleFunctor PST(k) 0).map f ≫ δ.app Q =
      δ.app P ≫ (singularCochainFunctor 0).map f :=
    δ.naturality f
  have hcochain :
      (CochainComplex.singleFunctor NST(k) 0).map ((a).map f) ≫
          (e.inv.app Q ≫ A.map (δ.app Q)) =
        (e.inv.app P ≫ A.map (δ.app P)) ≫ A.map ((singularCochainFunctor 0).map f) := by
    rw [← Category.assoc, he, Category.assoc, ← A.map_comp, hδ, A.map_comp]
    exact (Category.assoc _ _ _).symm
  change (M).map g ≫ eQ.hom = eP.hom ≫ (C).map f
  apply (adj.homEquiv P₀ ((C).obj Q)).injective
  apply (V).map_injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  change (V).map (adj.unit.app P₀) ≫ (E).map ((M).map g) ≫ (E).map eQ.hom =
    (V).map (adj.unit.app P₀) ≫ (E).map eP.hom ≫ (E).map ((C).map f)
  calc
    _ = (V).map g ≫ ((V).map (adj.unit.app Q₀) ≫ (E).map eQ.hom) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (E).map eQ.hom) hn).trans (Category.assoc _ _ _))
    _ = (V).map g ≫ D.map (e.inv.app Q ≫ A.map (δ.app Q)) :=
      congrArg ((V).map g ≫ ·) huQ
    _ = D.map (e.inv.app P ≫ A.map (δ.app P)) ≫ (E).map ((C).map f) := by
      change D.map ((CochainComplex.singleFunctor NST(k) 0).map ((a).map f)) ≫
          D.map (e.inv.app Q ≫ A.map (δ.app Q)) =
        D.map (e.inv.app P ≫ A.map (δ.app P)) ≫
          D.map (A.map ((singularCochainFunctor 0).map f))
      rw [← D.map_comp, ← D.map_comp, hcochain]
    _ = _ := (congrArg (· ≫ (E).map ((C).map f)) huP.symm).trans
      (Category.assoc _ _ _)

end AlgebraicGeometry.MotivicHomotopy
