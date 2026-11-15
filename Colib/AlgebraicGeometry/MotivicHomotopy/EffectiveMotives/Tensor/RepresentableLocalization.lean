/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.EffectiveLocalization
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.LiteralSingleReflection

/-! # Naturality of localization on degree-zero transfer representables -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable {k : Type u} [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST" => LargePresheaves k
local notation "NST" => LargeSheaves k
local notation "s" => singleDerivedMinus k 0
local notation "S" => singularEffectiveMotiveFunctor k
local notation "a" => derivedNisnevichSheafification k
local notation "A" => nisnevichSheafify k
local notation "M" => effectiveReflection k
local notation "V" => DerivedCategory.Minus.ι (C := NST)
local notation "J" => effectiveMotivesMinusToDerived k

/-- Localization of a transfer representable in degree zero is its original effective motive. -/
def localizedRepresentableIso (X : Cor k) :
    (singularPresheafToEffective k).obj
        ((singleDerivedMinus k 0).obj ((representableLarge k).obj X)) ≅
      (effectiveMotive k).obj X :=
  (sheafificationEffectiveReflectionIso k).symm.app _ ≪≫
    singleEffectiveReflectionIso k ((representableLarge k).obj X)

private theorem singleEffectiveReflectionIso_naturality {P Q : PST} (f : P ⟶ Q) :
    (a ⋙ M).map ((s).map f) ≫ (singleEffectiveReflectionIso k Q).hom =
      (singleEffectiveReflectionIso k P).hom ≫ (S).map f := by
  let adj := effectiveReflectionAdjunction k
  let F := CochainComplex.singleFunctor PST 0
  let G := (A).mapHomologicalComplex (.up ℤ)
  let H := singularCochainFunctor (k := k) 0
  let δ : F ⟶ H := singularCochainUnit
  let K := DerivedCategory.Q (C := NST)
  let c := (A).mapDerivedCategoryFactors
  let u (P : PST) := c.hom.app (F.obj P) ≫ K.map (G.map (δ.app P))
  let m := (a).map ((s).map f)
  let p := (singleEffectiveReflectionIso k P).hom
  let q := (singleEffectiveReflectionIso k Q).hom
  apply (adj.homEquiv ((a).obj ((s).obj P)) ((S).obj Q)).injective
  apply (V).map_injective
  change (V).map (adj.unit.app _ ≫ (effectiveMotivesMinusInclusion k).map ((M).map m ≫ q)) =
    (V).map (adj.unit.app _ ≫ (effectiveMotivesMinusInclusion k).map (p ≫ (S).map f))
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    Functor.map_comp, Functor.map_comp]
  change (V).map (adj.unit.app _) ≫ (J).map ((M).map m) ≫ (J).map q =
    (V).map (adj.unit.app _) ≫ (J).map p ≫ (J).map ((S).map f)
  let P₀ := (a).obj ((s).obj P)
  let Q₀ := (a).obj ((s).obj Q)
  let I := effectiveMotivesMinusInclusion k
  have hn : (V).map (adj.unit.app P₀) ≫ (J).map ((M).map m) =
      (V).map m ≫ (V).map (adj.unit.app Q₀) := by
    calc
      _ = (V).map (adj.unit.app P₀ ≫ I.map ((M).map m)) := ((V).map_comp _ _).symm
      _ = (V).map (m ≫ adj.unit.app Q₀) := (V).congr_map (adj.unit_naturality m)
      _ = _ := (V).map_comp _ _
  have hp : (V).map (adj.unit.app P₀) ≫ (J).map p = u P :=
    singleEffectiveReflectionIso_unit k P
  have hq : (V).map (adj.unit.app Q₀) ≫ (J).map q = u Q :=
    singleEffectiveReflectionIso_unit k Q
  have hc : (V).map m ≫ c.hom.app (F.obj Q) =
      c.hom.app (F.obj P) ≫ K.map (G.map (F.map f)) :=
    c.hom.naturality (F.map f)
  calc
    _ = ((V).map m ≫ (V).map (adj.unit.app Q₀)) ≫ (J).map q := by
      rw [← Category.assoc, hn]
    _ = (V).map m ≫ u Q := (Category.assoc _ _ _).trans (congrArg ((V).map m ≫ ·) hq)
    _ = u P ≫ (J).map ((S).map f) := by
      change (V).map m ≫ c.hom.app (F.obj Q) ≫ K.map (G.map (δ.app Q)) =
        (c.hom.app (F.obj P) ≫ K.map (G.map (δ.app P))) ≫ K.map (G.map (H.map f))
      rw [← Category.assoc ((V).map m), hc, Category.assoc,
        ← K.map_comp, ← G.map_comp, δ.naturality f, G.map_comp, K.map_comp]
      exact (Category.assoc _ _ _).symm
    _ = _ := (congrArg (· ≫ (J).map ((S).map f)) hp.symm).trans (Category.assoc _ _ _)

/-- Localization of the represented degree-zero map is the original effective motive map. -/
@[reassoc]
theorem localizedRepresentableIso_naturality {X Y : Cor k} (f : X ⟶ Y) :
    (singularPresheafToEffective k).map ((s).map ((representableLarge k).map f)) ≫
      (localizedRepresentableIso Y).hom =
    (localizedRepresentableIso X).hom ≫ (effectiveMotive k).map f := by
  let e := (sheafificationEffectiveReflectionIso k).symm
  let g := (s).map ((representableLarge k).map f)
  let P := (representableLarge k).obj X
  let Q := (representableLarge k).obj Y
  change (singularPresheafToEffective k).map g ≫
      e.hom.app ((s).obj Q) ≫ (singleEffectiveReflectionIso k Q).hom =
    (e.hom.app ((s).obj P) ≫ (singleEffectiveReflectionIso k P).hom) ≫ (effectiveMotive k).map f
  rw [e.hom.naturality_assoc, Category.assoc, singleEffectiveReflectionIso_naturality]
  rfl

end AlgebraicGeometry.MotivicHomotopy
