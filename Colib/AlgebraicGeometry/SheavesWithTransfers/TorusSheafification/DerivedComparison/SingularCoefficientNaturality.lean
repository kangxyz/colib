/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedComparison.SingularPlacement
import StacksFrontier.Homology.DerivedIndexing.Extend

/-!
# Coefficient naturality of the original derived torus comparison

The signed factor permutation is natural in the actual coefficient.
The already constructed natural derived comparison then gives the
naturality square for the original sheafified singular torus map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme
open Stacks.DerivedIndexing

universe w' u

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "G" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))

private theorem torusSingularPermutationInv_naturality
    {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    singularComplexMap (withParameterMap f G) ≫ (withParameterSingularComplexIso Q G).inv =
      (withParameterSingularComplexIso P G).inv ≫
        ((torusSectionsPresheafFunctor k).mapHomologicalComplex (.down ℕ)).map
          (singularComplexMap f) := by
  ext n : 1
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  let e := (Cor.parameterProductSwapNatIso (AlgebraicSimplex.smoothSiteObj k n) G).inv.app X.unop
  exact (f.hom.naturality e.op).symm

private theorem singularCochainTorusParameterIso_hom_naturality
    {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    (singularCochainFunctor 0).map (withParameterMap f G) ≫
        (singularCochainTorusParameterIso k Q).hom =
      (singularCochainTorusParameterIso k P).hom ≫
        ((torusSectionsPresheafFunctor k).mapHomologicalComplex (.up ℤ)).map
          ((singularCochainFunctor 0).map f) := by
  let e := ComplexShape.embeddingUpIntLE 0
  let D := e.extendFunctor (PresheafWithTransfers.{u + 1} k)
  let T := torusSectionsPresheafFunctor k
  let F := T.mapHomologicalComplex (.down ℕ)
  let L := T.mapHomologicalComplex (.up ℤ)
  let a := singularComplexMap (withParameterMap f G)
  let b := (withParameterSingularComplexIso Q G).inv
  let b' := (withParameterSingularComplexIso P G).inv
  let m := singularComplexMap f
  let x := (mapExtendIso T e (singularComplex P)).hom
  let y := (mapExtendIso T e (singularComplex Q)).hom
  change D.map a ≫ (D.map b ≫ y) = (D.map b' ≫ x) ≫ L.map (D.map m)
  calc
    _ = D.map (a ≫ b) ≫ y :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ y) (D.map_comp _ _).symm)
    _ = D.map (b' ≫ F.map m) ≫ y :=
      congrArg (fun z => D.map z ≫ y) (torusSingularPermutationInv_naturality k f)
    _ = D.map b' ≫ (D.map (F.map m) ≫ y) :=
      (congrArg (· ≫ y) (D.map_comp _ _)).trans (Category.assoc _ _ _)
    _ = _ := (congrArg (D.map b' ≫ ·) ((mapExtendNatIso T e).hom.naturality m)).trans
      (Category.assoc _ _ _).symm

variable [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

/-- The original sheafified singular comparison is natural for every
actual transfer coefficient map. -/
theorem singularSheafDerivedTorusSectionsMap_naturality
    {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    DerivedCategory.Q.map ((singularSheafCochainFunctor k 0).map (withParameterMap f G)) ≫
        singularSheafDerivedTorusSectionsMap k Q =
      singularSheafDerivedTorusSectionsMap k P ≫
        (torusSectionsDerivedFunctor k).map
          (DerivedCategory.Q.map ((singularSheafCochainFunctor k 0).map f)) := by
  let T := torusSectionsPresheafFunctor k
  let A := nisnevichSheafify k
  let R := torusSectionsDerivedFunctor k
  let F := A.mapHomologicalComplex (.up ℤ)
  let G₁ := T.mapHomologicalComplex (.up ℤ)
  let G₂ := (torusSectionsFunctor k).mapHomologicalComplex (.up ℤ)
  let q : CochainComplex (SheafWithTransfers.{u + 1} k) ℤ ⥤
      DerivedCategory (SheafWithTransfers.{u + 1} k) := DerivedCategory.Q
  let K := singularCochainComplex P 0
  let L := singularCochainComplex Q 0
  let a := (singularCochainFunctor 0).map (withParameterMap f G)
  let b := (singularCochainFunctor 0).map f
  let x := (singularCochainTorusParameterIso k P).hom
  let y := (singularCochainTorusParameterIso k Q).hom
  let τ := torusSectionsSheafificationComplexMap k (.up ℤ) K
  let τ' := torusSectionsSheafificationComplexMap k (.up ℤ) L
  have h : F.map a ≫ (F.map y ≫ τ') = (F.map x ≫ τ) ≫ G₂.map (F.map b) := by
    calc
      _ = F.map (a ≫ y) ≫ τ' :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ τ') (F.map_comp _ _).symm)
      _ = F.map (x ≫ G₁.map b) ≫ τ' :=
        congrArg (fun z => F.map z ≫ τ') (singularCochainTorusParameterIso_hom_naturality k f)
      _ = F.map x ≫ (F.map (G₁.map b) ≫ τ') :=
        (congrArg (· ≫ τ') (F.map_comp _ _)).trans (Category.assoc _ _ _)
      _ = _ := by
        have hh : F.map (G₁.map b) ≫ τ' = τ ≫ G₂.map (F.map b) := by
          ext i : 1
          exact torusSectionsSheafificationComparison_naturality k (b.f i)
        exact (congrArg (F.map x ≫ ·) hh).trans (Category.assoc _ _ _).symm
  simp only [singularSheafDerivedTorusSectionsMap, singularSheafCochainTorusSectionsMap_eq_placed]
  let υ := torusSectionsDerivedUnit k
  change q.map (F.map a) ≫ (q.map (F.map y ≫ τ') ≫ υ.app (F.obj L)) =
    (q.map (F.map x ≫ τ) ≫ υ.app (F.obj K)) ≫ R.map (q.map (F.map b))
  calc
    _ = q.map (F.map a ≫ (F.map y ≫ τ')) ≫ υ.app (F.obj L) :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (q.map_comp _ _).symm)
    _ = q.map ((F.map x ≫ τ) ≫ G₂.map (F.map b)) ≫ υ.app (F.obj L) :=
      congrArg (fun z => q.map z ≫ υ.app (F.obj L)) h
    _ = q.map (F.map x ≫ τ) ≫ (q.map (G₂.map (F.map b)) ≫ υ.app (F.obj L)) :=
      (congrArg (· ≫ _) (q.map_comp _ _)).trans (Category.assoc _ _ _)
    _ = _ := (congrArg (q.map (F.map x ≫ τ) ≫ ·) (υ.naturality (F.map b))).trans
      (Category.assoc _ _ _).symm

end AlgebraicGeometry.SheafWithTransfers
