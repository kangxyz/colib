/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.TransferParameterProduct
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSheafification.DerivedWindow

/-!
# The transferred torus parameter map in weight-zero cochains

Extend the already defined singular map by zero in the actual
cochain placement. The original chain permutations and sheafification
comparisons transport to those cochains with their original maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme
open Stacks.DerivedIndexing

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "B" => SheafWithTransfers.torusSectionsFunctor k
local notation "A" => nisnevichSheafify k
local notation "c" => ComplexShape.down ℕ
local notation "e" => ComplexShape.embeddingUpIntLE 0

/-- The literal termwise comparison between extending the sheafified
singular chains and sheafifying the extended presheaf chains. -/
def singularSheafCochainExtensionIso (P : PresheafWithTransfers.{u + 1} k) :
    (singularSheafComplex k P).extend e ≅ singularSheafCochainComplex k P 0 :=
  mapExtendIso (A) e (singularComplex P)

/-- The existing transfer parameter comparison on weight-zero cochains
is the extension of the original chain comparison. -/
theorem transferReducedTorusSingularParameterProduct_cochain (q : ℕ) :
    (singularSheafCochainExtensionIso k (reducedTorus k q)).hom ≫
      (singularSheafCochainFunctor k 0).map (reducedTorusParameterProduct k q) ≫
      SheafWithTransfers.singularSheafCochainTorusSectionsMap k (reducedTorus k (q + 1)) =
    ((e).extendFunctor _).map (transferReducedTorusSingularParameterProduct k q) ≫
      (mapExtendIso (B) e (singularSheafComplex k (reducedTorus k (q + 1)))).hom ≫
      ((B).mapHomologicalComplex (.up ℤ)).map
        (singularSheafCochainExtensionIso k (reducedTorus k (q + 1))).hom := by
  let P := reducedTorus k q
  let Q := reducedTorus k (q + 1)
  let f := reducedTorusParameterProduct k q
  let a := (A).mapHomologicalComplex (.up ℤ)
  let b := (B).mapHomologicalComplex (.up ℤ)
  let S := (e).extendFunctor (SheafWithTransfers.{u + 1} k)
  let m := (singularSheafFunctor k).map f
  let n := (singularCochainFunctor 0).map f
  let p := singularSheafCochainExtensionIso k P
  let r := singularSheafCochainExtensionIso k (torusSections Q)
  let g := SheafWithTransfers.singularSheafTorusSectionsMap k Q
  let x := (mapExtendIso (B) e (singularSheafComplex k Q)).hom
  let y := b.map (singularSheafCochainExtensionIso k Q).hom
  have h : S.map m ≫ r.hom = p.hom ≫ a.map n :=
    (mapExtendNatIso (A) e).hom.naturality (singularComplexMap f)
  change p.hom ≫ a.map n ≫ (r.inv ≫ S.map g ≫ x ≫ y) = S.map (m ≫ g) ≫ x ≫ y
  calc
    _ = (p.hom ≫ a.map n) ≫ r.inv ≫ S.map g ≫ x ≫ y := by simp only [Category.assoc]
    _ = (S.map m ≫ r.hom) ≫ r.inv ≫ S.map g ≫ x ≫ y :=
      congrArg (· ≫ r.inv ≫ S.map g ≫ x ≫ y) h.symm
    _ = _ := by simp only [Functor.map_comp, Category.assoc, r.hom_inv_id_assoc]

end AlgebraicGeometry.PresheafWithTransfers
