/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.BocksteinShift
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.ParameterProduct

/-!
# The Bockstein and the finite motivic parameter map

The original parameter map has degree one in the torus variable.
The shifted target comparison contributes the sign relating its two
coefficient Bocksteins.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CochainComplex
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))
  AddCommGrpCat.{u + 1}]

local notation "B" => (torusParameterSheafFunctor k)
local notation "R" =>
  (Functor.mapHomologicalComplex (torusParameterSheafFunctor k) (ComplexShape.up ℤ))

open finiteCoefficients

set_option maxHeartbeats 500000 in
-- Compare the two exact signed cone targets in the ordinary sheaf category.
/-- The original signed cone map anticommutes with the positive Bockstein
shifted once in the torus parameter. -/
theorem motivicFiniteSheafParameterProduct_modBockstein (q n : ℕ) :
    let L := motivicSheafComplex k (q + 1)
    let M := motivicFiniteSheafComplex k (q + 1) n
    motivicFiniteSheafParameterProduct k q n ≫
        (R).map ((modBockstein L n)⟦(1 : ℤ)⟧') ≫
        ((R).commShiftIso (1 : ℤ)).hom.app (M⟦(1 : ℤ)⟧) =
      -(modBockstein (motivicSheafComplex k q) n ≫
        (motivicFiniteSheafParameterProduct k q n)⟦(1 : ℤ)⟧') := by
  intro L M
  let K := motivicSheafComplex k q
  let f := motivicSheafParameterProduct k q
  let a := (shiftOneIso L n).hom
  let b := (mapIso B (L⟦(1 : ℤ)⟧) n).hom
  let e := motivicFiniteParameterTargetIso k q n
  let c := ((R).commShiftIso (1 : ℤ)).hom
  let D := CochainComplex
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) ℤ
  let S := CategoryTheory.shiftFunctor D (1 : ℤ)
  have he : e.hom = (R).map a ≫ b := by
    have h : S.map (n • 𝟙 L) = n • 𝟙 (S.obj L) := by simp [S]
    have h' : (R).map (n • 𝟙 (S.obj L)) = n • 𝟙 ((R).obj (S.obj L)) := by simp
    dsimp only [e, a, b]
    rw [motivicFiniteParameterTargetIso_hom_eq k q n h h',
      finiteCoefficients.mapIso_eq B (S.obj L) n h']
    change _ = (R).map ((shiftTriangleIso L n 1).hom.hom₃) ≫ _
    rw [shiftTriangleIso_hom₃ L n 1 h]
    rfl
  let β := modBockstein (L⟦(1 : ℤ)⟧) n
  let γ := (modBockstein L n)⟦(1 : ℤ)⟧'
  let M' := finiteCoefficients (L⟦(1 : ℤ)⟧) n
  let z := (R).map γ ≫ c.app (M⟦(1 : ℤ)⟧)
  let t := modBockstein ((R).obj (L⟦(1 : ℤ)⟧)) n
  have hb : b ≫ modBockstein ((R).obj (L⟦(1 : ℤ)⟧)) n =
      (R).map β ≫ c.app M' ≫
        S.map b := mapIso_hom_modBockstein B (L⟦(1 : ℤ)⟧) n
  have ha : a ≫ β = -(γ ≫ S.map a) := shiftOneIso_hom_modBockstein L n
  have hn : (R).map (S.map a) ≫ c.app M' =
      c.app (M⟦(1 : ℤ)⟧) ≫ S.map ((R).map a) := c.naturality a
  have ht : e.hom ≫ t = -(z ≫ S.map e.hom) := by
    calc
      _ = (R).map (a ≫ β) ≫ c.app M' ≫ S.map b := by
        rw [he, Category.assoc, show b ≫ t = _ from hb, (R).map_comp]
        simp only [Category.assoc]
      _ = -((R).map γ ≫ ((R).map (S.map a) ≫ c.app M') ≫ S.map b) := by
        rw [ha, (R).map_neg, (R).map_comp, Preadditive.neg_comp]
        simp only [Category.assoc]
      _ = _ := by rw [hn, he, S.map_comp]; simp only [z, Category.assoc]
  let p := motivicFiniteSheafParameterProduct k q n
  have hp : p ≫ e.hom = finiteCoefficients.map n f := by
    change (finiteCoefficients.map n f ≫ e.inv) ≫ e.hom = _
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have goal : p ≫ z = -(modBockstein K n ≫ S.map p) := by
    apply (cancel_mono (S.map e.hom)).1
    have hz : z ≫ S.map e.hom = -(e.hom ≫ t) := by rw [ht, neg_neg]
    rw [Category.assoc p, hz, Preadditive.comp_neg, ← Category.assoc p, hp,
      modBockstein_naturality, Preadditive.neg_comp, Category.assoc (modBockstein K n),
      ← S.map_comp, hp]
  exact goal

end AlgebraicGeometry.PresheafWithTransfers
