/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusCancellation.CylinderNaturality
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Single

/-!
# The unit of the singular transfer construction

The actual simplex projection gives the coefficient map in each degree.
In degree zero it defines a map from the original coefficient placed in
degree zero to its singular cochain complex.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme

universe u v

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k]

/-- The actual graph projections from the exterior simplex product. -/
def simplexProjection (n : ℕ) : simplexExteriorFunctor (k := k) n ⟶ 𝟭 (Cor k) where
  app X := (graphFunctor k).map
    (SmoothSite.productFst X.toSmoothSite (AlgebraicSimplex.smoothSiteObj k n))
  naturality X Y α :=
    parameterProduct_projection_naturality X.toSmoothSite Y.toSmoothSite
      (AlgebraicSimplex.smoothSiteObj k n) α

end AlgebraicGeometry.Cor

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Pullback of a coefficient along the actual simplex projection. -/
def singularTermUnit (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    P ⟶ singularTerm P n :=
  ObjectProperty.homMk (Functor.whiskerRight (NatTrans.op (Cor.simplexProjection n)) P.obj)

@[reassoc]
theorem singularTermUnit_naturality {P Q : PresheafWithTransfers.{v} k}
    (η : P ⟶ Q) (n : ℕ) :
    η ≫ singularTermUnit Q n = singularTermUnit P n ≫ (singularComplexMap η).f n := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  exact (η.hom.naturality ((Cor.simplexProjection n).app X.unop).op).symm

/-- The original coefficient in degree zero maps to its actual singular cochain complex. -/
def singularCochainUnitApp (P : PresheafWithTransfers.{v} k) :
    (CochainComplex.singleFunctor (PresheafWithTransfers.{v} k) 0).obj P ⟶
      singularCochainComplex P 0 :=
  HomologicalComplex.mkHomFromSingle
    (singularTermUnit P 0 ≫ (singularCochainXIso P 0 0).inv) (fun i hi => by
      have h : (0 : ℤ) < i := by
        change (0 : ℤ) + 1 = i at hi
        omega
      exact (isZero_singularCochainComplex_X P 0 i h).eq_of_tgt _ _)

/-- In degree zero the unit is the original graph projection with the placement isomorphisms. -/
theorem singularCochainUnitApp_f_zero (P : PresheafWithTransfers.{v} k) :
    (singularCochainUnitApp P).f 0 =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).hom ≫
        singularTermUnit P 0 ≫ (singularCochainXIso P 0 0).inv := by
  simp only [singularCochainUnitApp, HomologicalComplex.mkHomFromSingle_f]

/-- The degree-zero component of a placed singular coefficient map. -/
theorem singularCochainFunctor_map_f_zero {P Q : PresheafWithTransfers.{v} k}
    (f : P ⟶ Q) : ((singularCochainFunctor 0).map f).f 0 =
      (singularCochainXIso P 0 0).hom ≫ (singularComplexMap f).f 0 ≫
        (singularCochainXIso Q 0 0).inv :=
  HomologicalComplex.extendMap_f (singularComplexMap f) (ComplexShape.embeddingUpIntLE 0)
    (i := 0) (i' := 0) rfl

/-- The actual unit from coefficients in degree zero to singular cochains. -/
def singularCochainUnit :
    CochainComplex.singleFunctor (PresheafWithTransfers.{v} k) 0 ⟶ singularCochainFunctor 0 where
  app := singularCochainUnitApp
  naturality P Q f := by
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, singularCochainUnitApp_f_zero,
      singularCochainFunctor_map_f_zero]
    let S := CochainComplex.singleFunctor (PresheafWithTransfers.{v} k) 0
    let p := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 P).hom
    let q := (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Q).hom
    let a := singularTermUnit P 0
    let b := singularTermUnit Q 0
    let e := singularCochainXIso P 0 0
    let j := singularCochainXIso Q 0 0
    let g := (singularComplexMap f).f 0
    have hS : (S.map f).f 0 ≫ q = p ≫ f :=
      (HomologicalComplex.singleCompEvalIsoSelf _ (.up ℤ) 0).hom.naturality f
    have h : f ≫ b = a ≫ g := singularTermUnit_naturality f 0
    calc
      _ = ((S.map f).f 0 ≫ q) ≫ b ≫ j.inv := (Category.assoc _ _ _).symm
      _ = (p ≫ f) ≫ b ≫ j.inv := congrArg (fun m => m ≫ b ≫ j.inv) hS
      _ = p ≫ (f ≫ b) ≫ j.inv :=
        (Category.assoc p f (b ≫ j.inv)).trans
          (congrArg (fun m => p ≫ m) (Category.assoc f b j.inv).symm)
      _ = p ≫ (a ≫ g) ≫ j.inv := congrArg (fun m => p ≫ m ≫ j.inv) h
      _ = _ := by
        have h₀ : (a ≫ e.inv) ≫ e.hom ≫ g ≫ j.inv = a ≫ g ≫ j.inv :=
          (Category.assoc a e.inv _).trans
            (congrArg (fun m => a ≫ m) (e.inv_hom_id_assoc (g ≫ j.inv)))
        exact congrArg (fun m => p ≫ m) ((Category.assoc a g j.inv).trans h₀.symm)

/-- In chain degrees the unit uses the same degree-zero graph projection. -/
def singularChainUnitApp (P : PresheafWithTransfers.{v} k) :
    (ChainComplex.single₀ (PresheafWithTransfers.{v} k)).obj P ⟶ singularComplex P :=
  (ChainComplex.fromSingle₀Equiv (singularComplex P) P).symm (singularTermUnit P 0)

/-- In degree zero the original chain unit is the literal simplex projection. -/
theorem singularChainUnitApp_f_zero (P : PresheafWithTransfers.{v} k) :
    (singularChainUnitApp P).f 0 = singularTermUnit P 0 :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_zero
    (C := singularComplex P) (X := P) (singularTermUnit P 0)

end AlgebraicGeometry.PresheafWithTransfers
