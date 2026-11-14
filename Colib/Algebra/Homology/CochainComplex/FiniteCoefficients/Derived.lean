/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Map
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Degree-normalized signed Bockstein in the derived category

The actual signed connecting morphism is localized and shifted, with its target
normalized to degree `p + 1`. Exact functors preserve this map through their native
localization and shift comparisons. No replacement coefficient complex is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v' w w'

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [HasShift C ℤ]
  {D : Type u'} [Category.{v'} D] [HasShift D ℤ]
  (F : C ⥤ D) [F.CommShift ℤ]
/-- Shift-addition coherence preserves a connecting map with its actual next-degree target. -/
theorem map_normalized_shift_connecting {Y X : C} (δ : Y ⟶ X⟦(1 : ℤ)⟧) (p : ℤ) :
    F.map (δ⟦p⟧' ≫ (shiftFunctorAdd' C 1 p (p + 1) (add_comm 1 p)).inv.app X) ≫
      (F.commShiftIso (p + 1)).hom.app X =
    (F.commShiftIso p).hom.app Y ≫
      (F.map δ ≫ (F.commShiftIso 1).hom.app X)⟦p⟧' ≫
      (shiftFunctorAdd' D 1 p (p + 1) (add_comm 1 p)).inv.app (F.obj X) := by
  rw [F.commShiftIso_add' (add_comm 1 p)]
  simp only [Functor.CommShift.isoAdd'_hom_app, Functor.map_comp, Category.assoc]
  simp only [← Category.assoc, ← F.map_comp, Iso.inv_hom_id_app]
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc, Category.comp_id] using
    congrArg (fun f => f ≫ (shiftFunctor D p).map ((F.commShiftIso 1).hom.app X) ≫
      (shiftFunctorAdd' D 1 p (p + 1) (add_comm 1 p)).inv.app (F.obj X))
      ((F.commShiftIso p).hom.naturality δ)

end CategoryTheory.Functor
namespace CategoryTheory.Functor
open CategoryTheory.Limits
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
/-- The exact derived lift preserves the actual localized signed chain boundary. -/
theorem mapDerivedCategory_connecting {K L : CochainComplex A ℤ} (δ : L ⟶ K⟦(1 : ℤ)⟧) :
    F.mapDerivedCategory.map (DerivedCategory.Q.map δ ≫
        (DerivedCategory.Q.commShiftIso 1).hom.app K) ≫
      (F.mapDerivedCategory.commShiftIso 1).hom.app (DerivedCategory.Q.obj K) ≫
      (F.mapDerivedCategoryFactors.hom.app K)⟦(1 : ℤ)⟧' =
    F.mapDerivedCategoryFactors.hom.app L ≫
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map δ ≫
        ((F.mapHomologicalComplex (.up ℤ)).commShiftIso 1).hom.app K) ≫
      (DerivedCategory.Q.commShiftIso 1).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  have h := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom (1 : ℤ) K
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at h
  simp only [Functor.map_comp, Category.assoc]
  rw [h]
  rw [F.mapDerivedCategoryFactors_hom_naturality_assoc]
end CategoryTheory.Functor
namespace CategoryTheory.Functor
open CategoryTheory.Limits
variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
/-- Exact derived change commutes with normalization of a connecting map to degree `p + 1`. -/
theorem mapDerivedCategory_normalizedConnecting {K L : CochainComplex A ℤ}
    (δ : L ⟶ K⟦(1 : ℤ)⟧) (p : ℤ) :
    F.mapDerivedCategory.map
      ((DerivedCategory.Q.map δ ≫ (DerivedCategory.Q.commShiftIso 1).hom.app K)⟦p⟧' ≫
        (shiftFunctorAdd' _ 1 p (p + 1) (add_comm 1 p)).inv.app
          (DerivedCategory.Q.obj K)) ≫
      (F.mapDerivedCategory.commShiftIso (p + 1)).hom.app (DerivedCategory.Q.obj K) ≫
      (F.mapDerivedCategoryFactors.hom.app K)⟦p + 1⟧' =
    (F.mapDerivedCategory.commShiftIso p).hom.app (DerivedCategory.Q.obj L) ≫
      (F.mapDerivedCategoryFactors.hom.app L)⟦p⟧' ≫
      (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map δ ≫
        ((F.mapHomologicalComplex (.up ℤ)).commShiftIso 1).hom.app K) ≫
      (DerivedCategory.Q.commShiftIso 1).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj K))⟦p⟧' ≫
      (shiftFunctorAdd' _ 1 p (p + 1) (add_comm 1 p)).inv.app
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K)) := by
  rw [← Category.assoc, map_normalized_shift_connecting]
  have hnat := (shiftFunctorAdd' (DerivedCategory B) 1 p (p + 1)
    (add_comm 1 p)).inv.naturality (F.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hnat
  simp only [Category.assoc]
  rw [← hnat]
  rw [← Functor.map_comp_assoc]
  simp only [Category.assoc]
  rw [mapDerivedCategory_connecting]
  simp only [Functor.map_comp, Category.assoc]
end CategoryTheory.Functor

namespace CochainComplex.finiteCoefficients

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]

/-- The original signed cone boundary on derived coefficients, normalized from degree `p`
to degree `p + 1` by the native localization and shift-addition isomorphisms. -/
def derivedBockstein (K : CochainComplex A ℤ) (n : ℕ) (p : ℤ) :
    (DerivedCategory.Q.obj (finiteCoefficients K n))⟦p⟧ ⟶
      (DerivedCategory.Q.obj K)⟦p + 1⟧ :=
  (DerivedCategory.Q.map (bockstein K n) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app K)⟦p⟧' ≫
  (_root_.CategoryTheory.shiftFunctorAdd' _ 1 p (p + 1) (add_comm 1 p)).inv.app
    (DerivedCategory.Q.obj K)

variable (F : A ⥤ B) [F.Additive]

/-- The actual image of the signed chain boundary under an additive functor,
with its derived target normalized to degree `p + 1`. -/
def mappedDerivedBockstein (K : CochainComplex A ℤ) (n : ℕ) (p : ℤ) :
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj
      (finiteCoefficients K n)))⟦p⟧ ⟶
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))⟦p + 1⟧ :=
  (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (bockstein K n) ≫
    ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (1 : ℤ)).hom.app K) ≫
    (DerivedCategory.Q.commShiftIso (1 : ℤ)).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K))⟦p⟧' ≫
  (_root_.CategoryTheory.shiftFunctorAdd' _ 1 p (p + 1) (add_comm 1 p)).inv.app
    (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))

omit [HasDerivedCategory A] in
/-- The degree-normalized mapped boundary is the original signed Bockstein on
the actual target coefficient cone, through the canonical cone comparison. -/
theorem mappedDerivedBockstein_eq (K : CochainComplex A ℤ) (n : ℕ) (p : ℤ) :
    mappedDerivedBockstein F K n p =
      (DerivedCategory.Q.map (mapIso F K n).hom)⟦p⟧' ≫
        derivedBockstein ((F.mapHomologicalComplex (.up ℤ)).obj K) n p := by
  simp only [mappedDerivedBockstein, derivedBockstein, mapIso_bockstein,
    Functor.map_comp, Category.assoc]

end CochainComplex.finiteCoefficients

namespace CochainComplex.finiteCoefficients

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  {B : Type u'} [Category.{v'} B] [Abelian B] [HasDerivedCategory.{w'} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The exact derived comparison intertwines the original signed coefficient boundary
with its actual mapped boundary, both normalized to degree `p + 1`. -/
theorem mapDerivedCategory_derivedBockstein (K : CochainComplex A ℤ) (n : ℕ) (p : ℤ) :
    F.mapDerivedCategory.map (derivedBockstein K n p) ≫
      (F.mapDerivedCategory.commShiftIso (p + 1)).hom.app (DerivedCategory.Q.obj K) ≫
      (F.mapDerivedCategoryFactors.hom.app K)⟦p + 1⟧' =
    (F.mapDerivedCategory.commShiftIso p).hom.app (DerivedCategory.Q.obj (finiteCoefficients K n)) ≫
      (F.mapDerivedCategoryFactors.hom.app (finiteCoefficients K n))⟦p⟧' ≫
      mappedDerivedBockstein F K n p :=
  F.mapDerivedCategory_normalizedConnecting (bockstein K n) p

end CochainComplex.finiteCoefficients
