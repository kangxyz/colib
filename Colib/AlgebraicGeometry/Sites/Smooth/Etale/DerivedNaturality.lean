/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedChangeOfTopology
public import Colib.Algebra.Homology.CochainComplex.FiniteCoefficients.Basic

/-!
# Naturality of the genuine derived change-of-topology map

The source and target identifications are natural isomorphisms, so the existing
actual derived-Hom comparison commutes with scheme restriction and coefficient
chain maps. The signed Bockstein corollary uses the original connecting morphism
and keeps its shifted-complex target explicit; it does not identify that target
with ordinary sheaf cohomology or silently normalize the cohomological degree.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
universe u w w'

namespace AlgebraicGeometry.Scheme.SmoothSite
variable (S : Scheme.{u})
variable [HasSheafify (nisnevichTopology S) AddCommGrpCat.{u + 1}]
variable [HasSheafify (etaleTopology S) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{w}
  (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'}
  (Sheaf (etaleTopology S) AddCommGrpCat.{u + 1})]

/-- The actual lifted representing sources agree naturally after the exact derived lift. -/
def nisnevichToEtaleDerivedSourceIso :
    freeYoneda.{u + 1} (nisnevichTopology S) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
      (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategory ≅
    freeYoneda.{u + 1} (etaleTopology S) ⋙ DerivedCategory.singleFunctor _ 0 :=
  Functor.isoWhiskerLeft _
    ((nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategorySingleFunctor 0) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (nisnevichToEtaleFreeYonedaIso S) _

/-- Shifted localization of the mapped complex agrees naturally with the derived lift. -/
def nisnevichToEtaleDerivedTargetIso (p : ℤ) :
    DerivedCategory.Q ⋙ shiftFunctor _ p ⋙
      (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategory ≅
    (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⋙ shiftFunctor _ p :=
  Functor.isoWhiskerLeft _
    ((nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategory.commShiftIso p) ≪≫
  Functor.isoWhiskerRight
    (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategoryFactors _

/-- The original comparison is expressed through its natural source and target identifications. -/
theorem nisnevichToEtaleDerivedHomMap_formula (X : SmoothSite S)
    (K : CochainComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) ℤ) (p : ℤ)
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (nisnevichTopology S)).obj X) ⟶ (DerivedCategory.Q.obj K)⟦p⟧) :
    nisnevichToEtaleDerivedHomMap S X K p f =
      (nisnevichToEtaleDerivedSourceIso S).inv.app X ≫
      (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategory.map f ≫
      (nisnevichToEtaleDerivedTargetIso S p).hom.app K := by
  simp only [nisnevichToEtaleDerivedHomMap, nisnevichToEtaleDerivedSourceIso,
    nisnevichToEtaleDerivedTargetIso,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Iso.trans_inv, Iso.trans_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_inv,
    Functor.associator_hom_app, Category.id_comp, Category.assoc]

/-- The genuine derived comparison commutes with restriction in the representing scheme. -/
@[colib_tag "COL-1228", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:39-132" "specialization"
  "Naturality of the native single and localization comparisons on actual derived-Hom"]
theorem nisnevichToEtaleDerivedHomMap_restriction {X Y : SmoothSite S} (g : X ⟶ Y)
    (K : CochainComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) ℤ) (p : ℤ)
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (nisnevichTopology S)).obj Y) ⟶ (DerivedCategory.Q.obj K)⟦p⟧) :
    nisnevichToEtaleDerivedHomMap S X K p
      ((DerivedCategory.singleFunctor _ 0).map
        ((freeYoneda.{u + 1} (nisnevichTopology S)).map g) ≫ f) =
    (DerivedCategory.singleFunctor _ 0).map
      ((freeYoneda.{u + 1} (etaleTopology S)).map g) ≫
        nisnevichToEtaleDerivedHomMap S Y K p f := by
  rw [nisnevichToEtaleDerivedHomMap_formula, nisnevichToEtaleDerivedHomMap_formula]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun a => a ≫
      (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategory.map f ≫
      (nisnevichToEtaleDerivedTargetIso S p).hom.app K)
      ((nisnevichToEtaleDerivedSourceIso S).inv.naturality g).symm

/-- The genuine derived comparison intertwines the original coefficient chain maps. -/
@[colib_tag "COL-1228"]
theorem nisnevichToEtaleDerivedHomMap_coefficient (X : SmoothSite S)
    {K L : CochainComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) ℤ}
    (g : K ⟶ L) (p : ℤ)
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (nisnevichTopology S)).obj X) ⟶ (DerivedCategory.Q.obj K)⟦p⟧) :
    nisnevichToEtaleDerivedHomMap S X L p (f ≫ (DerivedCategory.Q.map g)⟦p⟧') =
      nisnevichToEtaleDerivedHomMap S X K p f ≫
        (DerivedCategory.Q.map
          (((nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapHomologicalComplex
            (.up ℤ)).map g))⟦p⟧' := by
  rw [nisnevichToEtaleDerivedHomMap_formula, nisnevichToEtaleDerivedHomMap_formula]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun a => (nisnevichToEtaleDerivedSourceIso S).inv.app X ≫
      (nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapDerivedCategory.map f ≫ a)
      ((nisnevichToEtaleDerivedTargetIso S p).hom.naturality g)

/-- The original signed connecting morphism commutes with derived comparison.
The target remains the shifted integral complex, before cohomological degree normalization. -/
@[colib_tag "COL-1228"]
theorem nisnevichToEtaleDerivedHomMap_bockstein (X : SmoothSite S)
    (K : CochainComplex (Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) ℤ)
    (n : ℕ) (p : ℤ)
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (nisnevichTopology S)).obj X) ⟶
        (DerivedCategory.Q.obj (CochainComplex.finiteCoefficients K n))⟦p⟧) :
    nisnevichToEtaleDerivedHomMap S X (K⟦(1 : ℤ)⟧) p
        (f ≫ (DerivedCategory.Q.map (CochainComplex.finiteCoefficients.bockstein K n))⟦p⟧') =
      nisnevichToEtaleDerivedHomMap S X (CochainComplex.finiteCoefficients K n) p f ≫
        (DerivedCategory.Q.map
          (((nisnevichToEtaleSheaf S AddCommGrpCat.{u + 1}).mapHomologicalComplex
            (.up ℤ)).map (CochainComplex.finiteCoefficients.bockstein K n)))⟦p⟧' :=
  nisnevichToEtaleDerivedHomMap_coefficient S X
    (CochainComplex.finiteCoefficients.bockstein K n) p f

end AlgebraicGeometry.Scheme.SmoothSite
