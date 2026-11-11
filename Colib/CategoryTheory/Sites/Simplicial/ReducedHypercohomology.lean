/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.CategoryTheory.Sites.Simplicial.ReducedChains
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Reduced hypercohomology on pointed simplicial presheaves

Reduced hypercohomology is derived Hom from the actual reduced normalized
chains after degreewise sheafification. Chain degree (n) occupies cochain
degree (-n). Restriction and changes of coefficients are precomposition
and shifted postcomposition in the same unbounded derived category.

The construction is the chain-side expression in equation (2.9) of
Voevodsky's *Reduced power operations in motivic cohomology*. The local
homotopy comparison and motivic representability are separate statements.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe d w v u

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- Reduced normalized chains placed in nonpositive cochain degrees. -/
def reducedCochains : PointedSimplicialPresheaf.{w} C ⥤
    CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ :=
  sheafifiedReducedChains C J ⋙ (ComplexShape.embeddingUpIntLE 0).extendFunctor _

/-- Freely pointing a discrete presheaf gives the free representing sheaf in cochain degree zero. -/
def reducedCochainsFreeDiscreteIso (F : Cᵒᵖ ⥤ Type w) :
    (reducedCochains C J).obj ((free C).obj ((discretePresheaf C).obj F)) ≅
      (CochainComplex.singleFunctor _ 0).obj
        ((presheafToSheaf J AddCommGrpCat.{w}).obj (F ⋙ AddCommGrpCat.free)) :=
  ((ComplexShape.embeddingUpIntLE 0).extendFunctor _).mapIso
      ((discreteSheafifiedReducedChainsIso C J).app F) ≪≫
    HomologicalComplex.extendSingleIso (ComplexShape.embeddingUpIntLE 0)
      ((presheafToSheaf J AddCommGrpCat.{w}).obj (F ⋙ AddCommGrpCat.free)) 0 0 rfl

variable [HasDerivedCategory.{d} (Sheaf J AddCommGrpCat.{w})]

/-- The derived object of the actual sheafified reduced cochains. -/
def reducedDerivedChains : PointedSimplicialPresheaf.{w} C ⥤
    DerivedCategory (Sheaf J AddCommGrpCat.{w}) :=
  reducedCochains C J ⋙ DerivedCategory.Q

/-- Reduced hypercohomology in degree `p` with coefficients in the cochain complex `K`. -/
def reducedHypercohomology (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (p : ℤ) :
    (PointedSimplicialPresheaf.{w} C)ᵒᵖ ⥤ AddCommGrpCat.{d} :=
  (reducedDerivedChains C J).op ⋙ preadditiveYoneda.obj ((DerivedCategory.Q.obj K)⟦p⟧)

theorem reducedHypercohomology_obj
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (p : ℤ)
    (X : PointedSimplicialPresheaf.{w} C) :
    (reducedHypercohomology C J K p).obj (op X) =
      AddCommGrpCat.of ((reducedDerivedChains C J).obj X ⟶ (DerivedCategory.Q.obj K)⟦p⟧) :=
  rfl

theorem reducedHypercohomology_map_apply
    (K : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ) (p : ℤ)
    {X Y : PointedSimplicialPresheaf.{w} C} (f : X ⟶ Y)
    (x : (reducedHypercohomology C J K p).obj (op Y)) :
    (reducedHypercohomology C J K p).map f.op x = (reducedDerivedChains C J).map f ≫ x :=
  rfl

/-- The coefficient map is shifted postcomposition in the native derived category. -/
def reducedHypercohomologyCoefficientMap
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ} (p : ℤ) (f : K ⟶ L) :
    reducedHypercohomology C J K p ⟶ reducedHypercohomology C J L p :=
  Functor.whiskerLeft (reducedDerivedChains C J).op
    (preadditiveYoneda.map ((DerivedCategory.Q.map f)⟦p⟧'))

theorem reducedHypercohomologyCoefficientMap_app_apply
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{w}) ℤ} (p : ℤ) (f : K ⟶ L)
    (X : PointedSimplicialPresheaf.{w} C) (x : (reducedHypercohomology C J K p).obj (op X)) :
    (reducedHypercohomologyCoefficientMap C J p f).app (op X) x =
      x ≫ (DerivedCategory.Q.map f)⟦p⟧' :=
  rfl

end CategoryTheory.PointedSimplicialPresheaf

attribute [colib_ref "Voevodsky2003ReducedPowers" "Section 2, equation (2.9), p. 5" "adaptation"
  "The reduced-chain side of the cohomology comparison, prior to local representability"]
  CategoryTheory.PointedSimplicialPresheaf.reducedHypercohomology
