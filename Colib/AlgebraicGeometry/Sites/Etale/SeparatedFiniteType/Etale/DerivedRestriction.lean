/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Adjunction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSectionsUnivLE
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Derived restriction to the full small etale site

The exact ordinary restriction functor gives a genuine unbounded derived functor.
The small free representing sheaf maps to the restriction of the big free source
via the tautological section and the actual small-basis equivalence unit. These
sources are not identified by an isomorphism. The resulting additive comparison
retains the original coefficient complex and all integer cohomological degrees.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE
universe u w w'
@[expose] public noncomputable section
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {B : Scheme.{u}} [IsAffine B] (X : SmoothSite B)
instance fullSmallEtaleRestrict_preservesFiniteLimits :
    PreservesFiniteLimits (fullSmallEtaleRestrict X) := by
  change PreservesFiniteLimits (etaleRestrict X ⋙ (sheafEquivSmallEtale X).functor)
  infer_instance
instance fullSmallEtaleRestrict_preservesFiniteColimits :
    PreservesFiniteColimits (fullSmallEtaleRestrict X) := by
  change PreservesFiniteColimits (etaleRestrict X ⋙ (sheafEquivSmallEtale X).functor)
  infer_instance
instance fullSmallEtaleRestrict_additive : (fullSmallEtaleRestrict X).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The tautological big section determines the small-to-restricted-big free source map. -/
@[colib_ref "axiom_stacks_5ed82d14"
  "StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedSections/\
    FreeYonedaSectionsUnivLE.lean:103-127"
  "ingredient" "Native free-source sections equivalence, applied to the transported generator"]
def fullSmallSourceMap (V : EtaleSeparatedFiniteType X.left) :
    (freeYoneda.{u + 1} X.left.smallEtaleTopology).obj ((toSmallEtale X.left).obj V) ⟶
      (fullSmallEtaleRestrict X).obj
        ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj ((toSmoothSite X).obj V)) :=
  (sectionsEquiv ((toSmallEtale X.left).obj V) _).symm
    (((sheafEquivSmallEtale X).unitIso.hom.app
      ((etaleRestrict X).obj
        ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj
          ((toSmoothSite X).obj V)))).hom.app (op V)
      (gen (J := SmoothSite.etaleTopology B) ((toSmoothSite X).obj V)))

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- Exact restriction induces the actual full-small derived-Hom comparison.
No source isomorphism or cohomological comparison isomorphism is asserted. -/
@[colib_tag "COL-1232", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:39-132" "specialization"
  "Exact derived restriction with native single, shift, and localization comparisons"]
def fullSmallDerivedHomMap (V : EtaleSeparatedFiniteType X.left)
    (K : CochainComplex (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) ℤ)
    (p : ℤ) :
    ((DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj ((toSmoothSite X).obj V)) ⟶
        (DerivedCategory.Q.obj K)⟦p⟧) →+
    ((DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} X.left.smallEtaleTopology).obj ((toSmallEtale X.left).obj V)) ⟶
        (DerivedCategory.Q.obj
          (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).obj K))⟦p⟧) where
  toFun f :=
    (DerivedCategory.singleFunctor _ 0).map (fullSmallSourceMap X V) ≫
    ((fullSmallEtaleRestrict X).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
    (fullSmallEtaleRestrict X).mapDerivedCategory.map f ≫
    ((fullSmallEtaleRestrict X).mapDerivedCategory.commShiftIso p).hom.app
      (DerivedCategory.Q.obj K) ≫
    ((fullSmallEtaleRestrict X).mapDerivedCategoryFactors.hom.app K)⟦p⟧'
  map_zero' := by simp
  map_add' f g := by simp [Functor.map_add, Preadditive.comp_add, Preadditive.add_comp]

/-- The localized restricted complex agrees naturally with the exact derived restriction. -/
def fullSmallDerivedTargetIso (p : ℤ) :
    DerivedCategory.Q ⋙ shiftFunctor _ p ⋙ (fullSmallEtaleRestrict X).mapDerivedCategory ≅
    (fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q ⋙ shiftFunctor _ p :=
  Functor.isoWhiskerLeft _ ((fullSmallEtaleRestrict X).mapDerivedCategory.commShiftIso p) ≪≫
  Functor.isoWhiskerRight (fullSmallEtaleRestrict X).mapDerivedCategoryFactors _

/-- The actual comparison uses the source morphism and natural target identification. -/
theorem fullSmallDerivedHomMap_formula (V : EtaleSeparatedFiniteType X.left)
    (K : CochainComplex (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) ℤ)
    (p : ℤ)
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj ((toSmoothSite X).obj V)) ⟶
        (DerivedCategory.Q.obj K)⟦p⟧) :
    fullSmallDerivedHomMap X V K p f =
      (DerivedCategory.singleFunctor _ 0).map (fullSmallSourceMap X V) ≫
      ((fullSmallEtaleRestrict X).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (fullSmallEtaleRestrict X).mapDerivedCategory.map f ≫
      (fullSmallDerivedTargetIso X p).hom.app K := by
  simp only [fullSmallDerivedHomMap, fullSmallDerivedTargetIso,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]

/-- Full-small derived restriction commutes with the original coefficient chain maps. -/
@[colib_tag "COL-1232"]
theorem fullSmallDerivedHomMap_coefficient (V : EtaleSeparatedFiniteType X.left)
    {K L : CochainComplex (Sheaf (SmoothSite.etaleTopology B) AddCommGrpCat.{u + 1}) ℤ}
    (g : K ⟶ L) (p : ℤ)
    (f : (DerivedCategory.singleFunctor _ 0).obj
      ((freeYoneda.{u + 1} (SmoothSite.etaleTopology B)).obj ((toSmoothSite X).obj V)) ⟶
        (DerivedCategory.Q.obj K)⟦p⟧) :
    fullSmallDerivedHomMap X V L p (f ≫ (DerivedCategory.Q.map g)⟦p⟧') =
      fullSmallDerivedHomMap X V K p f ≫
        (DerivedCategory.Q.map
          (((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).map g))⟦p⟧' := by
  rw [fullSmallDerivedHomMap_formula, fullSmallDerivedHomMap_formula]
  simpa only [Functor.comp_map, Functor.map_comp, Category.assoc] using
    congrArg (fun a => (DerivedCategory.singleFunctor _ 0).map (fullSmallSourceMap X V) ≫
      ((fullSmallEtaleRestrict X).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
      (fullSmallEtaleRestrict X).mapDerivedCategory.map f ≫ a)
      ((fullSmallDerivedTargetIso X p).hom.naturality g)

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
