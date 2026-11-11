/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPseudofunctor
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullback
public import Colib.CategoryTheory.Waldhausen.CocartesianSectionStructure

/-!
# Bounded-above-flat cocartesian sections on all schemes

The fibers are the existing full subcategories of Stacks-perfect complexes with an upper
term bound and flat terms. A single global zero section supplies all chosen section zeros.
Evaluation transfers the existing fiber Waldhausen structure; geometric pullback proves exact
reindexing for arbitrary scheme morphisms. No coefficient-index restriction or localization
conclusion is asserted.

Adapted from `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionChangeIndex.lean`,
lines 28–57, at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RingedSpace
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
open CategoryTheory.GrothendieckZeroSections CategoryTheory.Waldhausen
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
open CategoryTheory.Waldhausen.CocartesianSectionStructure
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Cocartesian coslice sections of the actual all-scheme geometric pseudofunctor. -/
abbrev BoundedAboveFlatGlobalSections (X : Scheme.{u}ᵒᵖ) :=
  underCocartesian (Pseudofunctor.Grothendieck.forget boundedAboveFlatPerfectPseudofunctor) X

/-- The original geometric Waldhausen structure in every scheme fiber. -/
def boundedAboveFlatGlobalFiberWaldhausen (X : Scheme.{u}ᵒᵖ) :
    Waldhausen.Structure (boundedAboveFlatPerfectPseudofunctor.obj ⟨X⟩) :=
  boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace

/-- The chosen geometric fiber zero, independent of the coslice index. -/
def boundedAboveFlatGlobalFiberZero (X : Scheme.{u}ᵒᵖ) :
    boundedAboveFlatPerfectPseudofunctor.obj ⟨X⟩ :=
  (boundedAboveFlatGlobalFiberWaldhausen X).zero

/-- The chosen geometric fiber object is zero. -/
theorem boundedAboveFlatGlobalFiberZero_isZero (X : Scheme.{u}ᵒᵖ) :
    IsZero (boundedAboveFlatGlobalFiberZero X) :=
  (boundedAboveFlatGlobalFiberWaldhausen X).isZero

/-- Geometric pullback preserves the zero property for every scheme morphism. -/
theorem boundedAboveFlatGlobalFiberZero_map_isZero {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    IsZero ((boundedAboveFlatPerfectPseudofunctor.map f.toLoc).toFunctor.obj
      (boundedAboveFlatGlobalFiberZero X)) :=
  (boundedAboveFlatPerfectPullback f.unop).map_isZero
    (boundedAboveFlatGlobalFiberZero_isZero X)

/-- Every geometric transition is exact for the existing fiber structures. -/
theorem boundedAboveFlatGlobalFiber_exact {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedAboveFlatGlobalFiberWaldhausen X).cof
      (boundedAboveFlatGlobalFiberWaldhausen X).weq
      (boundedAboveFlatGlobalFiberWaldhausen Y).cof
      (boundedAboveFlatGlobalFiberWaldhausen Y).weq
      (boundedAboveFlatPerfectPseudofunctor.map f.toLoc).toFunctor :=
  boundedAboveFlatPerfectPullback_isExact f.unop

/-- The same global zero family restricts to a chosen zero in each coslice category. -/
def boundedAboveFlatGlobalSectionZero (X : Scheme.{u}ᵒᵖ) : BoundedAboveFlatGlobalSections X :=
  sectionZero boundedAboveFlatPerfectPseudofunctor boundedAboveFlatGlobalFiberZero
    boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero f) X

/-- The original section structure is transported along genuine identity evaluation. -/
def boundedAboveFlatGlobalSectionWaldhausen (X : Scheme.{u}ᵒᵖ) :
    Waldhausen.Structure (BoundedAboveFlatGlobalSections X) :=
  sectionWaldhausen boundedAboveFlatPerfectPseudofunctor boundedAboveFlatGlobalFiberWaldhausen
    boundedAboveFlatGlobalFiberZero boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero f) X

/-- Literal coslice restriction on the all-scheme category. -/
def boundedAboveFlatGlobalSectionsMap {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    BoundedAboveFlatGlobalSections X ⥤ BoundedAboveFlatGlobalSections Y :=
  underCocartesianReindex (Pseudofunctor.Grothendieck.forget boundedAboveFlatPerfectPseudofunctor) f

/-- The small Waldhausen category of the same original sections. -/
def boundedAboveFlatGlobalSectionModel (X : Scheme.{u}ᵒᵖ) :
    WideSubcategory preservesZero.{u + 1} :=
  sectionModel boundedAboveFlatPerfectPseudofunctor boundedAboveFlatGlobalFiberWaldhausen
    boundedAboveFlatGlobalFiberZero boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero f) X

/-- Exact geometric reindexing defines one strict chosen-zero-preserving diagram on all schemes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSectionChangeIndex.lean:54-57"
  "adaptation" "The original all-scheme section diagram on native Stacks-perfect fibers"]
def boundedAboveFlatGlobalSectionModelFunctor :
    Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{u + 1} :=
  modelDiagram boundedAboveFlatPerfectPseudofunctor boundedAboveFlatGlobalFiberWaldhausen
    boundedAboveFlatGlobalFiberZero boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero f)
    (fun {_ _} f => boundedAboveFlatGlobalFiber_exact f)

/-- The strict functor retains the literal original reindexing functor. -/
theorem boundedAboveFlatGlobalSectionModelFunctor_map_toFunctor {X Y : Scheme.{u}ᵒᵖ}
    (f : X ⟶ Y) :
    (boundedAboveFlatGlobalSectionModelFunctor.map f).hom.toFunctor =
      boundedAboveFlatGlobalSectionsMap f := rfl

/-- Original identity evaluation with its unchanged geometric target. -/
def boundedAboveFlatGlobalSectionEvaluation (X : Scheme.{u}ᵒᵖ) :
    BoundedAboveFlatGlobalSections X ⥤
      (boundedAboveFlatPerfectComplex X.unop.toRingedSpace).FullSubcategory :=
  originalEvaluation boundedAboveFlatPerfectPseudofunctor X

instance boundedAboveFlatGlobalSectionEvaluation_isEquivalence (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionEvaluation X).IsEquivalence :=
  inferInstanceAs (originalEvaluation boundedAboveFlatPerfectPseudofunctor X).IsEquivalence

/-- Evaluation retains the original fiber zero literally. -/
theorem boundedAboveFlatGlobalSectionEvaluation_zero (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionEvaluation X).obj (boundedAboveFlatGlobalSectionZero X) =
      boundedAboveFlatGlobalFiberZero X := rfl

/-- Reindexing retains the restriction of the same global chosen zero literally. -/
theorem boundedAboveFlatGlobalSectionsMap_zero {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    (boundedAboveFlatGlobalSectionsMap f).obj (boundedAboveFlatGlobalSectionZero X) =
      boundedAboveFlatGlobalSectionZero Y :=
  reindex_sectionZero boundedAboveFlatPerfectPseudofunctor boundedAboveFlatGlobalFiberZero
    boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} g => boundedAboveFlatGlobalFiberZero_map_isZero g) f

/-- The transported structure uses exactly the declared global section zero. -/
theorem boundedAboveFlatGlobalSectionWaldhausen_zero (X : Scheme.{u}ᵒᵖ) :
    (boundedAboveFlatGlobalSectionWaldhausen X).zero =
      boundedAboveFlatGlobalSectionZero X := rfl

/-- The restricted global zero retains its universal property. -/
theorem boundedAboveFlatGlobalSectionZero_isZero (X : Scheme.{u}ᵒᵖ) :
    IsZero (boundedAboveFlatGlobalSectionZero X) :=
  (boundedAboveFlatGlobalSectionWaldhausen X).isZero

/-- Original evaluation is exact for the transported section structure. -/
theorem boundedAboveFlatGlobalSectionEvaluation_exact (X : Scheme.{u}ᵒᵖ) :
    Waldhausen.IsExact (boundedAboveFlatGlobalSectionWaldhausen X).cof
      (boundedAboveFlatGlobalSectionWaldhausen X).weq
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).cof
      (boundedAboveFlatPerfectWaldhausen X.unop.toRingedSpace).weq
      (boundedAboveFlatGlobalSectionEvaluation X) :=
  evaluation_exact boundedAboveFlatPerfectPseudofunctor boundedAboveFlatGlobalFiberWaldhausen
    boundedAboveFlatGlobalFiberZero boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} f => boundedAboveFlatGlobalFiberZero_map_isZero f) X

/-- Arbitrary scheme reindexing is exact for the transported section structures. -/
theorem boundedAboveFlatGlobalSectionsMap_exact {X Y : Scheme.{u}ᵒᵖ} (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedAboveFlatGlobalSectionWaldhausen X).cof
      (boundedAboveFlatGlobalSectionWaldhausen X).weq
      (boundedAboveFlatGlobalSectionWaldhausen Y).cof
      (boundedAboveFlatGlobalSectionWaldhausen Y).weq (boundedAboveFlatGlobalSectionsMap f) :=
  reindex_exact boundedAboveFlatPerfectPseudofunctor boundedAboveFlatGlobalFiberWaldhausen
    boundedAboveFlatGlobalFiberZero boundedAboveFlatGlobalFiberZero_isZero
    (fun {_ _} g => boundedAboveFlatGlobalFiberZero_map_isZero g)
    (fun {_ _} g => boundedAboveFlatGlobalFiber_exact g) f

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0533"] boundedAboveFlatGlobalSectionModelFunctor

end AlgebraicGeometry.Scheme.Modules
