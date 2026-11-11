/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.CategoryTheory.FiberedCategory.GrothendieckZeroSections
public import Colib.CategoryTheory.FiberedCategory.CocartesianSectionTransition
public import Colib.CategoryTheory.Waldhausen.EquivalenceStructure
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.ExactTransport
public import Colib.CategoryTheory.Waldhausen.SmallCategory
public import Mathlib.CategoryTheory.Widesubcategory

/-!
# Waldhausen structures on cocartesian coslice sections

Evaluation transports the given fiber structure. The zero is the restriction of one global
zero section, so reindexing preserves it literally. Exact fiber transition and the original
evaluation transition isomorphism prove exactness of reindexing. The resulting diagram uses
Mathlib's wide subcategory of the existing small Waldhausen category.

Adapted from `Quillen/Waldhausen/SConstruction/Iterated/SectionChangeIndexMixedModel.lean`,
lines 27–96, at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
Change-of-index restriction and its equivalence are not asserted here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open CategoryTheory.StrictSections CategoryTheory.GrothendieckSections
open CategoryTheory.GrothendieckZeroSections CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w x z
namespace CategoryTheory.Waldhausen.CocartesianSectionStructure
variable {D : Type u} [Category.{v} D]
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{w, max u v w})
    (W : ∀ d, Waldhausen.Structure (F.obj ⟨d⟩))
    (Z : ∀ d, F.obj ⟨d⟩) (hZ : ∀ d, IsZero (Z d))
    (hmap : ∀ {d e : D} (f : d ⟶ e), IsZero ((F.map f.toLoc).toFunctor.obj (Z d)))

/-- The original fiber classes transported along evaluation, with the global section zero. -/
def sectionWaldhausen (d : D) :
    Waldhausen.Structure (underCocartesian (Pseudofunctor.Grothendieck.forget F) d) :=
  (W d).ofEquivalence (originalEvaluationEquivalence F d) (sectionZero F Z hZ hmap d)
    (hZ d)

/-- Original identity evaluation is exact for the transported classes. -/
theorem evaluation_exact (d : D) :
    Waldhausen.IsExact (sectionWaldhausen F W Z hZ hmap d).cof
      (sectionWaldhausen F W Z hZ hmap d).weq (W d).cof (W d).weq
      (originalEvaluation F d) := Waldhausen.Structure.ofEquivalence_exact _ _ _ _

private theorem exact_of_evaluation
    {A B E : Type x} [SmallCategory A] [SmallCategory B] [Category.{z} E]
    (V : Waldhausen.Structure A) (W : Waldhausen.Structure E) (e : B ≌ E)
    (z : B) (hz : IsZero (e.functor.obj z)) (H : A ⥤ B)
    (h : Waldhausen.IsExact V.cof V.weq W.cof W.weq (H ⋙ e.functor)) :
    Waldhausen.IsExact V.cof V.weq (W.ofEquivalence e z hz).cof
      (W.ofEquivalence e z hz).weq H where
  zero hx := IsZero.of_full_of_faithful_of_isZero e.functor _ (h.zero hx)
  cofibration f hf := h.cofibration f hf
  weak f hf := h.weak f hf
  pushout hi hp := IsPushout.of_map_of_faithful e.functor (h.pushout hi hp)

/-- Original reindexing is exact when the original fiber transition is exact. -/
theorem reindex_exact
    (hExact : ∀ {d e : D} (f : d ⟶ e),
      Waldhausen.IsExact (W d).cof (W d).weq (W e).cof (W e).weq
        (F.map f.toLoc).toFunctor) {d e : D} (f : d ⟶ e) :
    Waldhausen.IsExact (sectionWaldhausen F W Z hZ hmap d).cof
      (sectionWaldhausen F W Z hZ hmap d).weq
      (sectionWaldhausen F W Z hZ hmap e).cof
      (sectionWaldhausen F W Z hZ hmap e).weq
      (underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f) := by
  apply exact_of_evaluation
  exact Waldhausen.ExtensionCategory.isExact_of_natIso _ _
    ((evaluation_exact F W Z hZ hmap d).comp (hExact f))
    ((originalEvaluationTransitionIso F d (Under.mk f)) ≪≫
      eqToIso (originalEvaluation_reindex F d f).symm)

/-- The actual section category, equipped with the evaluation-transported structure. -/
def sectionModel (d : D) : WideSubcategory preservesZero.{max u v w} :=
  ⟨{ Obj := underCocartesian (Pseudofunctor.Grothendieck.forget F) d,
       waldhausen := sectionWaldhausen F W Z hZ hmap d }⟩

/-- The strict diagram retains original reindexing and the chosen global zero. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/SectionChangeIndexMixedModel.lean:83-95"
  "adaptation" "Exact cocartesian reindexing with the same global chosen zero"]
def modelDiagram
    (hExact : ∀ {d e : D} (f : d ⟶ e),
      Waldhausen.IsExact (W d).cof (W d).weq (W e).cof (W e).weq
        (F.map f.toLoc).toFunctor) : D ⥤ WideSubcategory preservesZero.{max u v w} where
  obj := sectionModel F W Z hZ hmap
  map f := ⟨⟨underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f,
    reindex_exact F W Z hZ hmap hExact f⟩, reindex_sectionZero F Z hZ hmap f⟩
  map_id d := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact underCocartesianReindex_id _ d
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact underCocartesianReindex_comp _ f g

end CategoryTheory.Waldhausen.CocartesianSectionStructure
