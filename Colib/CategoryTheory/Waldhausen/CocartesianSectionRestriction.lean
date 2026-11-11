/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.CategoryTheory.Waldhausen.CocartesianSectionStructure
public import Colib.CategoryTheory.FiberedCategory.SectionChangeIndexZero

/-!
# Exact restriction of cocartesian section structures

Original identity evaluation proves exactness of restriction and its actual inverse. The
same global chosen-zero equality bundles the unchanged restriction as a native strict map.
Adapted from `Quillen/Waldhausen/SConstruction/Iterated/SectionChangeIndexMixedModel.lean`,
restriction_exact through restrictionModel, at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The private evaluation-reflection proof is retained verbatim from that original file.
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
open CategoryTheory.SectionChangeIndex
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : Pseudofunctor (LocallyDiscrete D) Cat.{w, max u v w})
    (W : ∀ d, Waldhausen.Structure (F.obj ⟨d⟩))
    (Z : ∀ d, F.obj ⟨d⟩) (hZ : ∀ d, IsZero (Z d))
    (hmap : ∀ {d e : D} (f : d ⟶ e), IsZero ((F.map f.toLoc).toFunctor.obj (Z d)))
    (K : C ⥤ D)

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

/-- Actual change of index is exact because its complete evaluation square is equality. -/
theorem restriction_exact (c : C) :
    Waldhausen.IsExact (sectionWaldhausen F W Z hZ hmap (K.obj c)).cof
      (sectionWaldhausen F W Z hZ hmap (K.obj c)).weq
      (sectionWaldhausen (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c).cof
      (sectionWaldhausen (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c).weq (underFunctor F K c) := by
  apply exact_of_evaluation
  change Waldhausen.IsExact (sectionWaldhausen F W Z hZ hmap (K.obj c)).cof
    (sectionWaldhausen F W Z hZ hmap (K.obj c)).weq (W (K.obj c)).cof (W (K.obj c)).weq
    (underFunctor F K c ⋙ originalEvaluation (pullback F K) c)
  rw [CategoryTheory.SectionChangeIndex.evaluation]
  exact evaluation_exact F W Z hZ hmap (K.obj c)

/-- The inverse of the actual restriction equivalence is exact for these same structures. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/SectionChangeIndexMixedModel.lean:117"
  "adaptation" "Original evaluation-transported structure, exact maps and shared chosen zero"]
theorem restriction_inverse_exact (c : C) :
    Waldhausen.IsExact
      (sectionWaldhausen (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c).cof
      (sectionWaldhausen (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c).weq
      (sectionWaldhausen F W Z hZ hmap (K.obj c)).cof
      (sectionWaldhausen F W Z hZ hmap (K.obj c)).weq
      (underFunctor F K c).asEquivalence.inverse := by
  apply exact_of_evaluation
  let e := (underFunctor F K c).asEquivalence
  have hi : e.inverse ⋙ originalEvaluation F (K.obj c) ≅
      originalEvaluation (pullback F K) c :=
    Functor.isoWhiskerLeft e.inverse
      (eqToIso (CategoryTheory.SectionChangeIndex.evaluation F K c).symm) ≪≫
      e.invFunIdAssoc (originalEvaluation (pullback F K) c)
  exact Waldhausen.ExtensionCategory.isExact_of_natIso _ _
    (evaluation_exact (pullback F K) (fun c => W (K.obj c))
      (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
      (fun {_ _} f => hmap (K.map f)) c) hi.symm

/-- Actual restriction as an exact, strictly chosen-zero-preserving Model map. -/
def restrictionModelMap (c : C) :
    sectionModel F W Z hZ hmap (K.obj c) ⟶
      sectionModel (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) c :=
  ⟨⟨underFunctor F K c, restriction_exact F W Z hZ hmap K c⟩,
    restriction_sectionZero F K Z hZ hmap c⟩

/-- The lifted Model comparison is strictly natural in every index arrow. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/SectionChangeIndexMixedModel.lean:150"
  "adaptation" "Original evaluation-transported structure, exact maps and shared chosen zero"]
def restrictionModel
    (hExact : ∀ {d e : D} (f : d ⟶ e),
      Waldhausen.IsExact (W d).cof (W d).weq (W e).cof (W e).weq
        (F.map f.toLoc).toFunctor) :
    K ⋙ modelDiagram F W Z hZ hmap hExact ⟶
      modelDiagram (pullback F K) (fun c => W (K.obj c))
        (fun c => Z (K.obj c)) (fun c => hZ (K.obj c))
        (fun {_ _} f => hmap (K.map f)) (fun {_ _} f => hExact (K.map f)) where
  app := restrictionModelMap F W Z hZ hmap K
  naturality _ _ f := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact reindex_naturality F K f

end CategoryTheory.Waldhausen.CocartesianSectionStructure
