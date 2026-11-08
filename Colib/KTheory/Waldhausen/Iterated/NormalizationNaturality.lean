/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Iterated.ExactCoherence

/-!
# Naturality of the original binary zero normalization

The displayed comparison is the actual rebasing isomorphism used in the binary prespectrum
composition homotopy. Its two naturality squares retain the original transformations and
whiskering maps. These categorical identities do not by themselves assert spectral pasting.
-/
/-! Implementation provenance:
    `Quillen/Waldhausen/SConstruction/Iterated/NormalizationNaturality.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {V : Structure D} {U : Structure E}

/-- The actual binary comparison between the canonical zero-normalized functors. -/
def exactNormalizationCompIso {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G) :
    CategoryTheory.rebaseFunctor (F ⋙ G) W.zero U.zero (((hF.comp hG).zero W.isZero).iso U.isZero) ≅
      CategoryTheory.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero) ⋙
        CategoryTheory.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero) :=
  (CategoryTheory.rebaseFunctorIso (F ⋙ G) W.zero U.zero
    (((hF.comp hG).zero W.isZero).iso U.isZero)).symm ≪≫
    isoWhiskerRight (CategoryTheory.rebaseFunctorIso F W.zero V.zero
      ((hF.zero W.isZero).iso V.isZero)) G ≪≫
    isoWhiskerLeft _ (CategoryTheory.rebaseFunctorIso G V.zero U.zero
      ((hG.zero V.isZero).iso U.isZero))

private theorem homotopy_level_cast {X Y : Topology.LoopPrespectrum}
    {f g g' : X ⟶ Y} (e : g = g')
    (p : Topology.LoopPrespectrum.Homotopy f g = Topology.LoopPrespectrum.Homotopy f g')
    (H : Topology.LoopPrespectrum.Homotopy f g) (n : ℕ) :
    (p.mp H).level n = H.level n := by
  subst g'
  rfl

/-- Every full level track of the existing binary homotopy is induced by this exact iso. -/
theorem exactOriginalPrespectrumMapCompHomotopy_level {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G) (n : ℕ) :
    (exactOriginalPrespectrumMapCompHomotopy W V U hF hG).level n =
      (originalPrespectrumTransformationHomotopy W U (hF.comp hG).rebase
        (hF.rebase.comp hG.rebase) (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
        ((congrArg (CategoryTheory.rebaseFunctor G V.zero U.zero
          ((hG.zero V.isZero).iso U.isZero)).obj
          (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)).trans
          (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))
        (exactNormalizationCompIso hF hG).hom
        (fun _A ↦ U.weq_iso _ inferInstance)).level n := by
  simp only [exactOriginalPrespectrumMapCompHomotopy, exactNormalizationCompIso]
  apply homotopy_level_cast (originalPrespectrumMap_comp W V U hF.rebase hG.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (CategoryTheory.rebaseFunctor_obj_base _ _ _ _))

/-- Postwhiskering a transformation commutes with the actual binary normalization. -/
theorem exactNormalizationCompIso_natural_left {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hF' : IsExact W.cof W.weq V.cof V.weq F')
    (hG : IsExact V.cof V.weq U.cof U.weq G) (η : F ⟶ F') :
    normalizedWeakTransformation (hF.comp hG) (hF'.comp hG) (whiskerRight η G) ≫
        (exactNormalizationCompIso hF' hG).hom =
      (exactNormalizationCompIso hF hG).hom ≫
        whiskerRight (normalizedWeakTransformation hF hF' η)
          (CategoryTheory.rebaseFunctor G V.zero U.zero ((hG.zero V.isZero).iso U.isZero)) := by
  ext A
  simp [exactNormalizationCompIso, normalizedWeakTransformation, Category.assoc,
    ← Functor.map_comp]

/-- Prewhiskering a transformation commutes with the actual binary normalization. -/
theorem exactNormalizationCompIso_natural_right {F : C ⥤ D} {G G' : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (hG' : IsExact V.cof V.weq U.cof U.weq G') (θ : G ⟶ G') :
    normalizedWeakTransformation (hF.comp hG) (hF.comp hG') (whiskerLeft F θ) ≫
        (exactNormalizationCompIso hF hG').hom =
      (exactNormalizationCompIso hF hG).hom ≫
        whiskerLeft (CategoryTheory.rebaseFunctor F W.zero V.zero ((hF.zero W.isZero).iso V.isZero))
          (normalizedWeakTransformation hG hG' θ) := by
  ext A
  simp [exactNormalizationCompIso, normalizedWeakTransformation, Category.assoc]

end CategoryTheory.Waldhausen.IteratedS

-- COL-0324 references
attribute [colib_ref "quillen"
  "Iterated/NormalizationNaturality.lean:1-93"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  CategoryTheory.Waldhausen.IteratedS.exactNormalizationCompIso
  CategoryTheory.Waldhausen.IteratedS.exactOriginalPrespectrumMapCompHomotopy_level
  CategoryTheory.Waldhausen.IteratedS.exactNormalizationCompIso_natural_left
  CategoryTheory.Waldhausen.IteratedS.exactNormalizationCompIso_natural_right
