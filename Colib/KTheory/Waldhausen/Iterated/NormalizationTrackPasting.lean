/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.KTheory.Waldhausen.Iterated.NormalizationPasting
public import Colib.Topology.Prespectrum.RelativeHomotopyLevels

/-! Binary normalization naturality on the original exported full prespectrum tracks. -/
/-! Implementation provenance:
    `Quillen/Waldhausen/SConstruction/Iterated/NormalizationTrackPasting.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole tracks, signs and
    independent parameters are retained. -/
@[expose] public section
open Topology SSet CategoryTheory.Functor
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology.LoopPrespectrum
universe u v
namespace CategoryTheory.Waldhausen.IteratedS
variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : Structure C} {V : Structure D} {U : Structure E}

/-- Postwhiskering commutes relatively with the actual exported binary normalization track. -/
def exactNormalizationLeftTrackPasting {F F' : C ⥤ D} {G : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hF' : IsExact W.cof W.weq V.cof V.weq F')
    (hG : IsExact V.cof V.weq U.cof U.weq G) (η : F ⟶ F')
    (hη : ∀ A, V.weq (η.app A)) :
    ((exactOriginalPrespectrumHomotopy W U (hF.comp hG) (hF'.comp hG)
      (Functor.whiskerRight η G) (fun A ↦ hG.weak _ (hη A))).trans
      (exactOriginalPrespectrumMapCompHomotopy W V U hF' hG)).RelHomotopy
    ((exactOriginalPrespectrumMapCompHomotopy W V U hF hG).trans
      ((exactOriginalPrespectrumHomotopy W V hF hF' η hη).postcomp
        (exactOriginalPrespectrumMap V U hG))) := by
  refine (exactNormalizationLeftPasting hF hF' hG η hη).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact exactOriginalPrespectrumMapCompHomotopy_level hF' hG n
  · intro n
    apply Homotopy.trans_level_congr
    · exact exactOriginalPrespectrumMapCompHomotopy_level hF hG n
    · exact (originalPrespectrumTransformationHomotopy_postcomp_level hF.rebase hF'.rebase
        hG.rebase _ _ _ (normalizedWeakTransformation hF hF' η)
        (normalizedWeakTransformation_weak hF hF' η hη) n).symm

/-- Prewhiskering commutes relatively with the actual exported binary normalization track. -/
def exactNormalizationRightTrackPasting {F : C ⥤ D} {G G' : D ⥤ E}
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (hG : IsExact V.cof V.weq U.cof U.weq G)
    (hG' : IsExact V.cof V.weq U.cof U.weq G') (θ : G ⟶ G')
    (hθ : ∀ A, U.weq (θ.app A)) :
    ((exactOriginalPrespectrumHomotopy W U (hF.comp hG) (hF.comp hG')
      (Functor.whiskerLeft F θ) (fun A ↦ hθ (F.obj A))).trans
      (exactOriginalPrespectrumMapCompHomotopy W V U hF hG')).RelHomotopy
    ((exactOriginalPrespectrumMapCompHomotopy W V U hF hG).trans
      (Homotopy.precomp (exactOriginalPrespectrumMap W V hF)
        (exactOriginalPrespectrumHomotopy V U hG hG' θ hθ))) := by
  refine (exactNormalizationRightPasting hF hG hG' θ hθ).ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact exactOriginalPrespectrumMapCompHomotopy_level hF hG' n
  · intro n
    apply Homotopy.trans_level_congr
    · exact exactOriginalPrespectrumMapCompHomotopy_level hF hG n
    · exact (originalPrespectrumTransformationHomotopy_precomp_level hF.rebase hG.rebase
        hG'.rebase _ _ _ (normalizedWeakTransformation hG hG' θ)
        (normalizedWeakTransformation_weak hG hG' θ hθ) n).symm

end CategoryTheory.Waldhausen.IteratedS

-- COL-0324 references
attribute [colib_ref "quillen"
  "Iterated/NormalizationTrackPasting.lean:1-70"
  "adaptation" "Actual whole tracks, canonical normalization and operation comparison"]
  CategoryTheory.Waldhausen.IteratedS.exactNormalizationLeftTrackPasting
  CategoryTheory.Waldhausen.IteratedS.exactNormalizationRightTrackPasting
