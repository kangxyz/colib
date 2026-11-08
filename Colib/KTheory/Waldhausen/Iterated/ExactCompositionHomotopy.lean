/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumCompositionHomotopy

/-!
# Relative composition coherence for canonically normalized exact functors

The original exact-functor homotopies retain their canonical zero normalization. Cancellation of
its intermediate conjugating isomorphism supplies the actual composite transformation. The full
triangle then compares its original homotopy with concatenation, relative to endpoints and the
basepoint line and compatibly with the independent prespectrum structure coordinate.
-/
/-! Implementation provenance:
`Quillen/Waldhausen/SConstruction/Iterated/ExactCompositionHomotopy.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native objects, complete tracks, original coordinates and signs are retained. -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor Topology.LoopPrespectrum

universe u v
namespace CategoryTheory.Waldhausen.IteratedS
open SmallWaldhausenCategory Topology SSet

variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) (V : Structure D) {F G H : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (hG : IsExact W.cof W.weq V.cof V.weq G)
  (hH : IsExact W.cof W.weq V.cof V.weq H)

/-- Conjugation by the original zero normalizations preserves the actual composite. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ExactCompositionHomotopy.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
lemma normalizedWeakTransformation_comp (η : F ⟶ G) (θ : G ⟶ H) :
    normalizedWeakTransformation hF hH (η ≫ θ) =
      normalizedWeakTransformation hF hG η ≫ normalizedWeakTransformation hG hH θ := by
  simp [normalizedWeakTransformation, Category.assoc]

/-- The original-universe composite transformation retains its full relative comparison. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ExactCompositionHomotopy.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def originalPrespectrumTransformationCompositionHomotopy
    (h0F : F.obj W.zero = V.zero) (h0G : G.obj W.zero = V.zero)
    (h0H : H.obj W.zero = V.zero)
    (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A)) :
    (originalPrespectrumTransformationHomotopy W V hF hH h0F h0H (η ≫ θ)
      (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A))).RelHomotopy
      ((originalPrespectrumTransformationHomotopy W V hF hG h0F h0G η hη).trans
        (originalPrespectrumTransformationHomotopy W V hG hH h0G h0H θ hθ)) := by
  exact prespectrumTransformationCompositionHomotopy
    (F := asSmallCategoryMap W V hF h0F) (G := asSmallCategoryMap W V hG h0G)
    (H := asSmallCategoryMap W V hH h0H)
    (whiskerLeft AsSmall.down (whiskerRight η AsSmall.up))
    (whiskerLeft AsSmall.down (whiskerRight θ AsSmall.up))
    (fun A ↦ hη (AsSmall.down.obj A)) (fun A ↦ hθ (AsSmall.down.obj A))

/-- Canonically normalized original exact-functor homotopies have genuine relative composition
coherence, with no chosen-zero-image hypotheses on the input functors. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ExactCompositionHomotopy.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def exactOriginalPrespectrumCompositionHomotopy
    (η : F ⟶ G) (θ : G ⟶ H)
    (hη : ∀ A, V.weq (η.app A)) (hθ : ∀ A, V.weq (θ.app A)) :
    (exactOriginalPrespectrumHomotopy W V hF hH (η ≫ θ)
      (fun A ↦ V.weq.comp_mem _ _ (hη A) (hθ A))).RelHomotopy
      ((exactOriginalPrespectrumHomotopy W V hF hG η hη).trans
        (exactOriginalPrespectrumHomotopy W V hG hH θ hθ)) := by
  unfold exactOriginalPrespectrumHomotopy
  simpa only [normalizedWeakTransformation_comp W V hF hG hH] using
    originalPrespectrumTransformationCompositionHomotopy W V
    hF.rebase hG.rebase hH.rebase
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _) (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (CategoryTheory.rebaseFunctor_obj_base _ _ _ _)
    (normalizedWeakTransformation hF hG η) (normalizedWeakTransformation hG hH θ)
    (normalizedWeakTransformation_weak hF hG η hη)
    (normalizedWeakTransformation_weak hG hH θ hθ)

/-- Two actual natural isomorphisms retain the same relative comparison after canonical
normalization of their original exact functors. -/
@[colib_ref "quillen"
    "Waldhausen/SConstruction/Iterated/ExactCompositionHomotopy.lean"
    "adaptation" "Actual native objects, whole tracks, coordinates and signs"]
def exactOriginalPrespectrumIsoCompositionHomotopy (e : F ≅ G) (e' : G ≅ H) :
    (exactOriginalPrespectrumIsoHomotopy W V hF hH (e ≪≫ e')).RelHomotopy
      ((exactOriginalPrespectrumIsoHomotopy W V hF hG e).trans
        (exactOriginalPrespectrumIsoHomotopy W V hG hH e')) :=
  exactOriginalPrespectrumCompositionHomotopy W V hF hG hH e.hom e'.hom
    (fun _ ↦ V.weq_iso _ inferInstance) (fun _ ↦ V.weq_iso _ inferInstance)

end CategoryTheory.Waldhausen.IteratedS
