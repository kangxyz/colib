/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeak
public import Colib.CategoryTheory.Waldhausen.WeakArrow.Structure

/-! # Relative weak classes on the original fine weak-arrow category

The objects remain actual globally weak arrows F(A)→B. Only morphism weak
classes are enlarged through the original target followed by G. The original
source, target, diagonal, and stored weak counit are unchanged.

Implementation provenance: `Quillen/Waldhausen/WeakArrow/RelativeStructure.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original categories, maps, hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v' u'' v''
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.WeakArrow.Relative
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]
  (V : Structure C) (W : Structure D) (U : Structure E)
  (F : C ⥤ D) (G : D ⥤ E)
  (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hG : IsExact W.cof W.weq U.cof U.weq G)

/-- The Waldhausen structure on `C` retaining its cofibrations and detecting weak equivalences
after the composite `F ⋙ G` in `U`. -/
abbrev sourceStructure : Structure C := Structure.withInverseImageWeak (hF.comp hG)
/-- The Waldhausen structure on `D` retaining its cofibrations and detecting weak equivalences
after `G` in `U`. -/
abbrev targetStructure : Structure D := Structure.withInverseImageWeak hG

/-- Same fine weak-arrow objects; only the map class is detected after G. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/RelativeStructure.lean:41" "adaptation"
    "Inverse-image weak classes on the unchanged fine weak-arrow objects"]
def arrowStructure : Structure (Obj W F) :=
  Structure.withInverseImageWeak ((WeakArrow.target_exact V W F hF).comp hG)

/-- The unchanged original functor is exact for the relative classes. -/
theorem functor_exact : IsExact (sourceStructure V W U F G hF hG).cof
    (sourceStructure V W U F G hF hG).weq (targetStructure W U G hG).cof
    (targetStructure W U G hG).weq F where
  zero := hF.zero
  cofibration := hF.cofibration
  weak _ h := h
  pushout := hF.pushout

/-- The original target projection is exact for the genuine relative structures. -/
theorem target_exact : IsExact (arrowStructure V W U F G hF hG).cof
    (arrowStructure V W U F G hF hG).weq (targetStructure W U G hG).cof
    (targetStructure W U G hG).weq (target W F) where
  zero := (WeakArrow.target_exact V W F hF).zero
  cofibration := (WeakArrow.target_exact V W F hF).cofibration
  weak _ h := h
  pushout := (WeakArrow.target_exact V W F hF).pushout

/-- The original identity-arrow diagonal is exact without changing its objects or arrows. -/
theorem diagonal_exact : IsExact (sourceStructure V W U F G hF hG).cof
    (sourceStructure V W U F G hF hG).weq (arrowStructure V W U F G hF hG).cof
    (arrowStructure V W U F G hF hG).weq (diagonal W F) where
  zero := (WeakArrow.diagonal_exact V W F hF).zero
  cofibration := (WeakArrow.diagonal_exact V W F hF).cofibration
  weak _ h := h
  pushout := (WeakArrow.diagonal_exact V W F hF).pushout

/-- The actual stored globally weak arrow remains relatively weak. -/
theorem counit_weak (X : Obj W F) :
    (arrowStructure V W U F G hF hG).weq ((counit W F).app X) :=
  hG.weak X.obj.hom X.property

/-- Relative weakness of the target component controls the original source component
by the actual stored globally weak arrow square. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/RelativeStructure.lean:78" "adaptation"
    "Relative source exactness using target two-out-of-three"]
theorem source_exact [U.weq.HasTwoOutOfThreeProperty] :
    IsExact (arrowStructure V W U F G hF hG).cof (arrowStructure V W U F G hF hG).weq
      (sourceStructure V W U F G hF hG).cof (sourceStructure V W U F G hF hG).weq
      (source W F) where
  zero := (WeakArrow.source_exact V W F hF).zero
  cofibration := (WeakArrow.source_exact V W F hF).cofibration
  weak {X Y} f hf := by
    change U.weq (G.map (F.map f.hom.left))
    apply U.weq.of_postcomp _ (G.map Y.obj.hom) (hG.weak _ Y.property)
    have he : G.map (F.map f.hom.left) ≫ G.map Y.obj.hom =
        G.map X.obj.hom ≫ G.map f.hom.right := by
      simpa only [Functor.map_comp, Functor.id_map] using congrArg G.map f.hom.w
    rw [he]
    exact U.weq.comp_mem _ _ (hG.weak _ X.property) hf
  pushout := (WeakArrow.source_exact V W F hF).pushout

end CategoryTheory.Waldhausen.WeakArrow.Relative
