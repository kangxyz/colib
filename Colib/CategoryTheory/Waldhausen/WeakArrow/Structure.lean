/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.CommaCategory.Structure
public import Colib.CategoryTheory.Waldhausen.CofibrationClosedSubcategory

/-!
# The actual weak-arrow enlargement of an exact functor

Original weak arrows F(A)→B form a genuine cofibration-pushout-closed full
subcategory of the componentwise comma Waldhausen category. The literal
diagonal and both projections are exact. Their natural weak comparison uses
the original stored arrow and preserves the original factorization of F.
Target weak reflection is derived from original App1 and two-out-of-three.

Implementation provenance: `Quillen/Waldhausen/WeakArrow/Structure.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original categories, maps, hypotheses and universe parameters are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.WeakArrow
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (F : C ⥤ D)
  (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The predicate selecting comma objects whose stored arrow `F.obj A ⟶ B` is a weak equivalence
in `W`. -/
def objects : ObjectProperty (FunctorComma.Obj F) := fun X => W.weq X.hom
/-- The full category of weak arrows from the image of `F`, with the original commutative comma
squares as morphisms. -/
abbrev Obj := (objects W F).FullSubcategory

/-- Weak arrows are closed under the actual pointwise cofibration pushouts. -/
theorem closed : CofibrationClosedSubcategory.Closed (FunctorComma.waldhausenStructure V W F hF)
    (objects W F) where
  zero_mem := W.weq.id_mem _
  pushout_mem {A B E Q} {i f g j} hi h hA hB hE := by
    obtain ⟨hl, hr⟩ := FunctorComma.pointwise_of_isPushout V W F hF hi h
    exact W.gluing _ _ _ _ (hF.cofibration _ hi.1) hi.2 (hF.pushout hi.1 hl) hr
      (by exact i.w) (by exact f.w) (by exact g.w) (by exact j.w) hA hB hE

/-- Actual weak-arrow objects retain their source and target, with componentwise classes. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/Structure.lean:50" "adaptation"
    "The full subcategory of actual weak arrows with inherited componentwise classes"]
def waldhausenStructure : Structure (Obj W F) :=
  CofibrationClosedSubcategory.waldhausenStructure (FunctorComma.waldhausenStructure V W F hF)
    (objects W F) (closed V W F hF)

/-- The functor taking a weak-arrow object `F.obj A ⟶ B` to `A` and a commutative square to its
source component. -/
def source : Obj W F ⥤ C := (objects W F).ι ⋙ Comma.fst F (𝟭 D)
/-- The functor taking a weak-arrow object `F.obj A ⟶ B` to `B` and a commutative square to its
target component. -/
def target : Obj W F ⥤ D := (objects W F).ι ⋙ Comma.snd F (𝟭 D)

/-- The actual source projection is exact for the inherited componentwise structure. -/
theorem source_exact : IsExact (waldhausenStructure V W F hF).cof
    (waldhausenStructure V W F hF).weq V.cof V.weq (source W F) :=
  (CofibrationClosedSubcategory.inclusion_exact _ _ (closed V W F hF)).comp
    (FunctorComma.source_exact V W F hF)
/-- The actual target projection is exact for the inherited componentwise structure. -/
theorem target_exact : IsExact (waldhausenStructure V W F hF).cof
    (waldhausenStructure V W F hF).weq W.cof W.weq (target W F) :=
  (CofibrationClosedSubcategory.inclusion_exact _ _ (closed V W F hF)).comp
    (FunctorComma.target_exact V W F hF)

/-- The literal diagonal sends A to its original identity weak arrow F(A)→F(A). -/
def diagonal : C ⥤ Obj W F where
  obj A := ⟨⟨A, F.obj A, 𝟙 _⟩, W.weq.id_mem _⟩
  map f := ObjectProperty.homMk ⟨f, F.map f, by simp⟩

/-- Both triangles retain the actual original functors. -/
@[simp] theorem diagonal_source : diagonal W F ⋙ source W F = 𝟭 C := rfl
@[simp] theorem diagonal_target : diagonal W F ⋙ target W F = F := rfl

/-- The comparison to the identity is the original stored weak arrow, without replacement. -/
def counit : source W F ⋙ diagonal W F ⟶ 𝟭 (Obj W F) where
  app X := ObjectProperty.homMk ⟨𝟙 X.obj.left, X.obj.hom, by simp [diagonal, source]⟩
  naturality {X Y} f := by
    apply ObjectProperty.hom_ext
    apply Comma.hom_ext
    · simp [diagonal, source]
    · exact f.hom.w

/-- The actual stored weak arrow proves pointwise weakness of the counit. -/
theorem counit_weak (X : Obj W F) :
    (waldhausenStructure V W F hF).weq ((counit W F).app X) :=
  ⟨V.weq.id_mem _, X.property⟩

/-- The diagonal preserves the actual comma pushout and inherited structure. -/
theorem diagonal_exact : IsExact V.cof V.weq (waldhausenStructure V W F hF).cof
    (waldhausenStructure V W F hF).weq (diagonal W F) where
  zero h := (waldhausenStructure V W F hF).isZero.of_iso
    ((diagonal W F).mapIso (h.iso V.isZero))
  cofibration f hf := ⟨hf, hF.cofibration _ hf⟩
  weak f hf := ⟨hf, hF.weak _ hf⟩
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (objects W F).ι
    exact FunctorComma.isPushout_of_pointwise F _ _ _ _ h (hF.pushout hi h) (hF.pushout hi h)

/-- A natural weak comparison retains the original functor in the factorization. -/
def comparison : source W F ⋙ F ⟶ target W F where
  app X := X.obj.hom
  naturality {_ _} f := f.hom.w

/-- Every component of the original comparison is its stored weak arrow. -/
theorem comparison_weak (X : Obj W F) : W.weq ((comparison W F).app X) := X.property

/-- Original target weakness detects both components when the original functor reflects weakness. -/
@[colib_tag "COL-0309",
  colib_ref "quillen" "Quillen/Waldhausen/WeakArrow/Structure.lean:112" "adaptation"
    "Target weak reflection from the original functor reflection and two-out-of-three"]
theorem target_reflects [W.weq.HasTwoOutOfThreeProperty]
    (reflects : ∀ {A B : C} (f : A ⟶ B), W.weq (F.map f) → V.weq f)
    {X Y : Obj W F} (f : X ⟶ Y) (hf : W.weq ((target W F).map f)) :
    (waldhausenStructure V W F hF).weq f := by
  refine ⟨reflects f.hom.left ?_, hf⟩
  apply W.weq.of_postcomp _ Y.obj.hom Y.property
  rw [f.hom.w]
  exact W.weq.comp_mem _ _ X.property hf

end CategoryTheory.Waldhausen.WeakArrow
