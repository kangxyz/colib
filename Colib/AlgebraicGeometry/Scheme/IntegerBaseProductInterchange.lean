/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProducts

/-!
# Interchange of independent products over the integer base

The actual nested pullbacks retain their three projections, original factor maps and
involutive swap. The full-category lift retains quasi-compactness of the fixed legs;
morphisms of the varying scheme remain unrestricted.

Source: archive Quillen/AlgebraicGeometry/Scheme/BaseProductInterchange.lean
SHA256: 7ec69cef161801f81533c1215b27e6b3aa885c09809f00068df9088897cf3f44
Selection: lines 25-231, independent-factor interchange and actual qc lift.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local simp] pullback.map pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc
universe u

namespace AlgebraicGeometry.Scheme.Products

variable {S T S' T' : AlgebraicGeometry.Scheme.{u}}

/-- The literal nested pullback map sends `((x,s),t)` to `((x,t),s)`. -/
@[colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:35"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def baseProductSwapMap (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductFunctor q).obj ((baseProductFunctor p).obj X) ⟶
      (baseProductFunctor p).obj ((baseProductFunctor q).obj X) :=
  pullback.lift
    (pullback.lift
      (pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q ≫
        pullback.fst (specULiftZIsTerminal.from X) p)
      (pullback.snd (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q)
      (specULiftZIsTerminal.hom_ext _ _))
    (pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q ≫
      pullback.snd (specULiftZIsTerminal.from X) p)
    (specULiftZIsTerminal.hom_ext _ _)

/-- The shared original base coordinate is unchanged. -/
@[reassoc (attr := simp), colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:51"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapMap_fst_fst (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec
    (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫
        pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor q).obj X)) p ≫
          pullback.fst (specULiftZIsTerminal.from X) q =
      pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q ≫
        pullback.fst (specULiftZIsTerminal.from X) p := by
  simp [baseProductSwapMap]

/-- The original outer factor becomes the inner second coordinate. -/
@[reassoc (attr := simp), colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:62"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapMap_fst_snd (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec
    (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫
        pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor q).obj X)) p ≫
          pullback.snd (specULiftZIsTerminal.from X) q =
      pullback.snd (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q := by
  simp [baseProductSwapMap]

/-- The original inner second coordinate becomes the outer factor. -/
@[reassoc (attr := simp), colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:72"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapMap_snd (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of
    (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫
        pullback.snd (specULiftZIsTerminal.from ((baseProductFunctor q).obj X)) p =
      pullback.fst (specULiftZIsTerminal.from ((baseProductFunctor p).obj X)) q ≫
        pullback.snd (specULiftZIsTerminal.from X) p := by
  simp [baseProductSwapMap]

/-- Exchanging the same two original factors twice is the original identity map. -/
@[colib_tag "COL-0532", colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:81"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapMap_comp (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of
    (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    baseProductSwapMap p q X ≫ baseProductSwapMap q p X = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [Category.assoc]
  · simp [Category.assoc]

/-- The swap commutes with every original base-scheme morphism. -/
@[reassoc, colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:90"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapMap_naturality (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec
    (.of (ULift.{u} ℤ))))
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) :
    (baseProductFunctor q).map ((baseProductFunctor p).map f) ≫ baseProductSwapMap p q Y =
      baseProductSwapMap p q X ≫
        (baseProductFunctor p).map ((baseProductFunctor q).map f) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;> simp [baseProductSwapMap, baseProductFunctor, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, Category.assoc]

/-- The actual independent-factor interchange of the existing product functors. -/
@[colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:100"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
def baseProductSwapIso (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) :
    baseProductFunctor p ⋙ baseProductFunctor q ≅
      baseProductFunctor q ⋙ baseProductFunctor p :=
  NatIso.ofComponents (fun X =>
    { hom := baseProductSwapMap p q X
      inv := baseProductSwapMap q p X
      hom_inv_id := baseProductSwapMap_comp p q X
      inv_hom_id := baseProductSwapMap_comp q p X })
    (fun f => baseProductSwapMap_naturality p q f)

/-- The forward isomorphism component is exactly the original two-lift map. -/
@[simp, colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:112"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapIso_hom_app (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec
    (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X = baseProductSwapMap p q X := rfl

/-- The chosen reverse component is the same literal swap with factors exchanged. -/
@[simp, colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:118"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapIso_inv_app (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec
    (.of (ULift.{u} ℤ))))
    (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).inv.app X = baseProductSwapMap q p X := rfl

/-- The actual natural isomorphisms are involutive without identifying their pullback objects. -/
@[colib_tag "COL-0532", colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:123"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapIso_trans (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of
    (ULift.{u} ℤ)))) :
    baseProductSwapIso p q ≪≫ baseProductSwapIso q p = Iso.refl _ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact baseProductSwapMap_comp p q X

/-- Removing the final first factor retains the original map of the other product functor. -/
@[reassoc, colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:132"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapIso_projection_first (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X ≫
        (baseProductProjection p).app ((baseProductFunctor q).obj X) =
      (baseProductFunctor q).map ((baseProductProjection p).app X) := by
  apply pullback.hom_ext <;>
    simp [baseProductSwapMap, baseProductProjection, baseProductFunctor]

/-- Removing the inner second factor retains the original outer projection. -/
@[reassoc, colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:142"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapIso_projection_second (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductSwapIso p q).hom.app X ≫
        (baseProductFunctor p).map ((baseProductProjection q).app X) =
      (baseProductProjection q).app ((baseProductFunctor p).obj X) := by
  apply pullback.hom_ext <;>
    simp [baseProductSwapMap, baseProductProjection, baseProductFunctor, Category.assoc]

/-- An actual morphism of the first fixed factor commutes with the whole swap. -/
@[reassoc, colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:152"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapIso_transformation_first (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (p' : S' ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (f : S ⟶ S')
    (hf : f ≫ p' = p) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductFunctor q).map ((baseProductTransformation p p' f hf).app X) ≫
        (baseProductSwapIso p' q).hom.app X =
      (baseProductSwapIso p q).hom.app X ≫
        (baseProductTransformation p p' f hf).app ((baseProductFunctor q).obj X) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]

/-- An independent actual morphism of the second factor commutes with the whole swap. -/
@[reassoc, colib_ref "quillen"
  "Quillen pinned aglib 2c34f185: Aglib/AlgebraicGeometry/Products/IntegerBaseInterchange.lean:166"
  "adaptation" "Original construction on native objects with its original maps and hypotheses."]
theorem baseProductSwapIso_transformation_second (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) (q' : T' ⟶ (Spec (.of (ULift.{u} ℤ)))) (g : T ⟶ T')
    (hg : g ≫ q' = q) (X : AlgebraicGeometry.Scheme.{u}) :
    (baseProductTransformation q q' g hg).app ((baseProductFunctor p).obj X) ≫
        (baseProductSwapIso p q').hom.app X =
      (baseProductSwapIso p q).hom.app X ≫
        (baseProductFunctor p).map ((baseProductTransformation q q' g hg).app X) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]
  · simp [baseProductSwapMap, baseProductFunctor, baseProductTransformation, Category.assoc]

end AlgebraicGeometry.Scheme.Products
