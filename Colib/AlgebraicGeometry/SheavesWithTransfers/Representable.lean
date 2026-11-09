/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.UnderlyingExactness
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge
public import Colib.CategoryTheory.Preadditive.LiftedAdditiveYoneda

/-!
# Sheafified signed representables

Extracted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Transfers/Cohomology/Ext/OrdinarySource.lean`, blob
`3299b08d82e4b2c4634406d1fdaa9958a3c0bc71`.
Uses native signed cycles and the actual sheafification maps.
No ordinary derived cohomology comparison is claimed.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.SheafWithTransfers
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf
variable (k : Type u) [Field k]

/-- The actual signed representable, sheafified with its original transfers. -/
def transferRepresentable : Cor k ⥤ SheafWithTransfers.{u + 1} k :=
  PresheafWithTransfers.representableLarge k ⋙ PresheafWithTransfers.nisnevichSheafify k

instance transferRepresentable_additive : (transferRepresentable k).Additive := by
  have : (PresheafWithTransfers.representableLarge k).Additive := ⟨by
    intro X Y f g
    ext Z a
    change ULift.up (a.down ≫ (f + g)) =
      ULift.up (a.down ≫ f + a.down ≫ g)
    rw [Preadditive.comp_add]⟩
  unfold transferRepresentable
  infer_instance

/-- Transfer Yoneda followed by the genuine sheafification adjunction represents sections. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Cohomology/Ext/OrdinarySource.lean:44-50"
  "adaptation" "The actual sheafified lifted representable represents original sections"]
def transferSectionsEquiv (X : Cor k) (F : SheafWithTransfers.{u + 1} k) :
    ((transferRepresentable k).obj X ⟶ F) ≃+
      PresheafWithTransfers.sections F.obj X :=
  { toEquiv := (PresheafWithTransfers.nisnevichSheafificationHomEquiv k
      ((PresheafWithTransfers.representableLarge k).obj X) F).trans
        (AdditiveFunctor.liftedYonedaAddEquiv F.obj X).toEquiv
    map_add' _ _ := by rfl }

/-- The section is evaluation of the original sheafification unit on the identity cycle. -/
theorem transferSectionsEquiv_apply (X : Cor k) (F : SheafWithTransfers.{u + 1} k)
    (f : (transferRepresentable k).obj X ⟶ F) :
    transferSectionsEquiv k X F f =
      f.hom.hom.app (op X)
        ((PresheafWithTransfers.toNisnevichSheafify k
          ((PresheafWithTransfers.representableLarge k).obj X)).hom.app (op X)
            (ULift.up (𝟙 X))) := rfl

/-- Evaluation commutes with the actual coefficient morphism. -/
theorem transferSectionsEquiv_comp (X : Cor k) {F G : SheafWithTransfers.{u + 1} k}
    (f : (transferRepresentable k).obj X ⟶ F) (g : F ⟶ G) :
    transferSectionsEquiv k X G (f ≫ g) =
      g.hom.hom.app (op X) (transferSectionsEquiv k X F f) := rfl

/-- Lifted Yoneda is contravariant for the original signed correspondence map. -/
private theorem liftedYoneda_naturality_left
    (P : PresheafWithTransfers.{u + 1} k) {X Y : Cor k} (a : X ⟶ Y)
    (f : (PresheafWithTransfers.representableLarge k).obj Y ⟶ P) :
    AdditiveFunctor.liftedYonedaAddEquiv P X
        ((PresheafWithTransfers.representableLarge k).map a ≫ f) =
      P.obj.map a.op (AdditiveFunctor.liftedYonedaAddEquiv P Y f) := by
  change f.hom.app (op X) (ULift.up ((𝟙 X) ≫ a)) =
    P.obj.map a.op (f.hom.app (op Y) (ULift.up (𝟙 Y)))
  rw [Category.id_comp]
  have h := ConcreteCategory.congr_hom (f.hom.naturality a.op) (ULift.up (𝟙 Y))
  change f.hom.app (op X) (ULift.up (a ≫ 𝟙 Y)) =
    P.obj.map a.op (f.hom.app (op Y) (ULift.up (𝟙 Y))) at h
  simpa only [Category.comp_id] using h

/-- The sheafified section equivalence retains naturality for every signed correspondence. -/
theorem transferSectionsEquiv_naturality_left (F : SheafWithTransfers.{u + 1} k)
    {X Y : Cor k} (a : X ⟶ Y) (f : (transferRepresentable k).obj Y ⟶ F) :
    transferSectionsEquiv k X F ((transferRepresentable k).map a ≫ f) =
      PresheafWithTransfers.transfer F.obj a (transferSectionsEquiv k Y F f) := by
  change AdditiveFunctor.liftedYonedaAddEquiv F.obj X
    (((PresheafWithTransfers.nisnevichSheafificationAdjunction k).homEquiv _ _)
      ((PresheafWithTransfers.nisnevichSheafify k).map
        ((PresheafWithTransfers.representableLarge k).map a) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact liftedYoneda_naturality_left k F.obj a _

attribute [colib_tag "COL-0382"]
  transferRepresentable
  transferSectionsEquiv
  transferSectionsEquiv_apply
  transferSectionsEquiv_naturality_left

attribute [colib_ref "MVW2006"
  "Lecture 13, Lemma 13.4(2), pp. 99-100"
  "adaptation" "Sheafified signed representables, with evaluation at the actual unit identity"]
  transferSectionsEquiv

end AlgebraicGeometry.SheafWithTransfers
