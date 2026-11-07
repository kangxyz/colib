/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Fibration.AcyclicSubcategory

/-!
Implementation provenance: `Quillen/Waldhausen/Fibration/InverseImageWeak.lean`
at Quillen c561118b7795eb9780be9ed391c3251d6a4d0afd.

# Inverse-image weak equivalences along an actual exact functor

Only the weak class changes: the source category, cofibrations, chosen zero,
and pushouts are unchanged. Gluing follows by mapping the displayed pushouts.
Two-out-of-three and the structural extension axiom descend from the target.
The latter uses the genuine image zero, without any strict zero-preservation
assumption. This categorical construction asserts no localization comparison.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {V : Structure C} {W : Structure D} {F : C ⥤ D}

namespace Structure
variable (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The actual source cofibration category with weak equivalences detected by `F`. -/
def withInverseImageWeak : Structure C where
  zero := V.zero
  isZero := V.isZero
  cof := V.cof
  weq := W.weq.inverseImage F
  cof_multiplicative := inferInstance
  weq_multiplicative := inferInstance
  cof_iso := V.cof_iso
  weq_iso := by
    intro X Y f hf
    let : IsIso f := hf
    exact W.weq_iso (F.map f) inferInstance
  cof_zero := V.cof_zero
  pushout_exists := V.pushout_exists
  cof_pushout := V.cof_pushout
  gluing := by
    intro A B D P A' B' D' P' i f g j i' f' g' j' a b d p hi hi' h h' ei ef eg ej ha hb hd
    exact W.gluing (F.map a) (F.map b) (F.map d) (F.map p)
      (hF.cofibration _ hi) (hF.cofibration _ hi') (hF.pushout hi h) (hF.pushout hi' h')
      (by simpa only [F.map_comp] using congrArg F.map ei)
      (by simpa only [F.map_comp] using congrArg F.map ef)
      (by simpa only [F.map_comp] using congrArg F.map eg)
      (by simpa only [F.map_comp] using congrArg F.map ej) ha hb hd

@[simp] theorem withInverseImageWeak_cof : (withInverseImageWeak hF).cof = V.cof := rfl

@[simp] theorem withInverseImageWeak_zero : (withInverseImageWeak hF).zero = V.zero := rfl

/-- Weakness is precisely the target weak predicate on the actual mapped morphism. -/
@[simp] theorem withInverseImageWeak_weq_iff {X Y : C} (f : X ⟶ Y) :
    (withInverseImageWeak hF).weq f ↔ W.weq (F.map f) := Iff.rfl

/-- The unchanged source weak class is contained in the genuine relative class. -/
def inverseImageWeakNested : Fibration.NestedWeakEquivalences V where
  coarse := withInverseImageWeak hF
  cof_eq := rfl
  zero_eq := rfl
  le_weq := fun _ _ f hf ↦ hF.weak f hf

/-- The same functor is exact for the newly constructed source weak class. -/
theorem withInverseImageWeak_exact :
    IsExact (withInverseImageWeak hF).cof (withInverseImageWeak hF).weq W.cof W.weq F where
  zero := hF.zero
  cofibration := hF.cofibration
  weak _ h := h
  pushout := hF.pushout

instance withInverseImageWeak_twoOutOfThree [W.weq.HasTwoOutOfThreeProperty] :
    (withInverseImageWeak hF).weq.HasTwoOutOfThreeProperty :=
  inferInstanceAs (W.weq.inverseImage F).HasTwoOutOfThreeProperty

end Structure
namespace Fibration.ExtensionAxiom
variable {W : Structure D} (he : Fibration.ExtensionAxiom W)

include he in
/-- Extension applies to displayed cofibers with any actual zero corner. -/
theorem extension_of_isZero {Z : D} (hZ : IsZero Z)
    {A B Q A' B' Q' : D}
    {i : A ⟶ B} {q : B ⟶ Q} {i' : A' ⟶ B'} {q' : B' ⟶ Q'}
    (hi : W.cof i) (hi' : W.cof i')
    (h : IsPushout i (hZ.from_ A) q (hZ.to_ Q))
    (h' : IsPushout i' (hZ.from_ A') q' (hZ.to_ Q'))
    (a : A ⟶ A') (b : B ⟶ B') (c : Q ⟶ Q')
    (wi : i ≫ b = a ≫ i') (wq : q ≫ c = b ≫ q')
    (ha : W.weq a) (hc : W.weq c) : W.weq b := by
  have transfer {X Y R : D} {j : X ⟶ Y} {r : Y ⟶ R}
      (hp : IsPushout j (hZ.from_ X) r (hZ.to_ R)) :
      IsPushout j (W.isZero.from_ X) r (W.isZero.to_ R) := by
    apply hp.of_iso (Iso.refl _) (Iso.refl _) (hZ.iso W.isZero) (Iso.refl _)
    · simp
    · exact W.isZero.eq_of_tgt _ _
    · simp
    · exact hZ.eq_of_src _ _
  exact he.extension hi hi' (transfer h) (transfer h') a b c wi wq ha hc

end Fibration.ExtensionAxiom
namespace Structure
variable (hF : IsExact V.cof V.weq W.cof W.weq F)

/-- The target extension axiom descends along the actual mapped cofiber squares. -/
theorem withInverseImageWeak_extensionAxiom (he : Fibration.ExtensionAxiom W) :
    Fibration.ExtensionAxiom (withInverseImageWeak hF) where
  extension {A B Q A' B' Q'} {i q i' q'} hi hi' h h' a b c wi wq ha hc := by
    let hZ := hF.zero V.isZero
    have mapped {X Y R : C} {j : X ⟶ Y} {r : Y ⟶ R}
        (hj : V.cof j) (hp : IsPushout j (V.isZero.from_ X) r (V.isZero.to_ R)) :
        IsPushout (F.map j) (hZ.from_ (F.obj X)) (F.map r) (hZ.to_ (F.obj R)) := by
      convert! hF.pushout hj hp using 1
      · exact hZ.eq_of_tgt _ _
      · exact hZ.eq_of_src _ _
    exact he.extension_of_isZero hZ (hF.cofibration _ hi) (hF.cofibration _ hi')
      (mapped hi h) (mapped hi' h') (F.map a) (F.map b) (F.map c)
      (by simpa only [F.map_comp] using congrArg F.map wi)
      (by simpa only [F.map_comp] using congrArg F.map wq) ha hc

end Structure
end CategoryTheory.Waldhausen
