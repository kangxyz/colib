/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.Coefficients
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.Triangulated
import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift

/-! # Termwise maps on the original projective derived functors -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

set_option quotPrecheck false in
local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ

variable [HasDerivedCategory.{w} PST(k)]

/-- A map of coefficient functors induces the termwise map on the selected projective model. -/
def projectiveDerivedMinusFunctorMap {G H : PST(k) ⥤ PST(k)} [G.Additive] [H.Additive]
    (f : G ⟶ H) : projectiveDerivedMinusFunctor k G ⟶ projectiveDerivedMinusFunctor k H := by
  let E := boundedAboveProjectiveEquivalence k
  let I := (boundedAboveProjectiveCondition k).ι
  let Q := DerivedCategory.Qh (C := PST(k))
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let ff := Functor.FullyFaithful.ofFullyFaithful V
  apply (ff.whiskeringRight _).preimage
  exact Functor.whiskerLeft (E.inverse ⋙ I)
    (Functor.whiskerRight (f.mapHomotopyCategory c) Q)

/-- The map of coefficient functors acts termwise on the selected projective model. -/
theorem projectiveDerivedMinusFunctorMap_map_app
    {G H : PST(k) ⥤ PST(k)} [G.Additive] [H.Additive] (f : G ⟶ H)
    (K : DerivedCategory.Minus PST(k)) :
    DerivedCategory.Minus.ι.map ((projectiveDerivedMinusFunctorMap f).app K) =
      DerivedCategory.Qh.map ((f.mapHomotopyCategory c).app
        ((boundedAboveProjectiveEquivalence k).inverse.obj K).obj) := by
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let Q := DerivedCategory.Qh (C := PST(k))
  let J := (boundedAboveProjectiveEquivalence k).inverse ⋙
    (boundedAboveProjectiveCondition k).ι
  let R := projectiveDerivedMinusFunctor k G
  let R' := projectiveDerivedMinusFunctor k H
  let t : R ⋙ V ⟶ R' ⋙ V :=
    Functor.whiskerLeft J (Functor.whiskerRight (f.mapHomotopyCategory c) Q)
  let ff := (Functor.FullyFaithful.ofFullyFaithful V).whiskeringRight (DerivedCategory.Minus PST(k))
  exact NatTrans.congr_app (ff.map_preimage (X := R) (Y := R') t) K

private theorem natTrans_commShift_trans {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] {F G H : C ⥤ D}
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (a : F ⟶ G) (b : G ⟶ H)
    (ha : NatTrans.CommShift a ℤ) (hb : NatTrans.CommShift b ℤ) :
    NatTrans.CommShift (a ≫ b) ℤ := by
  let := ha
  let := hb
  infer_instance

set_option maxHeartbeats 1500000 in
-- The comparison carries the native shifts through three functor categories.
/-- The termwise map of the original derived coefficient functors commutes with shift. -/
theorem projectiveDerivedMinusFunctorMap_commShift
    {G H : PST(k) ⥤ PST(k)} [G.Additive] [H.Additive] (f : G ⟶ H) :
    NatTrans.CommShift (projectiveDerivedMinusFunctorMap f) ℤ := by
  let V := DerivedCategory.Minus.ι (C := PST(k))
  let E := (boundedAboveProjectiveEquivalence k).inverse
  let I := (boundedAboveProjectiveCondition k).ι
  let Q := DerivedCategory.Qh (C := PST(k))
  let A := G.mapHomotopyCategory c
  let B := H.mapHomotopyCategory c
  let P := projectiveHomotopyMapToDerivedMinus k G
  let R := projectiveHomotopyMapToDerivedMinus k H
  let t := f.mapHomotopyCategory c
  let a : P ⋙ V ≅ I ⋙ A ⋙ Q := Iso.refl _
  let b : R ⋙ V ≅ I ⋙ B ⋙ Q := Iso.refl _
  let j : projectiveDerivedMinusFunctor k G ≅ E ⋙ P := Iso.refl _
  let j' : projectiveDerivedMinusFunctor k H ≅ E ⋙ R := Iso.refl _
  let α := Functor.isoWhiskerRight j V ≪≫ Functor.associator E P V
  let β := Functor.isoWhiskerRight j' V ≪≫ Functor.associator E R V
  let : NatTrans.CommShift j.hom ℤ := projectiveDerivedMinusFunctor_comp_projective_commShift k G
  let : NatTrans.CommShift j'.hom ℤ := projectiveDerivedMinusFunctor_comp_projective_commShift k H
  let hj : NatTrans.CommShift (Functor.whiskerRight j.hom V) ℤ := inferInstance
  let hj' : NatTrans.CommShift (Functor.whiskerRight j'.hom V) ℤ := inferInstance
  let : NatTrans.CommShift α.hom ℤ :=
    natTrans_commShift_trans _ _ hj (NatTrans.CommShift.associator (F₁ := E) P V ℤ)
  let : NatTrans.CommShift β.hom ℤ :=
    natTrans_commShift_trans _ _ hj' (NatTrans.CommShift.associator (F₁ := E) R V ℤ)
  let : NatTrans.CommShift β.inv ℤ := NatTrans.CommShift.of_iso_inv β ℤ
  let : NatTrans.CommShift a.hom ℤ := projectiveHomotopyMapToDerivedMinus_comp_ι_commShift k G
  let : NatTrans.CommShift b.hom ℤ := projectiveHomotopyMapToDerivedMinus_comp_ι_commShift k H
  let T := projectiveDerivedMinusFunctorMap f
  let u : projectiveDerivedMinusFunctor k G ⋙ V ⟶ projectiveDerivedMinusFunctor k H ⋙ V :=
    α.hom ≫ Functor.whiskerLeft E a.hom ≫
      Functor.whiskerLeft E (Functor.whiskerLeft I (Functor.whiskerRight t Q)) ≫
      Functor.whiskerLeft E b.inv ≫ β.inv
  have hu : Functor.whiskerRight T V = u := by
    apply NatTrans.ext
    funext X
    have h := projectiveDerivedMinusFunctorMap_map_app f X
    change V.map (T.app X) = _ at h
    rw [Functor.whiskerRight_app, h]
    simp only [u, α, β, a, b, j, j', Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerRight_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app, Category.comp_id, Category.id_comp]
    let X₀ := (projectiveDerivedMinusFunctor k G).obj X
    let Y₀ := (projectiveDerivedMinusFunctor k H).obj X
    let z : V.obj X₀ ⟶ V.obj Y₀ := Q.map (t.app (I.obj (E.obj X)))
    change z = V.map (𝟙 X₀) ≫ 𝟙 (V.obj X₀) ≫ z ≫ 𝟙 (V.obj Y₀) ≫ V.map (𝟙 Y₀)
    rw [V.map_id, V.map_id, Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
  apply NatTrans.CommShift.of_comp_faithful (G := V) (h := ?_)
  change NatTrans.CommShift (Functor.whiskerRight T V) ℤ
  rw [hu]
  let u₁ := Functor.whiskerLeft E a.hom
  let u₂ := Functor.whiskerLeft E (Functor.whiskerLeft I (Functor.whiskerRight t Q))
  let u₃ := Functor.whiskerLeft E b.inv
  let : NatTrans.CommShift b.inv ℤ := NatTrans.CommShift.of_iso_inv b ℤ
  let : NatTrans.CommShift t ℤ := inferInstanceAs (NatTrans.CommShift (f.mapHomotopyCategory c) ℤ)
  let : NatTrans.CommShift u₁ ℤ := by dsimp only [u₁]; infer_instance
  let : NatTrans.CommShift u₂ ℤ := by dsimp only [u₂]; infer_instance
  let : NatTrans.CommShift u₃ ℤ := by dsimp only [u₃]; infer_instance
  change NatTrans.CommShift (α.hom ≫ u₁ ≫ u₂ ≫ u₃ ≫ β.inv) ℤ
  exact natTrans_commShift_trans _ _ inferInstance (natTrans_commShift_trans _ _ inferInstance
    (natTrans_commShift_trans _ _ inferInstance (natTrans_commShift_trans _ _ inferInstance
      inferInstance)))

end AlgebraicGeometry.PresheafWithTransfers
