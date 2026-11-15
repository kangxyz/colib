/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorSingle
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ProjectiveBifunctorShift
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.CochainSingleParameterShift
import StacksFrontier.CategoryTheory.Localization.BifunctorCommShiftTwoLiftingIso
import StacksFrontier.CategoryTheory.Shift.DetectingCommShift

/-! # Shift in the first variable with a fixed degree-zero parameter -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory HomologicalComplex

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "c" => ComplexShape.up ℤ
local notation "S(" K ")" => CochainComplex.singleFunctor PST(K) (0 : ℤ)

variable (F : PST(k) ⥤ PST(k) ⥤ PST(k)) [F.Additive] [∀ P, (F.obj P).Additive]

local instance (P : PST(k)) : (F.flip.obj P).Additive where
  map_add := by
    intro X Y f g
    change (F.map (f + g)).app P = (F.map f).app P + (F.map g).app P
    exact NatTrans.congr_app (F.map_add (f := f) (g := g)) P

/-- A degree-zero right coefficient introduces no sign in the varied shift. -/
theorem mapBifunctorSingleRightNatIso_commShift (P : PST(k)) :
    NatTrans.CommShift (mapBifunctorSingleRightNatIso F P).hom ℤ := by
  refine ⟨fun n => NatTrans.ext (funext fun K => ?_)⟩
  change (((F.map₂CochainComplex).flip.obj ((S(k)).obj P)).commShiftIso n).hom.app K ≫
        (mapBifunctorSingleRightIso F K P).hom⟦n⟧' =
      (mapBifunctorSingleRightIso F (K⟦n⟧) P).hom ≫
        (((F.flip.obj P).mapHomologicalComplex c).commShiftIso n).hom.app K
  rw [Functor.commShiftIso_map₂CochainComplex_flip_hom_app]
  exact CochainComplex.mapBifunctorSingleRightIso_commShift₁ F P K n

set_option maxHeartbeats 650000 in
-- Give the localization structure and the native homotopy shift their explicit functor types.
/-- The honest homotopy comparison preserves the native signed shift in the first variable. -/
theorem signedTotalHomotopySingleRightIso_commShift (P : PST(k)) :
    NatTrans.CommShift (signedTotalHomotopySingleRightIso F P).hom ℤ := by
  let Q := HomotopyCategory.quotient PST(k) c
  let W := HomologicalComplex.homotopyEquivalences PST(k) c
  let G := F.map₂CochainComplex ⋙ (Functor.whiskeringRight _ _ _).obj Q
  let H := signedTotalHomotopyBifunctor F
  let : Localization.Lifting₂ Q Q W W G H := signedTotalHomotopyBifunctorLifting F
  let S₀ := (S(k)).obj P
  let T := (F.flip.obj P)
  let a : Q ⋙ H.flip.obj (Q.obj S₀) ≅ G.flip.obj S₀ :=
    (Localization.Lifting₂.iso Q Q W W G.flip H.flip).app S₀
  let b := T.mapHomotopyCategoryFactors c
  let e := signedTotalHomotopySingleRightIso F P
  let : Q.EssSurj := ⟨fun K => ⟨K.as, ⟨Iso.refl _⟩⟩⟩
  let : NatTrans.CommShift (F₁ := Q ⋙ H.flip.obj (Q.obj S₀)) (F₂ := G.flip.obj S₀) a.hom ℤ :=
    Localization.lifting₂_iso_hom_app_commShift Q Q W W G.flip H.flip S₀
  let : NatTrans.CommShift (mapBifunctorSingleRightNatIso F P).hom ℤ :=
    mapBifunctorSingleRightNatIso_commShift F P
  apply NatTrans.commShift_of_whiskerLeft Q e.hom
  let d := a.hom ≫ Functor.whiskerRight (mapBifunctorSingleRightNatIso F P).hom Q ≫ b.inv
  have h : Functor.whiskerLeft Q e.hom = d := by
    apply NatTrans.ext
    funext K
    change Q.map (mapBifunctorSingleRightIso F K P).hom =
      𝟙 _ ≫ Q.map (mapBifunctorSingleRightIso F K P).hom ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
  rw [h]
  let : NatTrans.CommShift b.hom ℤ := inferInstanceAs
    (NatTrans.CommShift (T.mapHomotopyCategoryFactors c).hom ℤ)
  let : NatTrans.CommShift b.inv ℤ := NatTrans.CommShift.of_iso_inv b ℤ
  let v : G.flip.obj S₀ ⟶ (T.mapHomologicalComplex c) ⋙ Q :=
    Functor.whiskerRight (mapBifunctorSingleRightNatIso F P).hom Q
  let : NatTrans.CommShift v ℤ := inferInstanceAs
    (NatTrans.CommShift (Functor.whiskerRight (mapBifunctorSingleRightNatIso F P).hom Q) ℤ)
  change NatTrans.CommShift (a.hom ≫ v ≫ b.inv) ℤ
  let : NatTrans.CommShift (v ≫ b.inv) ℤ := NatTrans.CommShift.comp v b.inv ℤ
  exact NatTrans.CommShift.comp a.hom (v ≫ b.inv) ℤ

end AlgebraicGeometry.PresheafWithTransfers
