/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Preadditive.IntegralConvolutionAssociator
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# Swap of the integral convolution

The swap applies the given correspondence comparison and interchanges
the two coefficient sections in each generator.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory TensorProduct

universe u v w

namespace CategoryTheory.Preadditive.ConvolutionRepresented
open CategoryTheory.Preadditive.Convolution (integerModuleFunctor)

variable {C : Type u} [Category.{v} C] [Preadditive C]


variable (F : C ⥤ C ⥤ C) (s : F ≅ F.flip)

/-- Right-compose the original label with the correspondence swap. -/
def convolutionSwapFactor (X Y Z : C) :
    (convolutionCorrespondenceModule F X).obj (Y, Z) ⟶
      (convolutionCorrespondenceModule F X).obj (Z, Y) :=
  (preadditiveCoyoneda.obj (op X) ⋙ AddCommGrpCat.uliftFunctor.{max u v w, v} ⋙
    integerModuleFunctor).map ((s.hom.app Y).app Z)

/-- The swap on each of the three original tensor factors. -/
def convolutionSwapPairing (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (X Y Z : C) :
    ((convolutionDiagram F P Q X).obj (op (Y, Z))).obj (Y, Z) ⟶
      convolutionSections F Q P X :=
  ((β_ (integerModuleFunctor.obj (sections P Y)) (integerModuleFunctor.obj (sections Q
      Z))).hom
      ⊗ₘ convolutionSwapFactor F s X Y Z) ≫ coend.ι (convolutionDiagram F Q P X) (Z, Y)

/-- The swap pairing on the three pure coefficient and correspondence factors. -/
theorem convolutionSwapPairing_tmul (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (X Y
    Z : C)
    (p : sections P Y) (q : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionSwapPairing F s P Q X Y Z ((p ⊗ₜ[ℤ] q) ⊗ₜ[ℤ] ULift.up a) =
      convolutionGenerator F Q P X Z Y q p (a ≫ (s.hom.app Y).app Z) :=
  rfl

set_option maxHeartbeats 750000 in
-- The tensor factors in the two dinaturality maps use nested module bundles.
/-- The swap pairing respects the two original transfer relations. -/
theorem convolutionSwapPairing_dinatural (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w}))
    (X : C)
    {Y Y' Z Z' : C} (f : Y ⟶ Y') (g : Z ⟶ Z') :
    let D := convolutionDiagram F P Q X
    let h : (Y, Z) ⟶ (Y', Z') := (f, g)
    (D.map h.op).app (Y, Z) ≫ convolutionSwapPairing F s P Q X Y Z =
      (D.obj (op (Y', Z'))).map h ≫ convolutionSwapPairing F s P Q X Y' Z' := by
  let h : (Y, Z) ⟶ (Y', Z') := (f, g)
  let A := convolutionCoefficientModule P Q
  let B := convolutionCorrespondenceModule F X
  let W := ModuleCat.of ℤ ((sections P Y' ⊗[ℤ] sections Q Z') ⊗[ℤ]
    ULift.{max u v w} (X ⟶ (F.obj Y).obj Z))
  let l : W ⟶ convolutionSections F Q P X :=
    (A.map h.op ⊗ₘ B.map (𝟙 (Y, Z))) ≫ convolutionSwapPairing F s P Q X Y Z
  let r : W ⟶ convolutionSections F Q P X :=
    (A.map (𝟙 (op (Y', Z'))) ⊗ₘ B.map h) ≫ convolutionSwapPairing F s P Q X Y' Z'
  change l = r
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  rintro pq ⟨a⟩
  refine TensorProduct.inductionOn pq ?_ ?_
  · intro p q
    change l ((p ⊗ₜ[ℤ] q) ⊗ₜ[ℤ] ULift.up a) = r ((p ⊗ₜ[ℤ] q)
        ⊗ₜ[ℤ] ULift.up a)
    dsimp only [l, r]
    rw [B.map_id, A.map_id]
    change convolutionSwapPairing F s P Q X Y Z
        (((transfer P f p) ⊗ₜ[ℤ] (transfer Q g q)) ⊗ₜ[ℤ] ULift.up a) =
      convolutionSwapPairing F s P Q X Y' Z'
        ((p ⊗ₜ[ℤ] q) ⊗ₜ[ℤ] ULift.up (a ≫ convolutionCorrespondenceMap F f g))
    rw [convolutionSwapPairing_tmul, convolutionSwapPairing_tmul,
      convolutionGenerator_transfer, Category.assoc, Category.assoc]
    apply congrArg (convolutionGenerator F Q P X Z' Y' q p)
    apply congrArg (a ≫ ·)
    unfold convolutionCorrespondenceMap Convolution.bifunctorMap
    have h₀ := (Functor.uncurry.map s.hom).naturality h
    change ((F.map f).app Z ≫ (F.obj Y').map g) ≫ (s.hom.app Y').app Z' =
      (s.hom.app Y).app Z ≫ (F.obj Z).map f ≫ (F.map g).app Y' at h₀
    rw [← (F.map g).naturality f]
    exact h₀.symm
  · intro p q hp hq
    rw [TensorProduct.add_tmul, l.hom.map_add, r.hom.map_add, hp, hq]

/-- Swap the two generators before taking the coend. -/
def convolutionSwapApp (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (X : C) :
    convolutionSections F P Q X ⟶ convolutionSections F Q P X :=
  coend.desc («F» := convolutionDiagram F P Q X)
    (fun yz => convolutionSwapPairing F s P Q X yz.1 yz.2)
    (fun i j (fg : i ⟶ j) => convolutionSwapPairing_dinatural F s P Q X fg.1 fg.2)

private theorem convolutionSwapApp_generator (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v
    w})) (X Y Z : C)
    (p : sections P Y) (q : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    convolutionSwapApp F s P Q X (convolutionGenerator F P Q X Y Z p q a) =
      convolutionGenerator F Q P X Z Y q p (a ≫ (s.hom.app Y).app Z) := by
  change (coend.ι (convolutionDiagram F P Q X) (Y, Z) ≫ convolutionSwapApp F s P Q X)
      ((p ⊗ₜ[ℤ] q) ⊗ₜ[ℤ] ULift.up a) = _
  let D := convolutionDiagram F P Q X
  let f (YZ : (C × C)) := convolutionSwapPairing F s P Q X YZ.1 YZ.2
  let z : ((D.obj (op (Y, Z))).obj (Y, Z)) := (p ⊗ₜ[ℤ] q) ⊗ₜ[ℤ] ULift.up a
  have h := coend.ι_desc (F := D) f
    (fun i j (fg : i ⟶ j) => convolutionSwapPairing_dinatural F s P Q X fg.1 fg.2) (Y, Z)
  exact (ConcreteCategory.congr_hom h z).trans (convolutionSwapPairing_tmul F s P Q X Y Z
      p q a)

/-- The swap of the coend presheaf acts on the original sections and correspondences. -/
def convolutionSwapHom (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) :
    convolutionPresheaf F P Q ⟶ convolutionPresheaf F Q P :=
  ObjectProperty.homMk
    { app X := (forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat).map
        (convolutionSwapApp F s P Q X.unop)
      naturality X X' β := by
        let V := forget₂ (ModuleCat.{max u v w} ℤ) AddCommGrpCat.{max u v w}
        change V.map (convolutionTransfer F P Q β.unop) ≫
            V.map (convolutionSwapApp F s P Q X'.unop) =
          V.map (convolutionSwapApp F s P Q X.unop) ≫
            V.map (convolutionTransfer F Q P β.unop)
        rw [← V.map_comp, ← V.map_comp]
        apply congrArg V.map
        apply convolutionSections_hom_ext
        intro Y Z p q a
        simp only [ModuleCat.comp_apply, convolutionTransfer_generator,
          convolutionSwapApp_generator, Category.assoc] }

theorem convolutionSwapHom_generator (P Q : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})) (X
    Y Z : C)
    (p : sections P Y) (q : sections Q Z) (a : X ⟶ (F.obj Y).obj Z) :
    (convolutionSwapHom F s P Q).hom.app (op X) (convolutionGenerator F P Q X Y Z p q a) =
      convolutionGenerator F Q P X Z Y q p (a ≫ (s.hom.app Y).app Z) :=
  convolutionSwapApp_generator F s P Q X Y Z p q a

/-- The convolution swap commutes with maps of each coefficient. -/
theorem convolutionSwapHom_naturality {P P' Q Q' : (Cᵒᵖ ⥤+ AddCommGrpCat.{max u v w})}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    convolutionMap F f g ≫ convolutionSwapHom F s P' Q' =
      convolutionSwapHom F s P Q ≫ convolutionMap F g f := by
  apply convolutionPresheaf_hom_ext
  intro X Y Z p q a
  change (convolutionSwapHom F s P' Q').hom.app (op X)
      ((convolutionMap F f g).hom.app (op X) (convolutionGenerator F P Q X Y Z p q a)) =
    (convolutionMap F g f).hom.app (op X)
      ((convolutionSwapHom F s P Q).hom.app (op X) (convolutionGenerator F P Q X Y Z p q a))
  rw [convolutionMap_generator, convolutionSwapHom_generator, convolutionSwapHom_generator,
    convolutionMap_generator]

variable (hs : ∀ Y Z, (s.hom.app Y).app Z ≫ (s.hom.app Z).app Y = 𝟙 _)

/-- The original symmetry of correspondences induces the swap of convolutions. -/
def convolutionSwap :
    convolutionBifunctor F ≅ (convolutionBifunctor F).flip :=
  NatIso.ofComponents
    (fun P => NatIso.ofComponents
      (fun Q =>
        { hom := convolutionSwapHom F s P Q
          inv := convolutionSwapHom F s Q P
          hom_inv_id := by
            apply convolutionPresheaf_hom_ext
            intro X Y Z p q a
            change (convolutionSwapHom F s Q P).hom.app (op X)
              ((convolutionSwapHom F s P Q).hom.app (op X)
                (convolutionGenerator F P Q X Y Z p q a)) = _
            rw [convolutionSwapHom_generator, convolutionSwapHom_generator, Category.assoc,
              hs, Category.comp_id]
            rfl
          inv_hom_id := by
            apply convolutionPresheaf_hom_ext
            intro X Y Z q p a
            change (convolutionSwapHom F s P Q).hom.app (op X)
              ((convolutionSwapHom F s Q P).hom.app (op X)
                (convolutionGenerator F Q P X Y Z q p a)) = _
            rw [convolutionSwapHom_generator, convolutionSwapHom_generator, Category.assoc,
              hs, Category.comp_id]
            rfl })
      (fun g => convolutionSwapHom_naturality F s (𝟙 P) g))
    (fun f => by
      apply NatTrans.ext
      funext Q
      exact convolutionSwapHom_naturality F s f (𝟙 Q))

end CategoryTheory.Preadditive.ConvolutionRepresented
