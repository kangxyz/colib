/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.CategoryTheory.Waldhausen.Fibration.InverseImageWeak
public import Colib.CategoryTheory.Waldhausen.Fibration.ExactChangeWeak
public import Colib.KTheory.Waldhausen.Iterated.Prespectrum
/-! # Original diagrams with weak equivalences detected by an exact transformation

Only the source weak class changes. The native category, cofibrations and literal chosen zero
are retained, with the original component functors and strict squares.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Waldhausen CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u v w
namespace CategoryTheory.Waldhausen.IteratedS.InverseImageModelDiagram
variable {I : Type u} [Category.{v} I] {A B : I ⥤ WideSubcategory preservesZero.{w}} (S : A ⟶ B)

/-- The same source category, cofibrations and zero, with actual detected weakness. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/InverseImageModelDiagram.lean:27"
  "adaptation" "Original detected weak structure on the same category and chosen zero"]
def model (i : I) : WideSubcategory preservesZero.{w} :=
  ⟨{ Obj := (A.obj i).obj.Obj,
     waldhausen := Structure.withInverseImageWeak (S.app i).hom.isExact }⟩

/-- The original component now reflects the chosen weak class by definition. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/InverseImageModelDiagram.lean:31"
  "adaptation" "Original detected weak structure on the same category and chosen zero"]
def component (i : I) : model S i ⟶ B.obj i :=
  ⟨⟨(S.app i).hom.toFunctor,
    Structure.withInverseImageWeak_exact (S.app i).hom.isExact⟩, (S.app i).property⟩

/-- Original source transitions are exact for the detected weak classes. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/InverseImageModelDiagram.lean:37"
  "adaptation" "Original detected weak structure on the same category and chosen zero"]
theorem map_exact {i j : I} (f : i ⟶ j) :
    IsExact (model S i).obj.waldhausen.cof (model S i).obj.waldhausen.weq
      (model S j).obj.waldhausen.cof (model S j).obj.waldhausen.weq (A.map f).hom.toFunctor := by
  have he : IsExact (Structure.withInverseImageWeak (S.app i).hom.isExact).cof
      (Structure.withInverseImageWeak (S.app i).hom.isExact).weq
      (B.obj j).obj.waldhausen.cof (B.obj j).obj.waldhausen.weq
      ((A.map f).hom.toFunctor ⋙ (S.app j).hom.toFunctor) := by
    have h := congrArg (fun k => k.hom.toFunctor) (S.naturality f)
    change (A.map f).hom.toFunctor ⋙ (S.app j).hom.toFunctor =
      (S.app i).hom.toFunctor ⋙ (B.map f).hom.toFunctor at h
    rw [h]
    exact (component S i).hom.isExact.comp (B.map f).hom.isExact
  exact {
    zero := (A.map f).hom.isExact.zero
    cofibration := (A.map f).hom.isExact.cofibration
    weak := fun k hk => he.weak k hk
    pushout := (A.map f).hom.isExact.pushout }

/-- The original transitions retain their literal chosen zeros. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/InverseImageModelDiagram.lean:56"
  "adaptation" "Original detected weak structure on the same category and chosen zero"]
def map {i j : I} (f : i ⟶ j) : model S i ⟶ model S j :=
  ⟨⟨(A.map f).hom.toFunctor, map_exact S f⟩, (A.map f).property⟩

/-- The detected source structures form a strict diagram. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/InverseImageModelDiagram.lean:62"
  "adaptation" "Original detected weak structure on the same category and chosen zero"]
def diagram : I ⥤ WideSubcategory preservesZero.{w} where
  obj := model S
  map := map S
  map_id i := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    have h := congrArg (fun k => k.hom.toFunctor) (A.map_id i)
    exact h
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    have h := congrArg (fun k => k.hom.toFunctor) (A.map_comp f g)
    exact h

/-- The unchanged original component functors form an actual Model transformation. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/InverseImageModelDiagram.lean:75"
  "adaptation" "Original detected weak structure on the same category and chosen zero"]
def restriction : diagram S ⟶ B where
  app := component S
  naturality i j f := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    have h := congrArg (fun k => k.hom.toFunctor) (S.naturality f)
    exact h

/-- The source identity changes only the weak class. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/InverseImageModelDiagram.lean:83"
  "adaptation" "Original detected weak structure on the same category and chosen zero"]
def changeWeak : A ⟶ diagram S where
  app i := ⟨⟨𝟭 _,
    Fibration.changeWeak_exact (Structure.inverseImageWeakNested (S.app i).hom.isExact)⟩, rfl⟩
  naturality i j f := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact (Functor.comp_id _).trans (Functor.id_comp _).symm

/-- The two actual transformations factor the original map strictly. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/InverseImageModelDiagram.lean:93"
  "adaptation" "Original detected weak structure on the same category and chosen zero"]
theorem factor : changeWeak S ≫ restriction S = S := by
  apply NatTrans.ext
  funext i
  apply WideSubcategory.hom_ext
  apply SmallWaldhausenCategory.Hom.ext
  exact Functor.id_comp _

end CategoryTheory.Waldhausen.IteratedS.InverseImageModelDiagram
