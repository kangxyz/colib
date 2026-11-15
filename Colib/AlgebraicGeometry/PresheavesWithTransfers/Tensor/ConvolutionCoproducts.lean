/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Tensor.ConvolutionFunctor
import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Coproducts of transfer convolutions

With a fixed left coefficient, each term of the native multispan for the
convolution is an evaluation followed by tensoring with fixed modules.
The native colimit of this diagram then preserves coproducts.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped MonoidalCategory

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "PST(" K ")" => TransferCoefficients K
local notation "MZ(" K ")" => IntegerCoefficients K
local notation "CC(" K ")" => Cor K × Cor K
local notation "D(" K ")" => WalkingMultispan (multispanShapeCoend CC(K))

variable (F : Cor k ⥤ Cor k ⥤ Cor k) (P : PST(k)) (X : Cor k)

private def convolutionEvaluation (W : Cor k) : PST(k) ⥤ MZ(k) :=
  forget ⋙ (evaluation (Cor k)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op W) ⋙ integerModuleFunctor

private def tensorEvaluation (a b : CC(k)) : PST(k) ⥤ MZ(k) :=
  convolutionEvaluation a.2 ⋙
    MonoidalCategory.tensorLeft (integerModuleFunctor.obj (sections P a.1)) ⋙
      MonoidalCategory.tensorRight ((convolutionCorrespondenceModule F X).obj b)

private def convolutionMultispanMap {Q Q' : PST(k)} (g : Q ⟶ Q') :
    (multispanIndexCoend (convolutionDiagram F P Q X)).multispan ⟶
      (multispanIndexCoend (convolutionDiagram F P Q' X)).multispan := by
  let a := convolutionMapDiagram F (𝟙 P) g X
  refine
    { app := fun w => match w with
        | .left f => (a.app (op f.right)).app f.left
        | .right x => (a.app (op x)).app x
      naturality := ?_ }
  intro J K g
  change WalkingMultispan.Hom J K at g
  cases g with
  | id => cases J <;> simp
  | fst w => exact NatTrans.congr_app (a.naturality w.hom.op) w.left
  | snd w => exact (a.app (op w.right)).naturality w.hom

private def convolutionMultispanFunctor : PST(k) ⥤ D(k) ⥤ MZ(k) where
  obj Q := (multispanIndexCoend (convolutionDiagram F P Q X)).multispan
  map := convolutionMultispanMap F P X
  map_id Q := by
    apply NatTrans.ext
    funext w
    cases w with
    | left a => exact (tensorEvaluation F P X a.right a.left).map_id Q
    | right a => exact (tensorEvaluation F P X a a).map_id Q
  map_comp f g := by
    apply NatTrans.ext
    funext w
    cases w with
    | left a => exact (tensorEvaluation F P X a.right a.left).map_comp f g
    | right a => exact (tensorEvaluation F P X a a).map_comp f g

private def convolutionMultispanEvaluationIso (w : D(k)) :
    convolutionMultispanFunctor F P X ⋙ (evaluation D(k) MZ(k)).obj w ≅
      match w with
      | .left f => tensorEvaluation F P X f.right f.left
      | .right a => tensorEvaluation F P X a a := by
  cases w <;> exact NatIso.ofComponents (fun _ => Iso.refl _)

private def convolutionSectionsFunctor : PST(k) ⥤ MZ(k) where
  obj Q := convolutionSections F P Q X
  map g := convolutionMapApp F (𝟙 P) g X
  map_id Q := by
    apply convolutionSections_hom_ext
    intro Y Z s t a
    rw [convolutionMapApp_generator]
    rfl
  map_comp f g := by
    apply convolutionSections_hom_ext
    intro Y Z s t a
    simp only [ModuleCat.comp_apply, convolutionMapApp_generator]
    rfl

private def convolutionSectionsFunctorIso [HasColimitsOfShape D(k) MZ(k)] :
    convolutionSectionsFunctor F P X ≅ convolutionMultispanFunctor F P X ⋙ colim :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {P₁ P₂} g => by
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply coend.hom_ext
    intro YZ
    let τ := convolutionMapDiagram F (𝟙 P) g X
    let t := convolutionMultispanMap F P X g
    have h := coend.ι_map τ YZ
    exact h.trans (ι_colimMap t (.right YZ)).symm)

private theorem convolutionSections_preservesCoproducts (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) (convolutionSectionsFunctor F P X) := by
  let A := AddCommGrpCat.{u + 1}
  let : HasColimitsOfSize.{u + 1, u + 1} AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfSize.{u + 1, u + 1, u + 1}
  let : HasColimitsOfSize.{u + 1, u + 1} MZ(k) := inferInstance
  let G := forget₂ MZ(k) A
  let e : integerModuleFunctor ⋙ G ≅ 𝟭 A := NatIso.ofComponents (fun _ => Iso.refl _)
  let : PreservesColimitsOfShape (Discrete I) (integerModuleFunctor ⋙ G) :=
    preservesColimitsOfShape_of_natIso e.symm
  let : PreservesColimitsOfShape (Discrete I) integerModuleFunctor :=
    preservesColimitsOfShape_of_reflects_of_preserves _ G
  let H := convolutionMultispanFunctor F P X
  let : PreservesColimitsOfShape (Discrete I) H :=
    preservesColimitsOfShape_of_evaluation H (Discrete I) (fun w => by
      let e' := convolutionMultispanEvaluationIso F P X w
      have : PreservesColimitsOfShape (Discrete I)
          (match w with
          | .left f => tensorEvaluation F P X f.right f.left
          | .right a => tensorEvaluation F P X a a) := by
        cases w <;> unfold tensorEvaluation convolutionEvaluation <;> infer_instance
      exact preservesColimitsOfShape_of_natIso e'.symm)
  exact preservesColimitsOfShape_of_natIso (convolutionSectionsFunctorIso F P X).symm

/-- Convolution with a fixed first presheaf preserves coproducts in the second presheaf. -/
theorem convolution_preservesCoproducts_right (I : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete I) ((convolutionBifunctor F).obj P) := by
  let A := AddCommGrpCat.{u + 1}
  let : HasColimitsOfShape (Discrete I) A := AddCommGrpCat.hasColimitsOfShape
  let U : PST(k) ⥤ (Cor k)ᵒᵖ ⥤ A := forget
  let V := forget₂ MZ(k) A
  let e : U.FullyFaithful := ObjectProperty.fullyFaithfulι (additiveFunctor (Cor k)ᵒᵖ A)
  let : U.Full := e.full
  let : U.Faithful := e.faithful
  let : ReflectsColimitsOfShape (Discrete I) U := inferInstance
  let B := (convolutionBifunctor F).obj P
  have : PreservesColimitsOfShape (Discrete I) (B ⋙ U) :=
    preservesColimitsOfShape_of_evaluation (B ⋙ U) (Discrete I) (fun Y => by
      let : PreservesColimitsOfShape (Discrete I) (convolutionSectionsFunctor F P Y.unop) :=
        convolutionSections_preservesCoproducts F P Y.unop I
      exact inferInstanceAs (PreservesColimitsOfShape (Discrete I)
        (convolutionSectionsFunctor F P Y.unop ⋙ V)))
  exact preservesColimitsOfShape_of_reflects_of_preserves B U

end AlgebraicGeometry.PresheafWithTransfers
