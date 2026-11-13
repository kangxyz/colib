/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel.SingleCoproduct
public import Colib.AlgebraicGeometry.SheavesWithTransfers.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryBounded
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# Nisnevich sheafification of single coproducts

Termwise Nisnevich sheafification preserves the original cofan of single
complexes. Localization preserves this coproduct in the derived category,
and the bounded-above inclusion reflects the colimit of the sheafified cofan.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]

/-- The actual exact bounded-above Nisnevich sheafification. -/
abbrev derivedNisnevichSheafification :
    DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k) ⥤
      DerivedCategory.Minus (SheafWithTransfers.{u + 1} k) :=
  (nisnevichSheafify k).mapDerivedCategoryMinus

/-- Bounded derived Nisnevich sheafification preserves the original
single coproduct and its coprojections. -/
theorem derivedNisnevichSheafification_preservesColimit_single {I : Type (u + 1)}
    (P : I → PresheafWithTransfers.{u + 1} k) [HasCoproduct P] (n : ℤ) :
    PreservesColimit (Discrete.functor fun i => (singleDerivedMinus k n).obj (P i))
      (derivedNisnevichSheafification k) := by
  let A := PresheafWithTransfers.{u + 1} k
  let B := SheafWithTransfers.{u + 1} k
  let V : DerivedCategory.Minus B ⥤ DerivedCategory B := DerivedCategory.Minus.ι
  let e := ObjectProperty.fullyFaithfulι (DerivedCategory.TStructure.t (C := B)).minus
  let : V.Full := e.full
  let : V.Faithful := e.faithful
  let hV : ReflectsColimitsOfShape (Discrete I) V :=
    (fullyFaithful_reflectsColimits V).reflectsColimitsOfShape
  let a := nisnevichSheafify k
  let c := ComplexShape.up ℤ
  let S : A ⥤ CochainComplex A ℤ := CochainComplex.singleFunctor A n
  let Q₁ : CochainComplex A ℤ ⥤ DerivedCategory A := DerivedCategory.Q
  let Q₂ : CochainComplex B ℤ ⥤ DerivedCategory B := DerivedCategory.Q
  let aC : CochainComplex A ℤ ⥤ CochainComplex B ℤ := a.mapHomologicalComplex c
  let aD := a.mapDerivedCategory
  let : PreservesColimitsOfSize.{0, u + 1} a :=
    (nisnevichSheafificationAdjunction k).leftAdjoint_preservesColimits
  let : PreservesColimitsOfShape (Discrete I) aC :=
    HomologicalComplex.preservesColimitsOfShape_of_eval aC (fun j => by
      change PreservesColimitsOfShape (Discrete I) (HomologicalComplex.eval A c j ⋙ a)
      infer_instance)
  let : PreservesColimitsOfShape (Discrete I) Q₂ :=
    Stacks.SmallDerivedCategory.derivedCategoryQ_preservesCoproducts B I
  let : PreservesColimitsOfShape (Discrete I) (Q₁ ⋙ aD) :=
    preservesColimitsOfShape_of_natIso a.mapDerivedCategoryFactors.symm
  let K := fun i => (singleDerivedMinus k n).obj (P i)
  let F := derivedNisnevichSheafification k
  let d : (Discrete.functor K ⋙ F) ⋙ V ≅
      Discrete.functor (fun i => (S ⋙ Q₁ ⋙ aD).obj (P i)) :=
    Discrete.natIso (fun _ => Iso.refl _)
  let t := isColimitOfHasCoproductOfPreservesColimit (S ⋙ Q₁ ⋙ aD) P
  apply preservesColimit_of_preserves_colimit_cocone (singleDerivedMinusCofanIsColimit k P n)
  apply isColimitOfReflects V
  refine ((IsColimit.precomposeHomEquiv d _).symm t).ofIsoColimit ?_
  refine Cocone.ext (Iso.refl _) (fun i => ?_)
  let f := aD.map (Q₁.map (S.map (Sigma.ι P i.as)))
  change (𝟙 _ ≫ f) ≫ 𝟙 _ = f
  rw [Category.id_comp, Category.comp_id]

end AlgebraicGeometry.MotivicHomotopy
