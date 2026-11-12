/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSupportedRestrictionModel
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalSectionLaurentAction
/-! # The actual supported global coefficient row and its strict restriction square

The original supported predicate, evaluation-transported structure and chosen zero are reused.
The whole coefficient restriction square is retained, before evaluation and after forgetting.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
private theorem exactIntoEquivalence
    {A B C : Type*} [Category A] [Category B] [Category C]
    (WA : Structure A) (WC : Structure C) (e : B ≌ C) (z : B)
    (hz : IsZero (e.functor.obj z)) (F : A ⥤ B)
    (h : IsExact WA.cof WA.weq WC.cof WC.weq (F ⋙ e.functor)) :
    IsExact WA.cof WA.weq (WC.ofEquivalence e z hz).cof
      (WC.ofEquivalence e z hz).weq F where
  zero hx := IsZero.of_full_of_faithful_of_isZero e.functor _ (h.zero hx)
  cofibration f hf := h.cofibration f hf
  weak f hf := h.weak f hf
  pushout hi hp := IsPushout.of_map_of_faithful e.functor (h.pushout hi hp)

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The original support predicate on the actual global coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:37"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
abbrev rowSupported (a : Under R) : ObjectProperty (((globalRow Q).obj a).obj.Obj) :=
  boundedAboveFlatGlobalSectionSupported (X :=
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
    (schemeMap f a)

/-- Global reindexing preserves actual support through its strict evaluation square. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:42"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
theorem rowMap_supported {a b : Under R} (g : a ⟶ b) (S : ((globalRow Q).obj a).obj.Obj)
    (hS : rowSupported f a S) : rowSupported f b (((globalRow Q).map g).hom.toFunctor.obj S) := by
  have hp := boundedAboveFlatCoefficientSectionsMap_supported
    (schemeMap f a) (schemeMap f b) (𝟙 (op Q), g)
    (boundedAboveFlatCoefficientOpenPairMap f g).left
    (MorphismProperty.Arrow.w (boundedAboveFlatCoefficientOpenPairMap f g))
    (((rowRestriction Q).app a).hom.toFunctor.obj S)
    ((restriction_supported R (op Q, a) (schemeMap f a) S).mpr hS)
  have h := congrArg (fun m => m.hom.toFunctor) ((rowRestriction Q).naturality g)
  have ho := congrArg (fun F => F.obj S) h
  apply (restriction_supported R (op Q, b) (schemeMap f b) _).mp
  exact Eq.mpr (congrArg (boundedAboveFlatCoefficientSectionSupported (schemeMap f b)) ho) hp

/-- Supported reindexing keeps the actual original global section functor. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:56"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
def supportedRowMapFunctor {a b : Under R} (g : a ⟶ b) :
    (rowSupported f a).FullSubcategory ⥤ (rowSupported f b).FullSubcategory :=
  (rowSupported f b).lift ((rowSupported f a).ι ⋙ ((globalRow Q).map g).hom.toFunctor)
    (fun S => rowMap_supported f g S.obj S.property)

/-- The full coefficient-restriction square commutes before evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:62"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
theorem supportedRowMap_restriction {a b : Under R} (g : a ⟶ b) :
    supportedRowMapFunctor f g ⋙ supportedRestriction R (op Q, b) (schemeMap f b) =
      supportedRestriction R (op Q, a) (schemeMap f a) ⋙
        (boundedAboveFlatCoefficientSupportedModelMap f g).hom.toFunctor := by
  change (boundedAboveFlatCoefficientSectionSupported (schemeMap f b)).lift
    ((rowSupported f a).ι ⋙ ((globalRow Q).map g).hom.toFunctor ⋙
      ((rowRestriction Q).app b).hom.toFunctor) _ =
    (boundedAboveFlatCoefficientSectionSupported (schemeMap f b)).lift
      ((rowSupported f a).ι ⋙ ((rowRestriction Q).app a).hom.toFunctor ⋙
        ((boundedAboveFlatCoefficientSectionModelRow Q).map g).hom.toFunctor) _
  apply supported_lift_congr
  have h := congrArg (fun m => m.hom.toFunctor) ((rowRestriction Q).naturality g)
  exact congrArg (fun F => (rowSupported f a).ι ⋙ F) h

/-- Supported reindexing is exact for the original evaluation-transported classes. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:77"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
theorem supportedRowMap_exact {a b : Under R} (g : a ⟶ b) :
    IsExact (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)).cof
      (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)).weq
      (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b)).cof
      (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b)).weq (supportedRowMapFunctor f g) := by
  have he := (supportedRestriction_exact R (op Q, a) (schemeMap f a)).comp
    (boundedAboveFlatCoefficientSupportedModelMap f g).hom.isExact
  rw [← supportedRowMap_restriction f g] at he
  have heval : IsExact (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)).cof
      (boundedAboveFlatGlobalSupportedWaldhausen (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)).weq
      (boundedAboveFlatPerfectSupportedWaldhausen (schemeMap f b)).cof
      (boundedAboveFlatPerfectSupportedWaldhausen (schemeMap f b)).weq
      (supportedRowMapFunctor f g ⋙ boundedAboveFlatGlobalSupportedEvaluation (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b)) := by
    have h := he.comp (boundedAboveFlatCoefficientSupportedEvaluation_exact (schemeMap f b))
    rw [Functor.assoc, supportedRestriction_evaluation] at h
    exact h
  exact exactIntoEquivalence _ _
    (boundedAboveFlatGlobalSupportedEvaluation (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b)).asEquivalence _ _ _ heval

/-- The supported Model arrow keeps the original global chosen zero. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:113"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
def supportedRowMap {a b : Under R} (g : a ⟶ b) :
    boundedAboveFlatGlobalSupportedSectionModel (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a) ⟶ boundedAboveFlatGlobalSupportedSectionModel (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, b))
      (schemeMap f b) :=
  ⟨⟨supportedRowMapFunctor f g, supportedRowMap_exact f g⟩, by
    apply ObjectProperty.FullSubcategory.ext
    exact ((globalRow Q).map g).property⟩

/-- Supported global sections form a strict coefficient Model diagram. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:126"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
def supportedRow : Under R ⥤ WideSubcategory preservesZero.{u + 1} where
  obj a := boundedAboveFlatGlobalSupportedSectionModel (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)
  map := supportedRowMap f
  map_id a := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change (rowSupported f a).lift
      ((rowSupported f a).ι ⋙ ((globalRow Q).map (𝟙 a)).hom.toFunctor) _ =
        (rowSupported f a).lift (rowSupported f a).ι _
    apply supported_lift_congr
    have h := congrArg (fun m => m.hom.toFunctor) ((globalRow Q).map_id a)
    exact congrArg (fun F => (rowSupported f a).ι ⋙ F) h
  map_comp g h := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    change (rowSupported f _).lift
      ((rowSupported f _).ι ⋙ ((globalRow Q).map (g ≫ h)).hom.toFunctor) _ =
        (rowSupported f _).lift
          ((rowSupported f _).ι ⋙ ((globalRow Q).map g).hom.toFunctor ⋙
            ((globalRow Q).map h).hom.toFunctor) _
    apply supported_lift_congr
    have hh := congrArg (fun m => m.hom.toFunctor) ((globalRow Q).map_comp g h)
    exact congrArg (fun F => (rowSupported f _).ι ⋙ F) hh

/-- Forget support without changing the original global section. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:151"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
def supportedRowForget : supportedRow f ⟶ globalRow Q where
  app a := boundedAboveFlatGlobalSupportedForget (X :=
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj (op Q, a))
      (schemeMap f a)
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    rfl

/-- Restrict the actual supported global row to the original supported coefficient row. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:160"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
def supportedRowRestriction : supportedRow f ⟶ boundedAboveFlatCoefficientSupportedModelFunctor f
  where
  app a := supportedRestrictionModel R (op Q, a) (schemeMap f a)
  naturality a b g := by
    apply WideSubcategory.hom_ext
    apply SmallWaldhausenCategory.Hom.ext
    exact supportedRowMap_restriction f g

/-- The actual supported forgetful comparison square is strict as a transformation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalSupportedRow.lean:167"
  "adaptation" "Original global supported row, exact reindexing and strict restriction square"]
theorem supportedRowRestriction_forget :
    supportedRowRestriction f ≫ boundedAboveFlatCoefficientSupportedForgetModelTransformation f =
      supportedRowForget f ≫ rowRestriction Q := by
  ext a
  exact congrArg (fun k => k.hom) (supportedRestrictionModel_forget R f a)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
