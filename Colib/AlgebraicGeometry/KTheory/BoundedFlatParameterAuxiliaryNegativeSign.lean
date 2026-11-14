/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryNegativeClasses
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterNegativeSign
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatParameterAuxiliaryFineConnectingComparison

/-!
# Original auxiliary-supported negative classes through the actual comparisons

The original supported negative groups are taken on the actual support arrows
for the union, auxiliary open, and inverse-image open. Their unchanged finite
negative comparisons are followed by the actual three auxiliary finite maps and
the original fine telescope inclusions. The all-index supported sign proves
that the independent current classes have exactly these images. Compactness of
the inverse-image open uses the original compact source and quasi-separated
target hypotheses.

Source: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/
ParameterAuxiliaryNegativeSign.lean`, revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.SchemeNaturalSeed
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex GlobalSupportedSection.ParameterAuxiliarySupport
open GlobalSupportedSection

/-- The actual support object has the original compact open as its underlying space. -/
theorem supportObject_compactSpace
    (Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
    (T : Q.left.Opens) [CompactSpace T] : CompactSpace (supportObject Q T).left := by
  change CompactSpace T
  infer_instance

attribute [local instance] supportObject_compactSpace

private theorem cancel_comparison {C : Type*} [Category C]
    {A B D E F : C} (x : A ⟶ B) (y : B ⟶ D) (z : A ⟶ E)
    (j : E ⟶ D) (v : D ⟶ F) (k : A ⟶ F) [Mono v]
    (h : x ≫ y ≫ v = k) (hj : z ≫ j ≫ v = k) : x ≫ y = z ≫ j := by
  apply (cancel_mono v).1
  simpa only [Category.assoc] using h.trans hj.symm

private theorem currentNegativeKComparison_iterated
    {A B : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (g : A ⟶ B)
    [IsOpenImmersion g.left] [CompactSpace A.left] [CompactSpace B.left]
    [QuasiSeparatedSpace B.left] (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison g i).hom.app a ≫
        (currentIteratedStableIso (ParameterModels.supported g.left)
          (ParameterLaurentTrack.supportedTrack g.left) (specUnder.obj a) (-(i : ℤ))).hom =
      (GlobalSupportedParameterCoefficient.finiteNegativeKComparison g i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((GlobalSupportedParameterCoefficient.iteratedStageInclusion g i).app
            (specUnder.obj a)) := by
  let : IsIso ((stableHomotopyFunctor (-(i : ℤ))).map
      ((GlobalSupportedParameterCoefficient.fineTelescopeComparison g).app a)) :=
    GlobalSupportedParameterCoefficient.fineTelescopeComparison_stable g a (-(i : ℤ))
  exact cancel_comparison _ _ _ _ _ _
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison_fine g i a)
    (GlobalSupportedParameterCoefficient.finiteNegativeKComparison_iterated_fine g i a)

private theorem currentFineSupportComparison_hom
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (ParameterAuxiliaryCurrentFiber.currentFineSupportComparison f T a d).hom =
      (currentIteratedStableIso
        (ParameterModels.supported (supportArrow Q (unionOpen f.left T)).left)
        (ParameterLaurentTrack.supportedTrack (supportArrow Q (unionOpen f.left T)).left)
        (specUnder.obj a) d).hom ≫
      (stableHomotopyFunctor d).map ((fiberTelescopeComparison f T).app a) := by
  simp only [ParameterAuxiliaryCurrentFiber.currentFineSupportComparison,
    currentIteratedStableIso, Iso.trans_hom, asIso_hom, Category.assoc,
    fiberAction, supportArrow, Over.homMk_left]

private theorem currentFineOpenComparison_hom
    {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    (T : Q.left.Opens)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (d : ℤ) :
    (ParameterAuxiliaryCurrentFiber.currentFineOpenComparison f T a d).hom =
      (currentIteratedStableIso
        (ParameterModels.supported (supportArrow P (inverseOpen f.left T)).left)
        (ParameterLaurentTrack.supportedTrack (supportArrow P (inverseOpen f.left T)).left)
        (specUnder.obj a) d).hom ≫
      (stableHomotopyFunctor d).map ((openTelescopeComparison f T).app a) := by
  simp only [ParameterAuxiliaryCurrentFiber.currentFineOpenComparison,
    currentIteratedStableIso, Iso.trans_hom, asIso_hom, Category.assoc,
    openAction, supportArrow, Over.homMk_left]

private theorem class_triangle {C : Type*} [Category C]
    {A B D E F : C} (x : A ⟶ B) (y : B ⟶ D) (z : A ⟶ E)
    (j : E ⟶ D) (v : D ⟶ F) (w : E ⟶ F)
    (h : x ≫ y = z ≫ j) (hv : j ≫ v = w) : x ≫ y ≫ v = z ≫ w := by
  rw [← Category.assoc, h, Category.assoc, hv]

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

private theorem currentNegativeKComparison_iterated_fine_fiber (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T;
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison
        (supportArrow Q (unionOpen f.left T)) i).hom.app a ≫
      (currentIteratedStableIso
        (ParameterModels.supported (supportArrow Q (unionOpen f.left T)).left)
        (ParameterLaurentTrack.supportedTrack (supportArrow Q (unionOpen f.left T)).left)
        (specUnder.obj a) (-(i : ℤ))).hom ≫
      (stableHomotopyFunctor (-(i : ℤ))).map ((fiberTelescopeComparison f T).app a) =
        fiberNegativeFineClass f T i a := by
  let : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T
  have h := currentNegativeKComparison_iterated
    (supportArrow Q (unionOpen f.left T)) i a
  have hincl :
      (GlobalSupportedParameterCoefficient.iteratedStageInclusion
          (supportArrow Q (unionOpen f.left T)) i).app (specUnder.obj a) ≫
        (fiberTelescopeComparison f T).app a =
      (fiberFiniteComparison f T i).app a ≫
        (boundedAboveFlatCoefficientSupportedFiberBassTelescopeInclusion f T i).app a := by
    apply LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl
  have hv := congrArg (stableHomotopyFunctor (-(i : ℤ))).map hincl
  simp only [Functor.map_comp] at hv
  exact class_triangle _ _ _ _ _ _ h hv

/-- The exact original fiber negative classes are fixed through the actual four-arrow comparison. -/
theorem currentNegativeKComparison_fine_fiber (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T;
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison
        (supportArrow Q (unionOpen f.left T)) i).hom.app a ≫
      (ParameterAuxiliaryCurrentFiber.currentFineSupportComparison f T a (-(i : ℤ))).hom =
        fiberNegativeFineClass f T i a := by
  let : CompactSpace (unionOpen f.left T) := unionOpen_compactSpace f T
  rewrite [currentFineSupportComparison_hom f T a (-(i : ℤ))]
  have hc := currentNegativeKComparison_iterated_fine_fiber f T i a
  dsimp only [Functor.comp_obj, fiber, fiberAction, supportArrow, Over.homMk_left] at hc ⊢
  exact hc

/-- The exact original ambient negative classes retain the actual auxiliary finite maps. -/
@[reassoc]
theorem currentNegativeKComparison_fine_ambient (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison
        (supportArrow Q T) i).hom.app a ≫
        (currentIteratedStableIso (ambient T) (ambientAction T)
          (specUnder.obj a) (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((ambientTelescopeComparison Q T).app a) =
      ambientNegativeFineClass T i a := by
  have h := currentNegativeKComparison_iterated (supportArrow Q T) i a
  have hincl :
      (GlobalSupportedParameterCoefficient.iteratedStageInclusion
          (supportArrow Q T) i).app (specUnder.obj a) ≫
        (ambientTelescopeComparison Q T).app a =
      (ambientFiniteComparison Q T i).app a ≫
        (boundedAboveFlatCoefficientSupportedAmbientBassTelescopeInclusion T i).app a := by
    apply LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl
  have hv := congrArg (stableHomotopyFunctor (-(i : ℤ))).map hincl
  simp only [Functor.map_comp] at hv
  exact class_triangle _ _ _ _ _ _ h hv

omit [CompactSpace Q.left] in
private theorem currentNegativeKComparison_iterated_fine_open (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T;
    letI : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f;
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison
        (supportArrow P (inverseOpen f.left T)) i).hom.app a ≫
      (currentIteratedStableIso
        (ParameterModels.supported (supportArrow P (inverseOpen f.left T)).left)
        (ParameterLaurentTrack.supportedTrack (supportArrow P (inverseOpen f.left T)).left)
        (specUnder.obj a) (-(i : ℤ))).hom ≫
      (stableHomotopyFunctor (-(i : ℤ))).map ((openTelescopeComparison f T).app a) =
        openNegativeFineClass f T i a := by
  let : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T
  let : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f
  have h := currentNegativeKComparison_iterated
    (supportArrow P (inverseOpen f.left T)) i a
  have hincl :
      (GlobalSupportedParameterCoefficient.iteratedStageInclusion
          (supportArrow P (inverseOpen f.left T)) i).app (specUnder.obj a) ≫
        (openTelescopeComparison f T).app a =
      (openFiniteComparison f T i).app a ≫
        (boundedAboveFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T i).app a := by
    apply LoopPrespectrum.Hom.ext
    funext n
    apply ContinuousMap.ext
    intro x
    rfl
  have hv := congrArg (stableHomotopyFunctor (-(i : ℤ))).map hincl
  simp only [Functor.map_comp] at hv
  exact class_triangle _ _ _ _ _ _ h hv

omit [CompactSpace Q.left] in
/-- The exact original inverse-open negative classes retain the original fine evaluation. -/
theorem currentNegativeKComparison_fine_open (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    letI : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T;
    letI : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f;
    (GlobalSupportedParameterCoefficient.currentNegativeKComparison
        (supportArrow P (inverseOpen f.left T)) i).hom.app a ≫
      (ParameterAuxiliaryCurrentFiber.currentFineOpenComparison f T a (-(i : ℤ))).hom =
        openNegativeFineClass f T i a := by
  let : CompactSpace (inverseOpen f.left T) := inverseOpen_compactSpace f T
  let : QuasiSeparatedSpace P.left := open_quasiSeparatedSpace f
  rewrite [currentFineOpenComparison_hom f T a (-(i : ℤ))]
  have hc := currentNegativeKComparison_iterated_fine_open f T i a
  dsimp only [Functor.comp_obj, ParameterAuxiliarySupport.openModel, openAction,
    supportArrow, Over.homMk_left] at hc ⊢
  exact hc

/-- The fine fiber class is invertible through its actual current and fine comparisons. -/
theorem fiberNegativeFineClass_isIso (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsIso (fiberNegativeFineClass f T i a) := by
  rw [← currentNegativeKComparison_fine_fiber f T i a]
  infer_instance

/-- The fine auxiliary ambient class is invertible through its actual comparison. -/
theorem ambientNegativeFineClass_isIso (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsIso (ambientNegativeFineClass T i a) := by
  let : IsIso ((stableHomotopyFunctor (-(i : ℤ))).map
      ((ambientTelescopeComparison Q T).app a)) :=
    ambientTelescopeComparison_stable Q T a (-(i : ℤ))
  rw [← currentNegativeKComparison_fine_ambient T i a]
  infer_instance

omit [CompactSpace Q.left] in
/-- The fine inverse-open class is invertible through its actual current and fine comparisons. -/
theorem openNegativeFineClass_isIso (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsIso (openNegativeFineClass f T i a) := by
  rw [← currentNegativeKComparison_fine_open f T i a]
  infer_instance

end AlgebraicGeometry.Scheme.Modules.GlobalAuxiliaryParameterCoefficient
