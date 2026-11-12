/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalLocalizationTelescopeMaps
/-! # Actual original global localization telescope arrows and comparison squares -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Topology
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.LocalizationTelescope

@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeSquares.lean:21"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
private theorem mapSquare {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' D' : C} (a : A ⟶ B) (b : B ⟶ D') (c : A ⟶ C') (d : C' ⟶ D')
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg F.map h).trans (F.map_comp c d))

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The actual supported comparison square commutes at every finite Bass stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeSquares.lean:30"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
theorem finiteForget_square (i : ℕ) :
    SupportedTelescope.finiteRestriction f i ≫ boundedAboveFlatCoefficientSupportedBassForget f i =
      finiteForget f i ≫ finiteRestriction Q i := by
  have h := congrArg (fun η => Functor.whiskerRight η prespectrumFunctor)
    (supportedRowRestriction_forget f)
  simp only [Functor.whiskerRight_comp] at h
  exact mapSquare (strictDiagramIterate (laurentUnderSquareFunctor R) i) _ _ _ _ h

/-- The actual coarse comparison square commutes at every finite Bass stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeSquares.lean:39"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
theorem finiteOpen_square (i : ℕ) :
    finiteOpen f i ≫ OpenTelescope.finiteRestriction f i =
      finiteRestriction Q i ≫ boundedAboveFlatCoefficientAmbientBassOpen f i := by
  have h := congrArg (fun η => Functor.whiskerRight η prespectrumFunctor)
    (openRowRestriction_changeWeak f)
  simp only [Functor.whiskerRight_comp] at h
  exact mapSquare (strictDiagramIterate (laurentUnderSquareFunctor R) i) _ _ _ _ h

/-- The supported comparison retains the complete actual telescope quotient maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeSquares.lean:48"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
theorem forget_square :
    SupportedTelescope.telescopeRestriction f ≫
      boundedAboveFlatCoefficientSupportedBassTelescopeForget f =
      forget f ≫ telescopeRestriction Q := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro n i t x
  change Telescope.cylinder
    (fun j => (boundedAboveFlatCoefficientAmbientBassDiagram Q j).obj a)
    (fun j => (boundedAboveFlatCoefficientAmbientBassTransition Q j).app a) n i
      (t, ((boundedAboveFlatCoefficientSupportedBassForget f i).app a).map n
        (((SupportedTelescope.finiteRestriction f i).app a).map n x)) =
    Telescope.cylinder
    (fun j => (boundedAboveFlatCoefficientAmbientBassDiagram Q j).obj a)
    (fun j => (boundedAboveFlatCoefficientAmbientBassTransition Q j).app a) n i
      (t, ((finiteRestriction Q i).app a).map n (((finiteForget f i).app a).map n x))
  exact congrArg (fun y => Telescope.cylinder
    (fun j => (boundedAboveFlatCoefficientAmbientBassDiagram Q j).obj a)
    (fun j => (boundedAboveFlatCoefficientAmbientBassTransition Q j).app a) n i (t, y))
      (congrArg (fun η => (η.app a).map n x) (finiteForget_square f i))

/-- The coarse comparison retains the complete actual telescope quotient maps. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalLocalizationTelescopeSquares.lean:71"
  "adaptation" "Original global localization arrows and whole-height strict comparison squares"]
theorem open_square :
    openMap f ≫ OpenTelescope.telescopeRestriction f =
      telescopeRestriction Q ≫ boundedAboveFlatCoefficientAmbientBassTelescopeOpen f := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro n i t x
  change Telescope.cylinder
    (fun j => (boundedAboveFlatCoefficientOpenBassDiagram f j).obj a)
    (fun j => (boundedAboveFlatCoefficientOpenBassTransition f j).app a) n i
      (t, ((OpenTelescope.finiteRestriction f i).app a).map n
        (((finiteOpen f i).app a).map n x)) =
    Telescope.cylinder
    (fun j => (boundedAboveFlatCoefficientOpenBassDiagram f j).obj a)
    (fun j => (boundedAboveFlatCoefficientOpenBassTransition f j).app a) n i
      (t, ((boundedAboveFlatCoefficientAmbientBassOpen f i).app a).map n
        (((finiteRestriction Q i).app a).map n x))
  exact congrArg (fun y => Telescope.cylinder
    (fun j => (boundedAboveFlatCoefficientOpenBassDiagram f j).obj a)
    (fun j => (boundedAboveFlatCoefficientOpenBassTransition f j).app a) n i (t, y))
      (congrArg (fun η => (η.app a).map n x) (finiteOpen_square f i))

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.LocalizationTelescope

