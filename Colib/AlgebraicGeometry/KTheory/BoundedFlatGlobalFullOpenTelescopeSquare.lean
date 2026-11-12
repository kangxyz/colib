/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalFullOpenTelescope
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientOrdinaryOpenRestrictionStages

/-! # Exact original localization comparison squares at every stage and on telescopes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS KTheory.Bass
open CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.FullOpenTelescope

private theorem mapSquare {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B C' D' : C} (a : A ⟶ B) (b : B ⟶ D') (c : A ⟶ C') (d : C' ⟶ D')
    (h : a ≫ b = c ≫ d) : F.map a ≫ F.map b = F.map c ≫ F.map d :=
  (F.map_comp a b).symm.trans ((congrArg F.map h).trans (F.map_comp c d))

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The actual full-open comparison commutes at every original finite stage. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenTelescopeSquare.lean:30"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem finiteRestriction_square (i : ℕ) :
    finiteRestriction f i ≫ GlobalSectionChangeIndex.finiteRestriction P i =
      OpenTelescope.finiteRestriction f i ≫ boundedAboveFlatCoefficientOpenBassRestriction f i := by
  have h := congrArg (fun η => Functor.whiskerRight η prespectrumFunctor)
    (globalOpenRestriction_square f)
  simp only [Functor.whiskerRight_comp] at h
  exact mapSquare (strictDiagramIterate (laurentUnderSquareFunctor R) i) _ _ _ _ h

/-- The full-open square retains the original coefficient telescope restriction literally. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalFullOpenTelescopeSquare.lean:39"
  "adaptation" "Actual original full-open maps and whole same-null Spec comparison"]
theorem restriction_square :
    restriction f ≫ telescopeRestriction P =
      OpenTelescope.telescopeRestriction f ≫
        boundedAboveFlatCoefficientOpenBassTelescopeRestriction f := by
  apply NatTrans.ext
  funext a
  apply Telescope.hom_ext
  intro n i t x
  change Telescope.cylinder
    (fun j => (boundedAboveFlatCoefficientFullOpenBassDiagram f j).obj a)
    (fun j => (boundedAboveFlatCoefficientFullOpenBassTransition f j).app a) n i
      (t, ((GlobalSectionChangeIndex.finiteRestriction P i).app a).map n
        (((finiteRestriction f i).app a).map n x)) =
    Telescope.cylinder
    (fun j => (boundedAboveFlatCoefficientFullOpenBassDiagram f j).obj a)
    (fun j => (boundedAboveFlatCoefficientFullOpenBassTransition f j).app a) n i
      (t, ((boundedAboveFlatCoefficientOpenBassRestriction f i).app a).map n
        (((OpenTelescope.finiteRestriction f i).app a).map n x))
  exact congrArg (fun y => Telescope.cylinder
    (fun j => (boundedAboveFlatCoefficientFullOpenBassDiagram f j).obj a)
    (fun j => (boundedAboveFlatCoefficientFullOpenBassTransition f j).app a) n i (t, y))
      (congrArg (fun η => (η.app a).map n x) (finiteRestriction_square f i))

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex.FullOpenTelescope

