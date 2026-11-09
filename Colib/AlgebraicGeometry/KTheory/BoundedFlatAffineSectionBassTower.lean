/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeed

/-!
# Actual iterated Bass diagrams of the geometric section prespectrum

The genuine strict section prespectrum now instantiates the polynomial/Laurent Bass endofunctor.
Every iterate is an actual strict ring diagram with all coefficient maps. Connecting arrows are
the iterated images of the single proved geometric seed.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Topology
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Apply the actual Bass endofunctor repeatedly to the genuine geometric section diagram. -/
def boundedAboveFlatAffineSectionBassDiagram (n : ℕ) : CommRingCat.{u} ⥤ LoopPrespectrum.{u+1} :=
  (KTheory.Bass.strictRingDiagramIterate n).obj boundedAboveFlatAffineSectionPrespectrumFunctor

/-- The initial stage is the original strict section prespectrum diagram. -/
theorem boundedAboveFlatAffineSectionBassDiagram_zero :
    boundedAboveFlatAffineSectionBassDiagram.{u} 0 =
      boundedAboveFlatAffineSectionPrespectrumFunctor := rfl

/-- Successor iteration applies the same Bass functor to the same original diagram. -/
theorem boundedAboveFlatAffineSectionBassDiagram_succ (n : ℕ) :
    boundedAboveFlatAffineSectionBassDiagram.{u} (n+1) =
      (KTheory.Bass.strictRingDiagramIterate n).obj
        (KTheory.Bass.strictRingDiagramFunctor.obj
          boundedAboveFlatAffineSectionPrespectrumFunctor) := rfl

/-- Every connecting arrow is the actual nth Bass image of the same original geometric seed. -/
def boundedAboveFlatAffineSectionBassTransition (n : ℕ) :
    boundedAboveFlatAffineSectionBassDiagram.{u} n ⟶
      boundedAboveFlatAffineSectionBassDiagram (n + 1) :=
  KTheory.Bass.strictRingDiagramTransition boundedAboveFlatAffineSectionBassSeed n

/-- The initial connecting arrow is the unchanged proved original seed. -/
theorem boundedAboveFlatAffineSectionBassTransition_zero :
    boundedAboveFlatAffineSectionBassTransition.{u} 0 = boundedAboveFlatAffineSectionBassSeed := rfl

/-- Each transition is the literal iterated image of the one proved affine Laurent seed. -/
theorem boundedAboveFlatAffineSectionBassTransition_eq (n : ℕ) :
    boundedAboveFlatAffineSectionBassTransition.{u} n =
      (KTheory.Bass.strictRingDiagramIterate n).map boundedAboveFlatAffineSectionBassSeed := rfl

/-- Every original coefficient map commutes literally with every actual iterated transition. -/
theorem boundedAboveFlatAffineSectionBassTransition_naturality (n : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffineSectionBassDiagram n).map f ≫
        (boundedAboveFlatAffineSectionBassTransition n).app S =
      (boundedAboveFlatAffineSectionBassTransition n).app R ≫
        (boundedAboveFlatAffineSectionBassDiagram (n + 1)).map f :=
  (boundedAboveFlatAffineSectionBassTransition n).naturality f

/-- At every level the iterated transition retains the same strict coefficient square. -/
theorem boundedAboveFlatAffineSectionBassTransition_naturality_apply (n k : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : ((boundedAboveFlatAffineSectionBassDiagram n).obj R).space k) :
    ((boundedAboveFlatAffineSectionBassTransition n).app S).map k
        (((boundedAboveFlatAffineSectionBassDiagram n).map f).map k x) =
      ((boundedAboveFlatAffineSectionBassDiagram (n + 1)).map f).map k
        (((boundedAboveFlatAffineSectionBassTransition n).app R).map k x) :=
  congrArg (fun a ↦ a.map k x) (boundedAboveFlatAffineSectionBassTransition_naturality n f)

end AlgebraicGeometry.Scheme.Modules

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassDiagram.lean:25-38"
  "adaptation" "Actual finite Bass iteration of the section prespectrum"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassDiagram
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassDiagram_zero
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassDiagram_succ

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassTransition.lean:24-49"
  "adaptation" "Iterated original Laurent seed with strict coefficient naturality"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassTransition
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassTransition_zero
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassTransition_naturality
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassTransition_naturality_apply

attribute [colib_ref "quillen" "Quillen/KTheory/Bass/StrictDiagram.lean:60-70"
  "adaptation" "The actual affine transition is the iterated image of its proved Laurent seed"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassTransition_eq

attribute [colib_tag "COL-0362"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassDiagram
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassTransition
