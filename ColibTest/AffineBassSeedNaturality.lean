/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeed

/-! The concrete geometric natural transformation, not a supplied seed or square. -/
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum AlgebraicGeometry.Scheme.Modules
open CommRingCat.PolynomialLaurent
universe u
variable (R : CommRingCat.{u})

example : KTheory.Bass.strictRingDiagramFunctor.obj
    boundedAboveFlatAffineSectionPrespectrumFunctor =
      laurentSquareFunctor ⋙ boundedAboveFlatAffineSectionPrespectrumFunctor.mapArrow.mapArrow ⋙
        strictSquareLoopedConeFunctor := boundedAboveFlatAffineSectionBassFunctor_eq
example : boundedAboveFlatAffineSectionBassSeed.app R =
    boundedAboveFlatAffineSectionBassSeedMap R := boundedAboveFlatAffineSectionBassSeed_app R
example : boundedAboveFlatAffineSectionBassSeedMap R ≫
    parameterLoopingMap (boundedAboveFlatAffineSectionBassConeMap (𝟙 R)) =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map (𝟙 R) ≫
        boundedAboveFlatAffineSectionBassSeedMap R :=
  boundedAboveFlatAffineSectionBassSeedMap_naturality (𝟙 R)

variable {R} {S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
example : boundedAboveFlatAffineSectionBassSeedMap R ≫
    parameterLoopingMap (boundedAboveFlatAffineSectionBassConeMap f) =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedAboveFlatAffineSectionBassSeedMap S :=
  boundedAboveFlatAffineSectionBassSeedMap_naturality f
example : boundedAboveFlatAffineSectionBassSeedMap R ≫
    parameterLoopingMap (boundedAboveFlatAffineSectionBassConeMap (f ≫ g)) =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map (f ≫ g) ≫
        boundedAboveFlatAffineSectionBassSeedMap T :=
  boundedAboveFlatAffineSectionBassSeedMap_naturality (f ≫ g)
example (n : ℕ) (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n)
    (t : unitInterval) :
    (boundedAboveFlatAffineSectionBassConeMap f).map n
      (Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedMap R).map n x) t) =
    Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedMap S).map n
      ((boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map n x)) t :=
  congrArg (fun h ↦ Path.toContinuousMap (h.map n x) t)
    (boundedAboveFlatAffineSectionBassSeedMap_naturality f)
example (n : ℕ) :
    ((KTheory.Bass.strictRingDiagramIterate n).obj
      boundedAboveFlatAffineSectionPrespectrumFunctor).map f ≫
        (KTheory.Bass.strictRingDiagramTransition boundedAboveFlatAffineSectionBassSeed n).app S =
      (KTheory.Bass.strictRingDiagramTransition boundedAboveFlatAffineSectionBassSeed n).app R ≫
        ((KTheory.Bass.strictRingDiagramIterate (n + 1)).obj
          boundedAboveFlatAffineSectionPrespectrumFunctor).map f :=
  KTheory.Bass.strictRingDiagramTransition_naturality boundedAboveFlatAffineSectionBassSeed n f

example : (KTheory.Bass.strictRingDiagramIterate 0).obj
    boundedAboveFlatAffineSectionPrespectrumFunctor =
      boundedAboveFlatAffineSectionPrespectrumFunctor := rfl
example : KTheory.Bass.strictRingDiagramTransition boundedAboveFlatAffineSectionBassSeed 0 =
    boundedAboveFlatAffineSectionBassSeed := rfl
