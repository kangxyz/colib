/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassStableColimit

/-! Canonical signed stable colimits, all stage legs and whole coefficient natural isomorphism. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules
noncomputable section
universe u

variable (R : CommRingCat.{u}) (d : ℤ) (i : ℕ)

example : colimit (boundedAboveFlatAffineSectionBassStableDiagram R d) ≅
    stableHomotopyGroup (boundedAboveFlatAffineSectionBassTelescope R) d :=
  boundedAboveFlatAffineSectionBassStableColimitIso R d

example : colimit (boundedAboveFlatAffineSectionBassStableDiagram R (-1)) ≅
    stableHomotopyGroup (boundedAboveFlatAffineSectionBassTelescope R) (-1) :=
  boundedAboveFlatAffineSectionBassStableColimitIso R (-1)

example : colimit (boundedAboveFlatAffineSectionBassStableDiagram R 0) ≅
    stableHomotopyGroup (boundedAboveFlatAffineSectionBassTelescope R) 0 :=
  boundedAboveFlatAffineSectionBassStableColimitIso R 0

example : colimit (boundedAboveFlatAffineSectionBassStableDiagram R 1) ≅
    stableHomotopyGroup (boundedAboveFlatAffineSectionBassTelescope R) 1 :=
  boundedAboveFlatAffineSectionBassStableColimitIso R 1

example : colimit.ι (boundedAboveFlatAffineSectionBassStableDiagram R d) i ≫
      (boundedAboveFlatAffineSectionBassStableColimitIso R d).hom =
    (stableHomotopyFunctor d).map
      ((boundedAboveFlatAffineSectionBassTelescopeInclusion i).app R) :=
  boundedAboveFlatAffineSectionBassStableColimitIso_ι_hom R d i

example : colimit.ι (boundedAboveFlatAffineSectionBassStableDiagram R d) 0 ≫
      (boundedAboveFlatAffineSectionBassStableColimitIso R d).hom =
    (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeInitial.app R) :=
  boundedAboveFlatAffineSectionBassStableColimitIso_ι_hom R d 0

example : boundedAboveFlatAffineSectionBassStableColimitFunctor.{u} d ≅
    boundedAboveFlatAffineSectionBassTelescopeFunctor ⋙ stableHomotopyFunctor d :=
  boundedAboveFlatAffineSectionBassStableColimitNatIso d

example : (boundedAboveFlatAffineSectionBassStableColimitNatIso d).hom.app R =
    (boundedAboveFlatAffineSectionBassStableColimitIso R d).hom := rfl

example {S : CommRingCat.{u}} (f : R ⟶ S) :
    colimMap (boundedAboveFlatAffineSectionBassStableDiagramMap f d) ≫
      (boundedAboveFlatAffineSectionBassStableColimitIso S d).hom =
    (boundedAboveFlatAffineSectionBassStableColimitIso R d).hom ≫
      (stableHomotopyFunctor d).map (boundedAboveFlatAffineSectionBassTelescopeMap f) :=
  boundedAboveFlatAffineSectionBassStableColimitIso_naturality f d

example : boundedAboveFlatAffineSectionBassStableDiagramMap (𝟙 R) d =
    𝟙 (boundedAboveFlatAffineSectionBassStableDiagram R d) :=
  (boundedAboveFlatAffineSectionBassStableDiagramFunctor d).map_id R

example {S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedAboveFlatAffineSectionBassStableDiagramMap (f ≫ g) d =
      boundedAboveFlatAffineSectionBassStableDiagramMap f d ≫
        boundedAboveFlatAffineSectionBassStableDiagramMap g d :=
  (boundedAboveFlatAffineSectionBassStableDiagramFunctor d).map_comp f g

example : (boundedAboveFlatAffineSectionBassStableColimitFunctor d).map (𝟙 R) =
    𝟙 ((boundedAboveFlatAffineSectionBassStableColimitFunctor d).obj R) :=
  (boundedAboveFlatAffineSectionBassStableColimitFunctor d).map_id R

example {S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedAboveFlatAffineSectionBassStableColimitFunctor d).map (f ≫ g) =
      (boundedAboveFlatAffineSectionBassStableColimitFunctor d).map f ≫
        (boundedAboveFlatAffineSectionBassStableColimitFunctor d).map g :=
  (boundedAboveFlatAffineSectionBassStableColimitFunctor d).map_comp f g
