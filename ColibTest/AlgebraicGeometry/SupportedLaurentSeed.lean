/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetSeed

/-! Consumers of the actual supported seed and the ambient SECTION seed, with literal parameters. -/
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.AffineOpenPair
open CommRingCat.PolynomialLaurent
noncomputable section
universe u

private theorem nullLoop_word {E F : LoopPrespectrum.{u}}
    {f : E ⟶ F} (H : Homotopy f f) (N : Homotopy f (zeroHom E F))
    (n : ℕ) (x : E.space n) (s : unitInterval) :
    Path.toContinuousMap ((H.nullLoopMap N).map n x) s =
      (N.symm.trans (H.trans N)).level n (s, x) := rfl

variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

-- The whole square uses the actual Bass functor on the original support inclusion.
example :
    boundedAboveFlatAffineSupportedSectionBassSeed j ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation j) =
      boundedAboveFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
        boundedAboveFlatAffineSectionBassUnderSeed R :=
  boundedAboveFlatAffineSupportedSectionBassSeed_forget j

-- The ambient target is literally the existing cocartesian section model, not raw complexes.
example (a : Under R) :
    (boundedAboveFlatAffineSectionModel a.right).obj.Obj =
      BoundedAboveFlatAffineSections a.right := rfl

-- Both null legs have their original directions: reversed null, forward unit, forward null.
example (a : Under R) (n : ℕ)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n)
    (s : unitInterval) :
    Path.toContinuousMap ((boundedAboveFlatAffineSupportedSectionBassSeedMap j a).map n x) s =
      ((boundedAboveFlatAffineSupportedSectionBassNullHomotopy j a).symm.trans
        (((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).postcomp
          (mappingConeInclusion
            (StrictSquare.comparison (boundedAboveFlatAffineSupportedSectionBassSquare j a)))).trans
          (boundedAboveFlatAffineSupportedSectionBassNullHomotopy j a))).level n (s, x) :=
  nullLoop_word
    ((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).postcomp
      (mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSupportedSectionBassSquare j a))))
    (boundedAboveFlatAffineSupportedSectionBassNullHomotopy j a) n x s

-- Level zero is included in the original null-cylinder support-forget identity.
example (a : Under R) (s : unitInterval)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space 0) :
    (boundedAboveFlatAffineSupportedSectionBassConeForget j a).map 0
        ((boundedAboveFlatAffineSupportedSectionBassNullHomotopy j a).level 0 (s, x)) =
      (boundedAboveFlatAffineSectionBassNullHomotopy a.right).level 0
        (s, (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map 0 x) :=
  boundedAboveFlatAffineSupportedSectionBassNullHomotopy_forget_apply j a 0 s x

-- Homotopy time and structure-map time are independently quantified.
example (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).level (n + 1)
        (s, ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).structureMap
          n x t) =
      ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj
        ((laurentUnderFunctor R).obj a)).structureMap n
        ((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).level n (s, x)) t :=
  (boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).comm n s x t

-- All levels retain the original forward Laurent action under support inclusion.
example (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap
        (inclusion j ((laurentUnderFunctor R).obj a))).map n
        ((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).level n (s, x)) =
      (boundedAboveFlatAffineSectionLaurentUnitHomotopy a.right).level n
        (s, (boundedAboveFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map n x) :=
  boundedAboveFlatAffineSupportedDiagramLaurentHomotopy_forget_apply j a n s x

-- The supported forward and inverse automorphisms are the original ambient section maps.
example {V : Scheme.{u}} (jL : V ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion jL]
    (s : BoundedAboveFlatAffineSupportedSections jL) :
    ((boundedAboveFlatAffineSupportedSectionLaurentUnitIso jL).hom.app s).hom =
      (boundedAboveFlatAffineSectionLaurentUnitIso R).hom.app s.obj :=
  boundedAboveFlatAffineSupportedSectionLaurentUnitIso_hom_original jL s

example {V : Scheme.{u}} (jL : V ⟶ Spec (.of (LaurentPolynomial R))) [IsOpenImmersion jL]
    (s : BoundedAboveFlatAffineSupportedSections jL) :
    ((boundedAboveFlatAffineSupportedSectionLaurentUnitIso jL).inv.app s).hom =
      (boundedAboveFlatAffineSectionLaurentUnitIso R).inv.app s.obj :=
  boundedAboveFlatAffineSupportedSectionLaurentUnitIso_inv_original jL s

-- No restriction to positive levels or identity coefficient maps is made.
example {a b : Under R} (f : a ⟶ b) :
    boundedAboveFlatAffineSupportedSectionBassSeedMap j a ≫
        parameterLoopingMap (boundedAboveFlatAffineSupportedSectionBassConeMap j f) =
      (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f ≫
        boundedAboveFlatAffineSupportedSectionBassSeedMap j b :=
  boundedAboveFlatAffineSupportedSectionBassSeedMap_naturality j f

-- The seed's loop coordinate is independent of the prespectrum structure coordinate.
example (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
      ((boundedAboveFlatAffineSupportedSectionBassSeedMap j a).map (n + 1)
        (((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).structureMap
          n x t)) s =
      Path.toContinuousMap
        ((parameterLooping (boundedAboveFlatAffineSupportedSectionBassCone j a)).structureMap n
          ((boundedAboveFlatAffineSupportedSectionBassSeedMap j a).map n x) t) s :=
  congrArg (fun p ↦ Path.toContinuousMap (p t) s)
    ((boundedAboveFlatAffineSupportedSectionBassSeedMap j a).comm n x)
