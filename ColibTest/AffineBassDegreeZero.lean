/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionBassSeed

/-! Actual Laurent tracks, independent interval coordinates, and all-level coefficient maps. -/
open CategoryTheory AlgebraicGeometry Topology
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS
noncomputable section
universe u
private abbrev sectionLoop (R : CommRingCat.{u})
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    Path (stagePoint 0 (boundedAboveFlatAffineSectionModel R))
      (stagePoint 0 (boundedAboveFlatAffineSectionModel R)) := x

variable (R : CommRingCat.{u}) (n : ℕ) (t s : unitInterval)

example (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level n (0, x) =
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map
        (laurentCoefficientInclusion R)).map n x :=
  (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).at_zero n x

example (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level n (1, x) =
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map
        (laurentCoefficientInclusion R)).map n x :=
  (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).at_one n x

example : (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level n
    (t, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).point n) =
      (boundedAboveFlatAffineSectionPrespectrumFunctor.obj
        (.of (LaurentPolynomial R))).point n :=
  (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).at_point n t

example (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level (n + 1)
      (t, (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).structureMap n x s) =
    (boundedAboveFlatAffineSectionPrespectrumFunctor.obj (.of (LaurentPolynomial R))).structureMap
      n ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level n (t, x)) s :=
  (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).comm n t x s

example (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space (n + 1)) :
    (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level (n + 1) (t, x) =
      stageTransformationTopHomotopy n
        (F := boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R))
        (G := boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R))
        (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
        (fun A ↦
          (boundedAboveFlatAffineSectionModel (.of (LaurentPolynomial R))).obj.waldhausen.weq_iso
          _ (show IsIso ((boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).app A).hom
            from inferInstance)) (t, x) := rfl

example (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0)
    (r : unitInterval) :
    sectionLoop (.of (LaurentPolynomial R))
      ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level 0 (t, x)) r =
      stageTransformationTopHomotopy 0
        (F := boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R))
        (G := boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R))
        (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
        (fun A ↦
          (boundedAboveFlatAffineSectionModel (.of (LaurentPolynomial R))).obj.waldhausen.weq_iso
          _ (show IsIso ((boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).app A).hom
            from inferInstance)) (t, sectionLoop R x r) := rfl


-- The Laurent loop is identified before inclusion into the degree-zero cone.
example (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space 0) :
    ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).postcomp
      (LoopPrespectrum.mappingConeInclusion (LoopPrespectrum.StrictSquare.comparison
        (boundedAboveFlatAffineSectionBassSquare R)))).level 0 (t, x) =
    (LoopPrespectrum.mappingConeInclusion (LoopPrespectrum.StrictSquare.comparison
      (boundedAboveFlatAffineSectionBassSquare R))).map 0
      (transformationLoopHomotopy
        (F := boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R))
        (G := boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R))
        (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
        (fun A ↦
          (boundedAboveFlatAffineSectionModel (.of (LaurentPolynomial R))).obj.waldhausen.weq_iso
          _ (show IsIso ((boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).app A).hom
            from inferInstance)) (t, x)) := rfl

-- The middle homotopy uses the forward unit, not its inverse or the inverse chart.
example : boundedAboveFlatAffineSectionLaurentPullbackUnitIso R =
    Functor.IdentityAutomorphism.onFunctor
      (boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R))
      (boundedAboveFlatAffineSectionLaurentUnitIso R) := rfl
