/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenBassSeedChangeWeak
import Colib.KTheory.Bass.StrictDiagramMap

/-! Consumers of the actual coarse section seed and the original whole changeWeak square. -/
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

-- The actual identity section transformation preserves the two constructed seeds.
example :
    boundedAboveFlatAffineSectionBassUnderSeed R ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedAboveFlatAffineSectionOpenPrespectrumTransformation j) =
      boundedAboveFlatAffineSectionOpenPrespectrumTransformation j ≫
        boundedAboveFlatAffineSectionOpenBassSeed j :=
  boundedAboveFlatAffineSectionOpenBassSeed_changeWeak j

-- The coarse category is literally the original section category, not raw complexes.
example : (boundedAboveFlatAffineSectionOpenModel j).obj.Obj =
    BoundedAboveFlatAffineSections R := rfl

-- Open weakness is the original geometric weak predicate on actual original evaluation.
example {A B : BoundedAboveFlatAffineSections R} (f : A ⟶ B) :
    (boundedAboveFlatAffineSectionOpenWaldhausen j).weq f ↔
      (boundedAboveFlatPerfectOpenWaldhausen j).weq
        ((boundedAboveFlatAffineOriginalEvaluation R).map f) := Iff.rfl

-- Neither cofibrations nor the actual section zero is changed.
example : (boundedAboveFlatAffineSectionOpenWaldhausen j).cof =
    (boundedAboveFlatAffineSectionWaldhausen R).cof := rfl
example : (boundedAboveFlatAffineSectionOpenWaldhausen j).zero =
    boundedAboveFlatAffineSectionZero R := rfl

-- Both null legs have their original directions: reversed null, forward unit, forward null.
example (a : Under R) (n : ℕ)
    (x : ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n)
    (s : unitInterval) :
    Path.toContinuousMap ((boundedAboveFlatAffineSectionOpenBassSeedMap j a).map n x) s =
      ((boundedAboveFlatAffineSectionOpenBassNullHomotopy j a).symm.trans
        (((boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).postcomp
          (mappingConeInclusion
            (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j a)))).trans
          (boundedAboveFlatAffineSectionOpenBassNullHomotopy j a))).level n (s, x) :=
  nullLoop_word
    ((boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).postcomp
      (mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j a))))
    (boundedAboveFlatAffineSectionOpenBassNullHomotopy j a) n x s

-- Degree zero belongs to the actual source-null changeWeak identity.
example (a : Under R) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj a.right).space 0) :
    (boundedAboveFlatAffineSectionOpenBassConeChangeWeak j a).map 0
        ((boundedAboveFlatAffineSectionBassNullHomotopy a.right).level 0 (s, x)) =
      (boundedAboveFlatAffineSectionOpenBassNullHomotopy j a).level 0
        (s, (boundedAboveFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map 0 x) :=
  boundedAboveFlatAffineSectionOpenBassNullHomotopy_changeWeak_apply j a 0 s x

-- Homotopy time and structure-map time are independently quantified.
example (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    (boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).level (n + 1)
        (s, ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a).structureMap
          n x t) =
      ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj
        ((laurentUnderFunctor R).obj a)).structureMap n
        ((boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (s, x)) t :=
  (boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).comm n s x t

-- At every level, the identity section map preserves the original Laurent loop.
example (a : Under R) (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj a.right).space n) :
    (boundedAboveFlatAffineSectionOpenPrespectrumMap
        (inclusion j ((laurentUnderFunctor R).obj a))).map n
        ((boundedAboveFlatAffineSectionLaurentUnitHomotopy a.right).level n (s, x)) =
      (boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n
        (s, (boundedAboveFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map n x) :=
  boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy_changeWeak_apply j a n s x

-- The two directions are exactly the existing original section Laurent automorphism.
example (a : Under R) :
    (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a).hom =
      (boundedAboveFlatAffineSectionLaurentPullbackUnitIso a.right).hom :=
  congrArg Iso.hom (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso_eq j a)
example (a : Under R) :
    (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso j a).inv =
      (boundedAboveFlatAffineSectionLaurentPullbackUnitIso a.right).inv :=
  congrArg Iso.inv (boundedAboveFlatAffineSectionOpenDiagramLaurentPullbackUnitIso_eq j a)

-- No restriction to positive levels or identity coefficient maps is made.
example {a b : Under R} (f : a ⟶ b) :
    boundedAboveFlatAffineSectionOpenBassSeedMap j a ≫
        parameterLoopingMap (boundedAboveFlatAffineSectionOpenBassConeMap j f) =
      (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map f ≫
        boundedAboveFlatAffineSectionOpenBassSeedMap j b :=
  boundedAboveFlatAffineSectionOpenBassSeedMap_naturality j f

-- The seed's loop coordinate is independent of the prespectrum structure coordinate.
example (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
      ((boundedAboveFlatAffineSectionOpenBassSeedMap j a).map (n + 1)
        (((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a).structureMap
          n x t)) s =
      Path.toContinuousMap
        ((parameterLooping (boundedAboveFlatAffineSectionOpenBassCone j a)).structureMap n
          ((boundedAboveFlatAffineSectionOpenBassSeedMap j a).map n x) t) s :=
  congrArg (fun p ↦ Path.toContinuousMap (p t) s)
    ((boundedAboveFlatAffineSectionOpenBassSeedMap j a).comm n x)

-- The proved actual square is consumed by every finite Bass transition.
example (n : ℕ) :
    KTheory.Bass.strictDiagramTransition (laurentUnderSquareFunctor R)
        (boundedAboveFlatAffineSectionBassUnderSeed R) n ≫
      (KTheory.Bass.strictDiagramIterate (laurentUnderSquareFunctor R) (n + 1)).map
        (boundedAboveFlatAffineSectionOpenPrespectrumTransformation j) =
      (KTheory.Bass.strictDiagramIterate (laurentUnderSquareFunctor R) n).map
          (boundedAboveFlatAffineSectionOpenPrespectrumTransformation j) ≫
        KTheory.Bass.strictDiagramTransition (laurentUnderSquareFunctor R)
          (boundedAboveFlatAffineSectionOpenBassSeed j) n :=
  KTheory.Bass.strictDiagramTransition_map _ _ _ _
    (boundedAboveFlatAffineSectionOpenBassSeed_changeWeak j) n
