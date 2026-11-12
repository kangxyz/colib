/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.NormalizedStageMapStable

public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassOriginalNegativeComparison
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalParameterCoefficientTelescope
public import
  Colib.AlgebraicGeometry.KTheory.Bass.SchemeConjugationLowStages

/-!
Source directory: `Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/`.
Module: `ParameterFiniteNegativeComparison.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Original negative classes in the actual normalized finite stages

The original finite-bottom comparison is followed by the inverses of the
actual coefficient restriction and Spec-row comparison, and then by the
original finite stage map. This fixes the class comparison before studying
the finite conjugating word. The first word acts trivially on these actual
classes. No such assertion is made for the second word.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum KTheory.Bass
open KTheory.Bass.NormalizedStageMap KTheory.Bass.SchemeNaturalSeed

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient

open GlobalSectionChangeIndex GlobalSupportedSection

variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))) [CompactSpace P.left]

/-- The original finite-bottom classes enter the normalized stage through the actual maps. -/
def normalizedNegativeKComparison (i : ℕ) (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((boundedAboveFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i).obj a) ≅
      stableHomotopyGroup ((normalized squareFunctor i (parameterDiagram P)).obj
        (specUnder.obj a)) (-(i : ℤ)) := by
  let H := stableHomotopyFunctor (-(i : ℤ))
  let e := (stageMap squareFunctor i (parameterDiagram P)).app (specUnder.obj a)
  let v := (finiteRestriction P i).app a
  let : IsIso (H.map v) := finiteRestriction_isStableEquivalence P i a (-(i : ℤ))
  let : IsIso (H.map e) := model_stageMap_stable squareFunctor i
    (ParameterModels.ambient P.left) (specUnder.obj a) (-(i : ℤ))
  exact (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).app a ≪≫
    (asIso (H.map v)).symm ≪≫ (H.mapIso ((finiteIso P i).app a)).symm ≪≫
      asIso (H.map e)

/-- The specified class comparison retains each original finite-stage map and its direction. -/
theorem normalizedNegativeKComparison_hom (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (normalizedNegativeKComparison P i a).hom =
      (boundedAboveFlatCoefficientAmbientNegativeKComparison P i).hom.app a ≫
        inv (I := finiteRestriction_isStableEquivalence P i a (-(i : ℤ)))
          ((stableHomotopyFunctor (-(i : ℤ))).map ((finiteRestriction P i).app a)) ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((finiteIso P i).inv.app a) ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((stageMap squareFunctor i (parameterDiagram P)).app (specUnder.obj a)) := by
  rfl

/-- The first conjugating word fixes the specified original finite-bottom class map. -/
@[reassoc]
theorem normalizedNegativeKComparison_one_conjugating
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (normalizedNegativeKComparison P 1 a).hom ≫
      (stableHomotopyFunctor (-((1 : ℕ) : ℤ))).map
        ((conjugatingIso 1 (parameterDiagram P)).hom.app (specUnder.obj a)) =
      (normalizedNegativeKComparison P 1 a).hom := by
  rw [show (conjugatingIso 1 (parameterDiagram P)).hom.app (specUnder.obj a) = 𝟙 _ from
    congrArg (fun η => η.app (specUnder.obj a)) (conjugatingIso_one_hom (parameterDiagram P))]
  rw [CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end AlgebraicGeometry.Scheme.Modules.GlobalParameterCoefficient
