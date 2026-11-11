/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenLaurentChangeWeak
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenBassSeed
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionForgetSeed

/-!
# The original fine and relative-open Bass seeds commute with change of weaknesses

The actual fine-to-coarse natural transformation supplies the four-corner Laurent square and
unchanged cone map. Its original null cylinder and whole scalar track prove compatibility of
the two genuinely constructed seeds. The source is the already constructed ambient seed
restricted along Under.forget. No seed square, localization or full-open equivalence is assumed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original four fine-to-coarse maps give the actual Laurent-square map. -/
def boundedAboveFlatAffineSectionOpenBassSquareChangeWeak (a : Under R) :
    boundedAboveFlatAffineSectionBassSquare a.right ⟶
      boundedAboveFlatAffineSectionOpenBassSquare j a :=
  ((Functor.mapArrowFunctor (Arrow (Under R)) (Arrow LoopPrespectrum.{u+1})).map
    ((Functor.mapArrowFunctor (Under R) LoopPrespectrum.{u+1}).map
      (boundedAboveFlatAffineSectionOpenPrespectrumTransformation j))).app
        (laurentUnderSquare R a)

/-- The original cone functor acts on that same four-corner map. -/
def boundedAboveFlatAffineSectionOpenBassConeChangeWeak (a : Under R) :
    boundedAboveFlatAffineSectionBassCone a.right ⟶ boundedAboveFlatAffineSectionOpenBassCone j a :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedAboveFlatAffineSectionOpenBassSquareChangeWeak j a))

/-- The whole original source-leg null cylinder survives at the identical time. -/
theorem boundedAboveFlatAffineSectionOpenBassNullHomotopy_changeWeak_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj a.right).space n) :
    (boundedAboveFlatAffineSectionOpenBassConeChangeWeak j a).map n
        ((boundedAboveFlatAffineSectionBassNullHomotopy a.right).level n (t, x)) =
      (boundedAboveFlatAffineSectionOpenBassNullHomotopy j a).level n
        (t, (boundedAboveFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedAboveFlatAffineSectionOpenBassSquareChangeWeak j a) n t x

/-- The two constructed seed maps commute with the original change of section weaknesses. -/
theorem boundedAboveFlatAffineSectionOpenBassSeedMap_changeWeak (a : Under R) :
    boundedAboveFlatAffineSectionBassSeedMap a.right ≫
        parameterLoopingMap (boundedAboveFlatAffineSectionOpenBassConeChangeWeak j a) =
      (boundedAboveFlatAffineSectionOpenPrespectrumTransformation j).app a ≫
        boundedAboveFlatAffineSectionOpenBassSeedMap j a := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j a))).map n
        ((boundedAboveFlatAffineSectionOpenPrespectrumMap
          (inclusion j ((laurentUnderFunctor R).obj a))).map n
          ((boundedAboveFlatAffineSectionLaurentUnitHomotopy a.right).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j a))).map n
          ((boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n
            (t, (boundedAboveFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map n x))
    rw [boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy_changeWeak_apply]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedAboveFlatAffineSectionOpenBassNullHomotopy_changeWeak_apply j a n t x

section
attribute [local irreducible] boundedAboveFlatAffineSectionPrespectrumFunctor
  boundedAboveFlatAffineSectionOpenPrespectrumFunctor
  boundedAboveFlatAffineSectionOpenPrespectrumTransformation

/-- The unchanged Bass functor acts by this exact looped fine-to-coarse cone map. -/
theorem boundedAboveFlatAffineSectionOpenBassChangeWeak_functor_app (a : Under R) :
    HEq (((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedAboveFlatAffineSectionOpenPrespectrumTransformation j)).app a)
      (parameterLoopingMap (boundedAboveFlatAffineSectionOpenBassConeChangeWeak j a)) := HEq.rfl

end

attribute [local irreducible] boundedAboveFlatAffineSectionPrespectrumFunctor
  boundedAboveFlatAffineSectionOpenPrespectrumFunctor boundedAboveFlatAffineSectionOpenBassSeed
  boundedAboveFlatAffineSectionBassUnderSeed
  boundedAboveFlatAffineSectionOpenPrespectrumTransformation

/-- The strict fine-to-coarse natural arrow preserves the exact original seed transformations. -/
theorem boundedAboveFlatAffineSectionOpenBassSeed_changeWeak :
    boundedAboveFlatAffineSectionBassUnderSeed R ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedAboveFlatAffineSectionOpenPrespectrumTransformation j) =
      boundedAboveFlatAffineSectionOpenPrespectrumTransformation j ≫
        boundedAboveFlatAffineSectionOpenBassSeed j := by
  apply NatTrans.ext
  funext a
  have hA :
      ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (Under.forget R ⋙ boundedAboveFlatAffineSectionPrespectrumFunctor)).obj a =
        parameterLooping (boundedAboveFlatAffineSectionBassCone a.right) := by
    have h := congrArg
      (fun H ↦ (H.obj boundedAboveFlatAffineSectionPrespectrumFunctor).obj a)
      (KTheory.Bass.strictRingDiagramRestriction_comp_bass R)
    exact h.trans (KTheory.Bass.strictDiagramFunctor_obj
      laurentSquareFunctor boundedAboveFlatAffineSectionPrespectrumFunctor a.right)
  have hC :
      ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j)).obj a =
        parameterLooping (boundedAboveFlatAffineSectionOpenBassCone j a) :=
    KTheory.Bass.strictDiagramFunctor_obj (laurentUnderSquareFunctor R)
      (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j) a
  apply eq_of_heq
  have hleft := CategoryTheory.heq_comp rfl hA hC
    (boundedAboveFlatAffineSectionBassUnderSeed_app (R := R) a)
    (boundedAboveFlatAffineSectionOpenBassChangeWeak_functor_app j a)
  have hright := CategoryTheory.heq_comp rfl rfl hC
    (HEq.refl ((boundedAboveFlatAffineSectionOpenPrespectrumTransformation j).app a))
    (heq_of_eq (boundedAboveFlatAffineSectionOpenBassSeed_app j a))
  exact hleft.trans
    ((heq_of_eq (boundedAboveFlatAffineSectionOpenBassSeedMap_changeWeak j a)).trans hright.symm)

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionOpenBassSeedChangeWeak.lean:35-113"
  "adaptation" "Actual relative-open section construction with the original maps and weak class"]
  boundedAboveFlatAffineSectionOpenBassSquareChangeWeak
  boundedAboveFlatAffineSectionOpenBassConeChangeWeak
  boundedAboveFlatAffineSectionOpenBassNullHomotopy_changeWeak_apply
  boundedAboveFlatAffineSectionOpenBassSeedMap_changeWeak
  boundedAboveFlatAffineSectionOpenBassChangeWeak_functor_app
  boundedAboveFlatAffineSectionOpenBassSeed_changeWeak

attribute [colib_tag "COL-0504"]
  boundedAboveFlatAffineSectionOpenBassSeed_changeWeak
  boundedAboveFlatAffineSectionOpenBassSeedMap_changeWeak
  boundedAboveFlatAffineSectionOpenBassNullHomotopy_changeWeak_apply

end AlgebraicGeometry.Scheme.Modules
