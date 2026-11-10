/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSupportedSectionDiagramLaurent
public import Colib.Topology.Prespectrum.StrictSquareNull
public import Colib.Topology.Prespectrum.NullLoopNaturality
public import Colib.KTheory.Bass.StrictDiagram

/-!
# The actual Bass seed for a fixed original supported coefficient diagram

The original Laurent-unit track is conjugated by the actual strict-square cone null cylinder.
Both tracks are proved literally natural on the fixed-open Under R diagram, so they give an
actual natural transformation to its existing Bass endofunctor. The identity-algebra level keeps
its specified pullback of j; comparison with the original j uses its separate actual projection
iso, never a literal identification of independently chosen pullback objects.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The existing strict Bass square evaluated on the original section prespectrum functor. -/
def boundedAboveFlatAffineSupportedSectionBassSquare (a : Under R) :
    Arrow (Arrow LoopPrespectrum.{u+1}) :=
  (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)

/-- The original coefficient map on all four corners of the actual strict Bass square. -/
def boundedAboveFlatAffineSupportedSectionBassSquareMap {a b : Under R} (f : a ⟶ b) :
    boundedAboveFlatAffineSupportedSectionBassSquare j a ⟶
      boundedAboveFlatAffineSupportedSectionBassSquare j b :=
  (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).mapArrow.mapArrow.map
    (laurentUnderSquareMap R f)

/-- The literal mapping cone used in the existing strict Bass endofunctor. -/
def boundedAboveFlatAffineSupportedSectionBassCone (a : Under R) : LoopPrespectrum.{u+1} :=
  mappingCone (StrictSquare.comparison (boundedAboveFlatAffineSupportedSectionBassSquare j a))

/-- The unchanged strict-square coefficient map on that actual cone. -/
def boundedAboveFlatAffineSupportedSectionBassConeMap {a b : Under R} (f : a ⟶ b) :
    boundedAboveFlatAffineSupportedSectionBassCone j a ⟶
      boundedAboveFlatAffineSupportedSectionBassCone j b :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedAboveFlatAffineSupportedSectionBassSquareMap j f))

/-- The original two source legs compose to the same original Laurent coefficient inclusion. -/
theorem boundedAboveFlatAffineSupportedSectionBassSquare_source (a : Under R) :
    (boundedAboveFlatAffineSupportedSectionBassSquare j a).left.hom ≫
        (boundedAboveFlatAffineSupportedSectionBassSquare j a).hom.right =
      (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a) := by
  change (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map
    ((polynomialUnderCoefficient R).app a) ≫
      (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map
        ((underToLaurent R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurent]

/-- The original Laurent restriction becomes null through the actual source-leg cone cylinder. -/
def boundedAboveFlatAffineSupportedSectionBassNullHomotopy (a : Under R) :
    Homotopy ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map
      ((laurentUnderCoefficient R).app a) ≫
      mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSupportedSectionBassSquare j a)))
      (zeroHom ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a)
        (boundedAboveFlatAffineSupportedSectionBassCone j a)) :=
  (StrictSquare.sourceNullHomotopy (boundedAboveFlatAffineSupportedSectionBassSquare j a)).cast
    (by rw [boundedAboveFlatAffineSupportedSectionBassSquare_source]; rfl) rfl

/-- The original unit and original null cylinder define the genuine one-step strict seed. -/
def boundedAboveFlatAffineSupportedSectionBassSeedMap (a : Under R) :
    (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a ⟶
      parameterLooping (boundedAboveFlatAffineSupportedSectionBassCone j a) :=
  ((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).postcomp
    (mappingConeInclusion
      (StrictSquare.comparison (boundedAboveFlatAffineSupportedSectionBassSquare j a)))).nullLoopMap
      (boundedAboveFlatAffineSupportedSectionBassNullHomotopy j a)

/-- The original null cylinder is literally natural at every interval value. -/
theorem boundedAboveFlatAffineSupportedSectionBassNullHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedAboveFlatAffineSupportedSectionBassConeMap j f).map n
        ((boundedAboveFlatAffineSupportedSectionBassNullHomotopy j a).level n (t, x)) =
      (boundedAboveFlatAffineSupportedSectionBassNullHomotopy j b).level n
        (t, ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedAboveFlatAffineSupportedSectionBassSquareMap j f) n t x

/-- Conjugating those exact original tracks gives a strictly coefficient-natural seed map. -/
theorem boundedAboveFlatAffineSupportedSectionBassSeedMap_naturality
    {a b : Under R} (f : a ⟶ b) :
    boundedAboveFlatAffineSupportedSectionBassSeedMap j a ≫
        parameterLoopingMap (boundedAboveFlatAffineSupportedSectionBassConeMap j f) =
      (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f ≫
        boundedAboveFlatAffineSupportedSectionBassSeedMap j b := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedAboveFlatAffineSupportedSectionBassSquare j b))).map n
        (((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map
          ((laurentUnderFunctor R).map f)).map n
          ((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSupportedSectionBassSquare j b))).map n
          ((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j b).level n
            (t, ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).map f).map n x))
    rw [boundedAboveFlatAffineSupportedDiagramLaurentHomotopy_naturality_apply j]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedAboveFlatAffineSupportedSectionBassNullHomotopy_naturality_apply j f n t x

/-- The existing Bass endofunctor is the literal strict-square cone-loop composite. -/
theorem boundedAboveFlatAffineSupportedSectionBassFunctor_eq :
    (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j) =
      laurentUnderSquareFunctor R ⋙
        (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).mapArrow.mapArrow ⋙
        strictSquareLoopedConeFunctor := rfl

/-- The actual geometric section seed, with no supplied seed or compatibility hypothesis. -/
def boundedAboveFlatAffineSupportedSectionBassSeed :
    (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j) ⟶
      (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j) :=
  { app := boundedAboveFlatAffineSupportedSectionBassSeedMap j
    naturality _ _ f := (boundedAboveFlatAffineSupportedSectionBassSeedMap_naturality j f).symm }

/-- Evaluation of the actual natural seed retains the original pointwise seed map. -/
theorem boundedAboveFlatAffineSupportedSectionBassSeed_app (a : Under R) :
    (boundedAboveFlatAffineSupportedSectionBassSeed j).app a =
      boundedAboveFlatAffineSupportedSectionBassSeedMap j a := rfl

/-- The same original Laurent action and two original null legs remain the literal loop value. -/
theorem boundedAboveFlatAffineSupportedSectionBassSeedMap_apply (a : Under R) (n : ℕ)
    (x : ((boundedAboveFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n)
    (t : unitInterval) :
    Path.toContinuousMap ((boundedAboveFlatAffineSupportedSectionBassSeedMap j a).map n x) t =
      (((boundedAboveFlatAffineSupportedDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedAboveFlatAffineSupportedSectionBassSquare j a))))
        |>.conjugateToZero
          (boundedAboveFlatAffineSupportedSectionBassNullHomotopy j a)).level n (t, x) := rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SupportedSectionBassSeed.lean:34-154"
  "adaptation" "Actual supported Laurent null-unit-null seed and strict coefficient naturality"]
  boundedAboveFlatAffineSupportedSectionBassSeed
  boundedAboveFlatAffineSupportedSectionBassSeedMap_apply
  boundedAboveFlatAffineSupportedSectionBassSeedMap_naturality
  boundedAboveFlatAffineSupportedSectionBassNullHomotopy_naturality_apply

attribute [colib_tag "COL-0503"]
  boundedAboveFlatAffineSupportedSectionBassSeed
  boundedAboveFlatAffineSupportedSectionBassSeedMap_apply
  boundedAboveFlatAffineSupportedSectionBassSeedMap_naturality

end AlgebraicGeometry.Scheme.Modules
