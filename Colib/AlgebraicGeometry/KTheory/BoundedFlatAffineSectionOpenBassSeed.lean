/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentUnderSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionOpenDiagramLaurent
public import Colib.Topology.Prespectrum.StrictSquareNull
public import Colib.Topology.Prespectrum.NullLoopNaturality
public import Colib.KTheory.Bass.StrictDiagram

/-!
# The actual Bass seed for a fixed original relative-open coefficient diagram

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
def boundedAboveFlatAffineSectionOpenBassSquare (a : Under R) :
    Arrow (Arrow LoopPrespectrum.{u+1}) :=
  (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).mapArrow.mapArrow.obj
    (laurentUnderSquare R a)

/-- The original coefficient map on all four corners of the actual strict Bass square. -/
def boundedAboveFlatAffineSectionOpenBassSquareMap {a b : Under R} (f : a ⟶ b) :
    boundedAboveFlatAffineSectionOpenBassSquare j a ⟶
      boundedAboveFlatAffineSectionOpenBassSquare j b :=
  (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).mapArrow.mapArrow.map
    (laurentUnderSquareMap R f)

/-- The literal mapping cone used in the existing strict Bass endofunctor. -/
def boundedAboveFlatAffineSectionOpenBassCone (a : Under R) : LoopPrespectrum.{u+1} :=
  mappingCone (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j a))

/-- The unchanged strict-square coefficient map on that actual cone. -/
def boundedAboveFlatAffineSectionOpenBassConeMap {a b : Under R} (f : a ⟶ b) :
    boundedAboveFlatAffineSectionOpenBassCone j a ⟶ boundedAboveFlatAffineSectionOpenBassCone j b :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedAboveFlatAffineSectionOpenBassSquareMap j f))

/-- The original two source legs compose to the same original Laurent coefficient inclusion. -/
theorem boundedAboveFlatAffineSectionOpenBassSquare_source (a : Under R) :
    (boundedAboveFlatAffineSectionOpenBassSquare j a).left.hom ≫
        (boundedAboveFlatAffineSectionOpenBassSquare j a).hom.right =
      (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map
        ((laurentUnderCoefficient R).app a) := by
  change (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map
    ((polynomialUnderCoefficient R).app a) ≫
      (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map ((underToLaurent R).app a) = _
  rw [← Functor.map_comp, polynomialUnderCoefficient_toLaurent]

/-- The original Laurent restriction becomes null through the actual source-leg cone cylinder. -/
def boundedAboveFlatAffineSectionOpenBassNullHomotopy (a : Under R) :
    Homotopy ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map
      ((laurentUnderCoefficient R).app a) ≫
      mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j a)))
      (zeroHom ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a)
        (boundedAboveFlatAffineSectionOpenBassCone j a)) :=
  (StrictSquare.sourceNullHomotopy (boundedAboveFlatAffineSectionOpenBassSquare j a)).cast
    (by rw [boundedAboveFlatAffineSectionOpenBassSquare_source]; rfl) rfl

/-- The original unit and original null cylinder define the genuine one-step strict seed. -/
def boundedAboveFlatAffineSectionOpenBassSeedMap (a : Under R) :
    (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a ⟶
      parameterLooping (boundedAboveFlatAffineSectionOpenBassCone j a) :=
  ((boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).postcomp
    (mappingConeInclusion
      (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j a)))).nullLoopMap
      (boundedAboveFlatAffineSectionOpenBassNullHomotopy j a)

/-- The original null cylinder is literally natural at every interval value. -/
theorem boundedAboveFlatAffineSectionOpenBassNullHomotopy_naturality_apply
    {a b : Under R} (f : a ⟶ b) (n : ℕ) (t : unitInterval)
    (x : ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    (boundedAboveFlatAffineSectionOpenBassConeMap j f).map n
        ((boundedAboveFlatAffineSectionOpenBassNullHomotopy j a).level n (t, x)) =
      (boundedAboveFlatAffineSectionOpenBassNullHomotopy j b).level n
        (t, ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map f).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedAboveFlatAffineSectionOpenBassSquareMap j f) n t x

/-- Conjugating those exact original tracks gives a strictly coefficient-natural seed map. -/
theorem boundedAboveFlatAffineSectionOpenBassSeedMap_naturality
    {a b : Under R} (f : a ⟶ b) :
    boundedAboveFlatAffineSectionOpenBassSeedMap j a ≫
        parameterLoopingMap (boundedAboveFlatAffineSectionOpenBassConeMap j f) =
      (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map f ≫
        boundedAboveFlatAffineSectionOpenBassSeedMap j b := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j b))).map n
        (((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map
          ((laurentUnderFunctor R).map f)).map n
          ((boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j b))).map n
          ((boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j b).level n
            (t, ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).map f).map n x))
    rw [boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy_naturality_apply j]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedAboveFlatAffineSectionOpenBassNullHomotopy_naturality_apply j f n t x

/-- The existing Bass endofunctor is the literal strict-square cone-loop composite. -/
theorem boundedAboveFlatAffineSectionOpenBassFunctor_eq :
    (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j) =
      laurentUnderSquareFunctor R ⋙
        (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).mapArrow.mapArrow ⋙
        strictSquareLoopedConeFunctor := rfl

/-- The actual relative-open section seed, with no supplied seed or compatibility hypothesis. -/
def boundedAboveFlatAffineSectionOpenBassSeed :
    (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j) ⟶
      (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
      (boundedAboveFlatAffineSectionOpenPrespectrumFunctor j) :=
  { app := boundedAboveFlatAffineSectionOpenBassSeedMap j
    naturality _ _ f := (boundedAboveFlatAffineSectionOpenBassSeedMap_naturality j f).symm }

/-- Evaluation of the actual natural seed retains the original pointwise seed map. -/
theorem boundedAboveFlatAffineSectionOpenBassSeed_app (a : Under R) :
    (boundedAboveFlatAffineSectionOpenBassSeed j).app a =
      boundedAboveFlatAffineSectionOpenBassSeedMap j a := rfl

/-- The same original Laurent action and two original null legs remain the literal loop value. -/
theorem boundedAboveFlatAffineSectionOpenBassSeedMap_apply (a : Under R) (n : ℕ)
    (x : ((boundedAboveFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n)
    (t : unitInterval) :
    Path.toContinuousMap ((boundedAboveFlatAffineSectionOpenBassSeedMap j a).map n x) t =
      (((boundedAboveFlatAffineSectionOpenDiagramLaurentHomotopy j a).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedAboveFlatAffineSectionOpenBassSquare j a))))
        |>.conjugateToZero
          (boundedAboveFlatAffineSectionOpenBassNullHomotopy j a)).level n (t, x) := rfl

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionOpenBassSeed.lean:34-154"
  "adaptation" "Actual relative-open section construction with the original maps and weak class"]
  boundedAboveFlatAffineSectionOpenBassSquare
  boundedAboveFlatAffineSectionOpenBassSquareMap
  boundedAboveFlatAffineSectionOpenBassCone
  boundedAboveFlatAffineSectionOpenBassConeMap
  boundedAboveFlatAffineSectionOpenBassSquare_source
  boundedAboveFlatAffineSectionOpenBassNullHomotopy
  boundedAboveFlatAffineSectionOpenBassSeedMap
  boundedAboveFlatAffineSectionOpenBassNullHomotopy_naturality_apply
  boundedAboveFlatAffineSectionOpenBassSeedMap_naturality
  boundedAboveFlatAffineSectionOpenBassFunctor_eq
  boundedAboveFlatAffineSectionOpenBassSeed
  boundedAboveFlatAffineSectionOpenBassSeed_app
  boundedAboveFlatAffineSectionOpenBassSeedMap_apply

attribute [colib_tag "COL-0504"]
  boundedAboveFlatAffineSectionOpenBassSeed
  boundedAboveFlatAffineSectionOpenBassSeedMap_apply

end AlgebraicGeometry.Scheme.Modules
