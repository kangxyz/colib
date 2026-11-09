/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.Polynomial.LaurentSquare
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionLaurentHomotopy
public import Colib.Topology.Prespectrum.StrictSquareNull
public import Colib.Topology.Prespectrum.NullLoopNaturality
public import Colib.RingTheory.KTheory.Bass.StrictRingSeed

/-!
# The original strict geometric Bass seed

The original Laurent-unit track is conjugated by the actual strict-square cone null cylinder.
Both tracks are literally coefficient-natural, so this construction is an actual natural
transformation from the original section diagram to its existing Bass endofunctor value.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Topology Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The actual two-chart square in the category of zero-preserving exact models. -/
def boundedAboveFlatAffineSectionBassModelSquare (R : CommRingCat.{u}) :=
  boundedAboveFlatAffineSectionModelFunctor.mapArrow.mapArrow.obj (laurentSquare R)

/-- The four actual exact coefficient maps on the native model square. -/
def boundedAboveFlatAffineSectionBassModelSquareMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionBassModelSquare R ⟶
      boundedAboveFlatAffineSectionBassModelSquare S :=
  boundedAboveFlatAffineSectionModelFunctor.mapArrow.mapArrow.map (laurentSquareMap f)

/-- The Laurent corner coefficient is literally the previously constructed canonical map. -/
theorem laurentSquareMap_right_right {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (laurentSquareMap f).right.right = laurentCoefficientMap f := rfl

/-- Before realization, the source composite is the exact Laurent-inclusion model map. -/
theorem boundedAboveFlatAffineSectionBassModelSquare_source (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineSectionBassModelSquare R).left.hom ≫
        (boundedAboveFlatAffineSectionBassModelSquare R).hom.right =
      boundedAboveFlatAffineSectionModelFunctor.map (laurentCoefficientInclusion R) := by
  change boundedAboveFlatAffineSectionModelFunctor.map
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫
    boundedAboveFlatAffineSectionModelFunctor.map (CommRingCat.ofHom Polynomial.toLaurent) = _
  rw [← Functor.map_comp, coefficient_toLaurent]
  rfl

/-- The existing strict Bass square evaluated on the original section prespectrum functor. -/
def boundedAboveFlatAffineSectionBassSquare (R : CommRingCat.{u}) :
    Arrow (Arrow LoopPrespectrum.{u+1}) :=
  boundedAboveFlatAffineSectionPrespectrumFunctor.mapArrow.mapArrow.obj (laurentSquare R)

/-- The original coefficient map on all four corners of the actual strict Bass square. -/
def boundedAboveFlatAffineSectionBassSquareMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionBassSquare R ⟶ boundedAboveFlatAffineSectionBassSquare S :=
  boundedAboveFlatAffineSectionPrespectrumFunctor.mapArrow.mapArrow.map (laurentSquareMap f)

/-- The literal mapping cone used in the existing strict Bass endofunctor. -/
def boundedAboveFlatAffineSectionBassCone (R : CommRingCat.{u}) : LoopPrespectrum.{u+1} :=
  mappingCone (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R))

/-- The unchanged strict-square coefficient map on that actual cone. -/
def boundedAboveFlatAffineSectionBassConeMap {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionBassCone R ⟶ boundedAboveFlatAffineSectionBassCone S :=
  mappingConeMap (strictSquareComparisonFunctor.map (boundedAboveFlatAffineSectionBassSquareMap f))

/-- The original two source legs compose to the same original Laurent coefficient inclusion. -/
theorem boundedAboveFlatAffineSectionBassSquare_source (R : CommRingCat.{u}) :
    (boundedAboveFlatAffineSectionBassSquare R).left.hom ≫
        (boundedAboveFlatAffineSectionBassSquare R).hom.right =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) := by
  change boundedAboveFlatAffineSectionPrespectrumFunctor.map
      (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) ≫
    boundedAboveFlatAffineSectionPrespectrumFunctor.map (CommRingCat.ofHom Polynomial.toLaurent) = _
  rw [← Functor.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact Polynomial.toLaurent_C r

/-- The original Laurent restriction becomes null through the actual source-leg cone cylinder. -/
def boundedAboveFlatAffineSectionBassNullHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedAboveFlatAffineSectionPrespectrumFunctor.map
      (laurentCoefficientInclusion R) ≫
      mappingConeInclusion (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)))
      (zeroHom (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R)
        (boundedAboveFlatAffineSectionBassCone R)) :=
  (StrictSquare.sourceNullHomotopy (boundedAboveFlatAffineSectionBassSquare R)).cast
    (by rw [boundedAboveFlatAffineSectionBassSquare_source]; rfl) rfl

/-- The original unit and original null cylinder define the genuine one-step strict seed. -/
def boundedAboveFlatAffineSectionBassSeedMap (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionPrespectrumFunctor.obj R ⟶
      parameterLooping (boundedAboveFlatAffineSectionBassCone R) :=
  ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).postcomp
    (mappingConeInclusion
      (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)))).nullLoopMap
      (boundedAboveFlatAffineSectionBassNullHomotopy R)

/-- The original null cylinder is literally natural at every interval value. -/
theorem boundedAboveFlatAffineSectionBassNullHomotopy_naturality_apply
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) (t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionBassConeMap f).map n
        ((boundedAboveFlatAffineSectionBassNullHomotopy R).level n (t, x)) =
      (boundedAboveFlatAffineSectionBassNullHomotopy S).level n
        (t, (boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedAboveFlatAffineSectionBassSquareMap f) n t x

/-- The actual null track retains the cylinder coordinate before quotienting. -/
theorem boundedAboveFlatAffineSectionBassNullHomotopy_apply (R : CommRingCat.{u})
    (n : ℕ) (s : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionBassNullHomotopy R).level n (s, x) =
      ReducedMappingCone.cylinder
        ((StrictSquare.span (boundedAboveFlatAffineSectionBassSquare R)).point n)
        ((boundedAboveFlatAffineSectionBassSquare R).right.right.point n)
        ((StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R)).map n)
        (s, (StrictSquare.sourceLeg (boundedAboveFlatAffineSectionBassSquare R)).map n x) := rfl

/-- The starting maps of the actual null tracks form their coefficient square. -/
theorem boundedAboveFlatAffineSectionBassNullHomotopy_start_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
        mappingConeInclusion
          (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R))) ≫
        boundedAboveFlatAffineSectionBassConeMap f =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion S) ≫
          mappingConeInclusion
            (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare S))) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  have h := boundedAboveFlatAffineSectionBassNullHomotopy_naturality_apply f n 0 x
  rw [(boundedAboveFlatAffineSectionBassNullHomotopy R).at_zero,
    (boundedAboveFlatAffineSectionBassNullHomotopy S).at_zero] at h
  exact h

/-- The terminal zero maps of the null tracks form their coefficient square. -/
theorem boundedAboveFlatAffineSectionBassNullHomotopy_end_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    zeroHom (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R)
        (boundedAboveFlatAffineSectionBassCone R) ≫ boundedAboveFlatAffineSectionBassConeMap f =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        zeroHom (boundedAboveFlatAffineSectionPrespectrumFunctor.obj S)
          (boundedAboveFlatAffineSectionBassCone S) := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact (boundedAboveFlatAffineSectionBassConeMap f).map_point n

/-- Naturality identifies the entire coherent null track after its exact endpoint transport. -/
theorem boundedAboveFlatAffineSectionBassNullHomotopy_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ((boundedAboveFlatAffineSectionBassNullHomotopy R).postcomp
      (boundedAboveFlatAffineSectionBassConeMap f)).cast
        (boundedAboveFlatAffineSectionBassNullHomotopy_start_naturality f)
        (boundedAboveFlatAffineSectionBassNullHomotopy_end_naturality f) =
      (boundedAboveFlatAffineSectionBassNullHomotopy S).precomp
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map f) := by
  apply Topology.LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  exact boundedAboveFlatAffineSectionBassNullHomotopy_naturality_apply f n t x

/-- Conjugating those exact original tracks gives a strictly coefficient-natural seed map. -/
theorem boundedAboveFlatAffineSectionBassSeedMap_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionBassSeedMap R ≫
        parameterLoopingMap (boundedAboveFlatAffineSectionBassConeMap f) =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedAboveFlatAffineSectionBassSeedMap S := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare S))).map n
        ((boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientMap f)).map n
          ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare S))).map n
          ((boundedAboveFlatAffineSectionLaurentUnitHomotopy S).level n
            (t, (boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map n x))
    rw [boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality_apply]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedAboveFlatAffineSectionBassNullHomotopy_naturality_apply f n t x

/-- The existing Bass endofunctor is the literal strict-square cone-loop composite. -/
theorem boundedAboveFlatAffineSectionBassFunctor_eq :
    KTheory.Bass.strictRingDiagramFunctor.obj boundedAboveFlatAffineSectionPrespectrumFunctor =
      laurentSquareFunctor ⋙ boundedAboveFlatAffineSectionPrespectrumFunctor.mapArrow.mapArrow ⋙
        strictSquareLoopedConeFunctor := rfl

/-- The actual geometric section seed, with no supplied seed or compatibility hypothesis. -/
def boundedAboveFlatAffineSectionBassSeed :
    boundedAboveFlatAffineSectionPrespectrumFunctor ⟶
      KTheory.Bass.strictRingDiagramFunctor.obj boundedAboveFlatAffineSectionPrespectrumFunctor :=
  KTheory.Bass.strictRingDiagramSeed boundedAboveFlatAffineSectionPrespectrumFunctor
    boundedAboveFlatAffineSectionBassSeedMap
    (fun f ↦ boundedAboveFlatAffineSectionBassSeedMap_naturality f)

/-- Evaluation of the actual natural seed retains the original pointwise seed map. -/
theorem boundedAboveFlatAffineSectionBassSeed_app (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionBassSeed.app R = boundedAboveFlatAffineSectionBassSeedMap R := rfl

/-- The same original Laurent action and two original null legs remain the literal loop value. -/
theorem boundedAboveFlatAffineSectionBassSeedMap_apply (R : CommRingCat.{u}) (n : ℕ)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) (t : unitInterval) :
    Path.toContinuousMap ((boundedAboveFlatAffineSectionBassSeedMap R).map n x) t =
      (((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).postcomp
        (mappingConeInclusion
          (StrictSquare.comparison (boundedAboveFlatAffineSectionBassSquare R))))
        |>.conjugateToZero (boundedAboveFlatAffineSectionBassNullHomotopy R)).level n (t, x) := rfl

end AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0361", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:33-63"
  "adaptation" "Actual two-chart section square, cone and literal Laurent source composite"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSquare
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSquare_source

attribute [colib_tag "COL-0361", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:66-116"
  "adaptation" "Actual cone cylinder and coefficient-natural reverse-null/unit/null seed"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassNullHomotopy
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap_naturality

attribute [colib_tag "COL-0361", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionBassSeed.lean:119-141"
  "adaptation" "Genuine geometric natural transformation and its unchanged pointwise loop"]
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeed
  AlgebraicGeometry.Scheme.Modules.boundedAboveFlatAffineSectionBassSeedMap_apply
