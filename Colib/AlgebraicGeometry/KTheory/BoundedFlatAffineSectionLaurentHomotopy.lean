/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.LaurentInclusionSquare
public import Colib.AlgebraicGeometry.Modules.BoundedFlatAffineSectionLaurentUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatAffineSectionPrespectrum
public import Colib.CategoryTheory.Functor.IdentityAutomorphismSquare
public import Colib.Topology.Prespectrum.HomotopyTransport
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumIsoNaturality

/-!
# The original Laurent-unit loop on the strict section prespectrum

The original Laurent automorphism supplies the entire structure-compatible iterated-S loop.
Its actual coefficient square gives literal naturality at every homotopy time, including
all positive realizations and the unchanged degree-zero compact-open loop space.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- The original Laurent action on sections reindexed along the actual inclusion. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentPullback.lean:26-32"
  "adaptation" "Actual pointwise section action after Laurent coefficient inclusion"]
def boundedAboveFlatAffineSectionLaurentPullbackUnitIso (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R) ≅
      boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R) :=
  Functor.IdentityAutomorphism.onFunctor
    (boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineSectionLaurentUnitIso R)

/-- The actual Laurent restriction model square commutes strictly for every coefficient map. -/
@[colib_tag "COL-0360", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentHomotopy.lean:33-43"
  "adaptation" "Native strict section Laurent track and exact coefficient square"]
theorem boundedAboveFlatAffineSectionLaurentModelSquare {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R) ≫
        boundedAboveFlatAffineSectionModelMap (laurentCoefficientMap f) =
      boundedAboveFlatAffineSectionModelMap f ≫
        boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion S) := by
  change boundedAboveFlatAffineSectionModelFunctor.map (laurentCoefficientInclusion R) ≫
      boundedAboveFlatAffineSectionModelFunctor.map (laurentCoefficientMap f) =
    boundedAboveFlatAffineSectionModelFunctor.map f ≫
      boundedAboveFlatAffineSectionModelFunctor.map (laurentCoefficientInclusion S)
  rw [← Functor.map_comp, ← Functor.map_comp, laurentCoefficientInclusion_square]

private theorem sectionLaurentPullbackUnitIso_eq (R : CommRingCat.{u}) :
    boundedAboveFlatAffineSectionLaurentPullbackUnitIso R =
      Functor.IdentityAutomorphism.onFunctor
        (boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R))
        (boundedAboveFlatAffineSectionLaurentUnitIso R) := rfl

/-- The same literal model equality intertwines the original Laurent automorphisms. -/
@[colib_tag "COL-0360", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentHomotopy.lean:51-66"
  "adaptation" "Native strict section Laurent track and exact coefficient square"]
theorem boundedAboveFlatAffineSectionLaurentModelUnitSquare {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Functor.whiskerRight (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R).hom
        (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f)) ≫
        eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSectionLaurentModelSquare f)) =
      eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSectionLaurentModelSquare f)) ≫
        Functor.whiskerLeft (boundedAboveFlatAffineSectionsMap f)
          (boundedAboveFlatAffineSectionLaurentPullbackUnitIso S).hom := by
  rw [sectionLaurentPullbackUnitIso_eq, sectionLaurentPullbackUnitIso_eq]
  exact Functor.IdentityAutomorphism.onFunctor_whisker_square
    (boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineSectionsMap (laurentCoefficientInclusion S))
    (boundedAboveFlatAffineSectionsMap f)
    (boundedAboveFlatAffineSectionsMap (laurentCoefficientMap f))
    (eqToHom (congrArg (fun k ↦ k.hom.toFunctor)
          (boundedAboveFlatAffineSectionLaurentModelSquare f)))
    (boundedAboveFlatAffineSectionLaurentUnitIso R) (boundedAboveFlatAffineSectionLaurentUnitIso S)
    (boundedAboveFlatAffineSectionLaurentUnitIso_coefficient f)

/-- The unchanged original Laurent coordinate acts on the entire strict section prespectrum. -/
@[colib_tag "COL-0360", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentHomotopy.lean:68-73"
  "adaptation" "Native strict section Laurent track and exact coefficient square"]
def boundedAboveFlatAffineSectionLaurentUnitHomotopy (R : CommRingCat.{u}) :
    Homotopy (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R))
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R)) :=
  prespectrumIsoHomotopy (boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R)

/-- Coefficient naturality retains every original interval value at every prespectrum level. -/
@[colib_tag "COL-0360", colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/Affine/SectionLaurentHomotopy.lean:75-90"
  "adaptation" "Entire same-time coefficient naturality at all native prespectrum levels"]
theorem boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality_apply
    {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℕ) (t : unitInterval)
    (x : (boundedAboveFlatAffineSectionPrespectrumFunctor.obj R).space n) :
    (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientMap f)).map n
        ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).level n (t, x)) =
      (boundedAboveFlatAffineSectionLaurentUnitHomotopy S).level n
        (t, (boundedAboveFlatAffineSectionPrespectrumFunctor.map f).map n x) := by
  exact prespectrumIsoHomotopy_square_apply
    (boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion R))
    (boundedAboveFlatAffineSectionModelMap (laurentCoefficientInclusion S))
    (boundedAboveFlatAffineSectionModelMap f)
    (boundedAboveFlatAffineSectionModelMap (laurentCoefficientMap f))
    (boundedAboveFlatAffineSectionLaurentPullbackUnitIso R)
    (boundedAboveFlatAffineSectionLaurentPullbackUnitIso S)
    (boundedAboveFlatAffineSectionLaurentModelSquare f)
    (boundedAboveFlatAffineSectionLaurentModelUnitSquare f) n t x

/-- The actual coefficient square is strict on whole prespectrum maps. -/
theorem boundedAboveFlatAffineSectionLaurentPrespectrumSquare
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion R) ≫
        boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientMap f) =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientInclusion S) := by
  rw [← Functor.map_comp, ← Functor.map_comp, laurentCoefficientInclusion_square]

/-- Every time slice retains literal coefficient naturality as an entire prespectrum map. -/
theorem boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality_at
    {R S : CommRingCat.{u}} (f : R ⟶ S) (t : unitInterval) :
    (boundedAboveFlatAffineSectionLaurentUnitHomotopy R).at t ≫
        boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientMap f) =
      boundedAboveFlatAffineSectionPrespectrumFunctor.map f ≫
        (boundedAboveFlatAffineSectionLaurentUnitHomotopy S).at t := by
  apply Topology.LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality_apply f n t x

/-- Endpoint transport identifies the entire postcomposed and precomposed Laurent tracks. -/
@[colib_tag "COL-0360"]
theorem boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    ((boundedAboveFlatAffineSectionLaurentUnitHomotopy R).postcomp
      (boundedAboveFlatAffineSectionPrespectrumFunctor.map (laurentCoefficientMap f))).cast
        (boundedAboveFlatAffineSectionLaurentPrespectrumSquare f)
        (boundedAboveFlatAffineSectionLaurentPrespectrumSquare f) =
      (boundedAboveFlatAffineSectionLaurentUnitHomotopy S).precomp
        (boundedAboveFlatAffineSectionPrespectrumFunctor.map f) := by
  apply Topology.LoopPrespectrum.Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨t, x⟩
  exact boundedAboveFlatAffineSectionLaurentUnitHomotopy_naturality_apply f n t x

end AlgebraicGeometry.Scheme.Modules
