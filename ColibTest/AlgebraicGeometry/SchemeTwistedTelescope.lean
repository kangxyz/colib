/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedTelescope
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum CategoryTheory.Waldhausen.IteratedS
open Topology.LoopPrespectrum.FiniteParameterLooping
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
open FiniteConeTopology GeometricConeFixedWords
variable {F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

example (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    normalized squareFunctor i F ≅ normalized squareFunctor i F :=
  conjugatingIso i F

example (A : Track laurent.op coefficient F) (i : ℕ) :
    seed (coneTrack A i) ≫ (strictDiagramFunctor squareFunctor).map (wordAt i F).hom =
      (wordAt i F).hom ≫ seed (coneTrack A i) :=
  wordAt_seed_square A i

example (A : Track laurent.op coefficient F) (i : ℕ) :
    normalizedTransition A i ≫ (conjugatingIso (i + 1) F).hom =
      (conjugatingIso i F).hom ≫ twistedTransition A i :=
  twisted_adjacent A i

example (A : Track laurent.op coefficient F) :
    Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w} :=
  twistedTelescope A

example (A : Track laurent.op coefficient F) :
    normalizedTelescope A ⟶ twistedTelescope A :=
  conjugacyTelescopeMap A

example (A : Track laurent.op coefficient F)
    (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : ((normalized squareFunctor i F).obj X).space n) :
    ((conjugacyTelescopeMap A).app X).map n
      (Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
        (fun j => (normalizedTransition A j).app X) n i (s, x)) =
    Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
      (fun j => (twistedTransition A j).app X) n i
      (s, ((conjugatingIso i F).hom.app X).map n x) :=
  conjugacyTelescopeMap_cylinder A X n i s x

example (A : Track laurent.op coefficient F) (i : ℕ) :
    Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
        (normalizedTransition A) i ≫ conjugacyTelescopeMap A =
      (conjugatingIso i F).hom ≫
        Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
          (twistedTransition A) i :=
  conjugacyTelescopeMap_inclusion A i

example (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence ((conjugacyTelescopeMap A).app X) :=
  model_conjugacyTelescopeMap_stable M A X

end KTheory.Bass.SchemeNaturalSeed
end
