/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTwistedInputMaps
noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u w
namespace KTheory.Bass.SchemeNaturalSeed
open NaturalTrack GeometricSeedCospan NormalizedStageMap
open FiniteLoopWords FiniteConeTopology GeometricConeFixedWords
variable {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}}

example (i : ℕ) (η : F ⟶ G) :
    normalizedMap squareFunctor i η ≫ (conjugatingIso i G).hom =
      (conjugatingIso i F).hom ≫ normalizedMap squareFunctor i η :=
  conjugatingIso_naturality i η

variable (A : Track laurent.op coefficient F) (B : Track laurent.op coefficient G)
    (η : F ⟶ G) (hη : Equivariant A B η)

include hη
example (i : ℕ) :
    normalizedMap squareFunctor i η ≫ twistedTransition B i =
      twistedTransition A i ≫ normalizedMap squareFunctor (i + 1) η :=
  twistedInput_transition A B η hη i

example : twistedTelescope A ⟶ twistedTelescope B :=
  twistedInputMap A B η hη

example (X : Scheme.{u}ᵒᵖ) (n i : ℕ) (s : unitInterval)
    (x : ((normalized squareFunctor i F).obj X).space n) :
    ((twistedInputMap A B η hη).app X).map n
      (Telescope.cylinder (fun j => (normalized squareFunctor j F).obj X)
        (fun j => (twistedTransition A j).app X) n i (s, x)) =
      Telescope.cylinder (fun j => (normalized squareFunctor j G).obj X)
        (fun j => (twistedTransition B j).app X) n i
        (s, ((normalizedMap squareFunctor i η).app X).map n x) :=
  twistedInputMap_cylinder A B η hη X n i s x

example (i : ℕ) :
    Telescope.diagramInclusion (fun j => normalized squareFunctor j F)
        (twistedTransition A) i ≫ twistedInputMap A B η hη =
      normalizedMap squareFunctor i η ≫
        Telescope.diagramInclusion (fun j => normalized squareFunctor j G)
          (twistedTransition B) i :=
  twistedInputMap_inclusion A B η hη i

example :
    normalizedInputMap A B η hη ≫ conjugacyTelescopeMap B =
      conjugacyTelescopeMap A ≫ twistedInputMap A B η hη :=
  conjugacyTelescopeMap_input_square A B η hη

end KTheory.Bass.SchemeNaturalSeed
end
