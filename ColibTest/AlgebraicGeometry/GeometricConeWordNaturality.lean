/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeWordNaturality
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.GeometricConeFixedWords
open GeometricConeInterchange FiniteConeTopology NormalizedStageMap

example (i : ℕ)
    {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    (Functor.FixedWords.power coneFunctor i).map η ≫ eqToHom (power_obj i G) =
      eqToHom (power_obj i F) ≫ iterateMap squareFunctor i η :=
  power_obj_naturality i η

example (i : ℕ)
    {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    iterateMap squareFunctor (i + 1) η ≫ (betaAt i G).hom =
      (betaAt i F).hom ≫ iterateMap squareFunctor (i + 1) η :=
  betaAt_naturality i η

example (i : ℕ)
    {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (η : F ⟶ G) :
    iterateMap squareFunctor i η ≫ (wordAt i G).hom =
      (wordAt i F).hom ≫ iterateMap squareFunctor i η :=
  wordAt_naturality i η

end KTheory.Bass.GeometricConeFixedWords
end
