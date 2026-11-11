/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeBetaRecursion
noncomputable section
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u v w
namespace KTheory.Bass.GeometricConeFixedWords
open GeometricConeInterchange FiniteConeTopology
example (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (Functor.FixedWords.power coneFunctor i).obj F = iterate squareFunctor i F :=
  power_obj i F

example : word.{u, w} 2 = permutationFunctorIso :=
  word_two

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (word 3).hom.app F =
      coneFunctor.map (permutationNatIso F).hom ≫
      (permutationNatIso (coneFunctor.obj F)).hom ≫
      coneFunctor.map (permutationNatIso F).hom :=
  word_three_hom_app F

example {F G : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}} (f : F ⟶ G) :
    coneFunctor.map f = ConeTrack.map squareFunctor f :=
  coneFunctor_map f

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (wordAt 0 F).hom = 𝟙 F :=
  wordAt_zero_hom F

example (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (betaAt 0 F).hom = 𝟙 (iterate squareFunctor 1 F) :=
  betaAt_zero_hom F

example (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (wordAt (i + 1) F).hom =
      ConeTrack.map squareFunctor (wordAt i F).hom ≫ (betaAt i F).hom :=
  wordAt_succ_hom i F

example (i : ℕ) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    (betaAt (i + 1) F).hom =
      (permutationNatIso (iterate squareFunctor i F)).hom ≫
        ConeTrack.map squareFunctor (betaAt i F).hom :=
  betaAt_succ_hom i F

end KTheory.Bass.GeometricConeFixedWords
end
