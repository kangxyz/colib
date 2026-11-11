/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.KTheory.Bass.FiniteLoopConjugacy
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w

namespace Topology.LoopPrespectrum.FiniteLoopWordSlide
open FiniteLoopWords FiniteLoopWordSlide
variable {C : Type u} [Category.{v} C] {A B : C ⥤ LoopPrespectrum.{w}}

example (j : ℕ) {A B : C ⥤ LoopPrespectrum.{w}}
    (f : A ⟶ B ⋙ parameterLoopingFunctor) :
    loopInto j f = loopMap j f ≫ eqToHom (loopDiagram_postcomp j B) :=
  loopInto_eq j f

example (j : ℕ) {A B : C ⥤ LoopPrespectrum.{w}}
    (f : A ⟶ B ⋙ parameterLoopingFunctor) (X : C) (n : ℕ)
    (z : ((loopDiagram j A).obj X).space n) (t : Fin (j + 1) → unitInterval) :
    evaluate (j + 1) B X n (((loopInto j f).app X).map n z) t =
      Path.toContinuousMap ((f.app X).map n (evaluate j A X n z (Fin.init t)))
        (t (Fin.last j)) :=
  loopInto_evaluate j f X n z t

example (j : ℕ) {A B : C ⥤ LoopPrespectrum.{w}}
    (f : A ⟶ B ⋙ parameterLoopingFunctor) :
    loopInto j f ≫ (reversalIso (j + 1) B).hom =
      (reversalIso j A).hom ≫ loopInto j f ≫ (cyclicIso j B).hom :=
  loopInto_reversal j f

example (j : ℕ) {A B : C ⥤ LoopPrespectrum.{w}}
    (f : A ⟶ B ⋙ parameterLoopingFunctor) :
    (loopMap j f ≫ eqToHom (loopDiagram_postcomp j B)) ≫ (reversalIso (j + 1) B).hom =
      (reversalIso j A).hom ≫ (loopMap j f ≫ eqToHom (loopDiagram_postcomp j B)) ≫
        (cyclicIso j B).hom :=
  loopMap_reversal j f

end Topology.LoopPrespectrum.FiniteLoopWordSlide

namespace KTheory.Bass.FiniteLoopConjugacy
open FiniteLoopWords FiniteLoopWordSlide
variable {C : Type u} [Category.{v} C] {A B : C ⥤ LoopPrespectrum.{w}}

example (j : ℕ) (f : A ⟶ B ⋙ parameterLoopingFunctor)
    (p : A ⟶ A) (q : B ⟶ B)
    (h : f ≫ Functor.whiskerRight q parameterLoopingFunctor = p ≫ f) :
    loopInto j f ≫ loopMap (j + 1) q = loopMap j p ≫ loopInto j f :=
  loopInto_square j f p q h

example (j : ℕ) (f : A ⟶ B ⋙ parameterLoopingFunctor)
    (p : A ⟶ A) (q b : B ⟶ B)
    (h : f ≫ Functor.whiskerRight q parameterLoopingFunctor = p ≫ f) :
    loopInto j f ≫ (reversalIso (j + 1) B).hom ≫ loopMap (j + 1) (q ≫ b) =
      ((reversalIso j A).hom ≫ loopMap j p) ≫
        (loopInto j f ≫ (cyclicIso j B).hom ≫ loopMap (j + 1) b) :=
  loopInto_conjugacy j f p q b h

end KTheory.Bass.FiniteLoopConjugacy
end
