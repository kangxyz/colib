/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.FiniteLoopWords
public import Colib.Topology.Prespectrum.LoopTranspose

/-!
# Sliding an arbitrary new loop through the fixed reversal

For every original diagram map `f : A → Omega B`, finite looping followed by reversal
agrees with reversing the old input times and then applying the prescribed cyclic word.
The entire functor-association transport is retained. The new time remains distinct from
all old loop times. This is independent of seeds, cone permutations, and unit actions.
-/
@[expose] public section
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
open Topology.LoopPrespectrum.FiniteParameterLooping
universe u v w
namespace Topology.LoopPrespectrum.FiniteLoopWordSlide
open Topology.LoopPrespectrum.FiniteParameterLooping Topology.LoopPrespectrum.FiniteLoopWords
variable {C : Type u} [Category.{v} C]

/-- Loop a map into one loop, with the target associated as the successor loop count. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWordSlide.lean:30"
  "adaptation" "Original fixed-order loop slide retaining the complete association transport."]
def loopInto : ∀ (j : ℕ) {A B : C ⥤ LoopPrespectrum.{w}},
    (A ⟶ B ⋙ parameterLoopingFunctor) → (loopDiagram j A ⟶ loopDiagram (j + 1) B)
  | 0, _, _, f => f
  | j + 1, _, _, f => Functor.whiskerRight (loopInto j f) parameterLoopingFunctor

private theorem whiskerRight_eqToHom {A B : C ⥤ LoopPrespectrum.{w}} (h : A = B) :
    Functor.whiskerRight (eqToHom h) parameterLoopingFunctor =
      eqToHom (congrArg (fun F => F ⋙ parameterLoopingFunctor) h) := by
  subst B
  exact Functor.whiskerRight_id' parameterLoopingFunctor

/-- The recursive map is the original looped map with its full functor-equality cast. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWordSlide.lean:42"
  "adaptation" "Original fixed-order loop slide retaining the complete association transport."]
theorem loopInto_eq (j : ℕ) {A B : C ⥤ LoopPrespectrum.{w}}
    (f : A ⟶ B ⋙ parameterLoopingFunctor) :
    loopInto j f = loopMap j f ≫ eqToHom (loopDiagram_postcomp j B) := by
  induction j with
  | zero => exact (Category.comp_id f).symm
  | succ j ih =>
    change Functor.whiskerRight (loopInto j f) parameterLoopingFunctor = _
    rw [ih, Functor.whiskerRight_comp, whiskerRight_eqToHom]
    rfl

/-- The last coordinate is the new loop produced by the given map. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWordSlide.lean:53"
  "adaptation" "Original fixed-order loop slide retaining the complete association transport."]
theorem loopInto_evaluate (j : ℕ) {A B : C ⥤ LoopPrespectrum.{w}}
    (f : A ⟶ B ⋙ parameterLoopingFunctor) (X : C) (n : ℕ)
    (z : ((loopDiagram j A).obj X).space n) (t : Fin (j + 1) → unitInterval) :
    evaluate (j + 1) B X n (((loopInto j f).app X).map n z) t =
      Path.toContinuousMap ((f.app X).map n (evaluate j A X n z (Fin.init t)))
        (t (Fin.last j)) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change evaluate (j + 1) B X n
      (((loopInto j f).app X).map n (Path.toContinuousMap z (t 0))) (Fin.tail t) = _
    rw [ih]
    congr 2

private theorem init_reverse (j : ℕ) (t : Fin (j + 1) → unitInterval) :
    Fin.init (t ∘ Fin.rev) = Fin.tail t ∘ Fin.rev := by
  funext a
  simp only [Fin.init, Function.comp_apply, Fin.tail, Fin.rev_castSucc]

/-- The complete arbitrary map obeys the fixed reversal/cyclic slide identity. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWordSlide.lean:73"
  "adaptation" "Original fixed-order loop slide retaining the complete association transport."]
theorem loopInto_reversal (j : ℕ) {A B : C ⥤ LoopPrespectrum.{w}}
    (f : A ⟶ B ⋙ parameterLoopingFunctor) :
    loopInto j f ≫ (reversalIso (j + 1) B).hom =
      (reversalIso j A).hom ≫ loopInto j f ≫ (cyclicIso j B).hom := by
  apply evaluation_hom_ext (j + 1)
  intro X n z t
  change evaluate (j + 1) B X n
      (((reversalIso (j + 1) B).hom.app X).map n (((loopInto j f).app X).map n z)) t =
    evaluate (j + 1) B X n (((cyclicIso j B).hom.app X).map n
      (((loopInto j f).app X).map n (((reversalIso j A).hom.app X).map n z))) t
  rw [reversalIso_evaluate, loopInto_evaluate, cyclicIso_evaluate, loopInto_evaluate,
    reversalIso_evaluate, init_reverse]
  simp only [Function.comp_apply, Fin.rev_last, Fin.init_snoc, Fin.snoc_last]

/-- The same full identity written with the original finite-loop functor and explicit cast. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/FiniteLoopWordSlide.lean:88"
  "adaptation" "Original fixed-order loop slide retaining the complete association transport."]
theorem loopMap_reversal (j : ℕ) {A B : C ⥤ LoopPrespectrum.{w}}
    (f : A ⟶ B ⋙ parameterLoopingFunctor) :
    (loopMap j f ≫ eqToHom (loopDiagram_postcomp j B)) ≫ (reversalIso (j + 1) B).hom =
      (reversalIso j A).hom ≫ (loopMap j f ≫ eqToHom (loopDiagram_postcomp j B)) ≫
        (cyclicIso j B).hom := by
  rw [← loopInto_eq]
  exact loopInto_reversal j f

end Topology.LoopPrespectrum.FiniteLoopWordSlide
