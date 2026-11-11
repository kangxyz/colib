/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Bass.GeneratedTensorTraceProof

/-! Left-generated finite tensor recipes, defined without invoking iterateFamily. -/
@[expose] public noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
open scoped Topology unitInterval
universe u v w
namespace KTheory.Bass.TensorGeneratedRecipe
open DiagramRowCell
variable {C : Type u} [Category.{v} C]
  (L : C ⥤ C) (c : 𝟭 C ⟶ L)
  (Q : C ⥤ Arrow (Arrow C)) (χ : L ⋙ Q ≅ Q ⋙ L.mapArrow.mapArrow)
  (hχ : ∀ X, Q.map (c.app X) ≫ χ.hom.app X =
    ((Functor.mapArrowFunctor (Arrow C) (Arrow C)).map
      ((Functor.mapArrowFunctor C C).map c)).app (Q.obj X))

variable (F : C ⥤ LoopPrespectrum.{w})
    (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
    (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
    (hn : ∀ {X Y} (g : X ⟶ Y) k x,
      q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
    (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
      q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
        (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
    (A : NaturalTrack.Track L c F) (D : Family L c F q hp hn hs A)

example (i : ℕ) :
    GeneratedTrace L c Q χ hχ i F q hp hn hs A D
      (iterateFamily L c Q χ hχ i F q hp hn hs A D).val :=
  iterateFamily_generated L c Q χ hχ i F q hp hn hs A D

example : GeneratedTrace L c Q χ hχ 0 F q hp hn hs A D D.val :=
  iterateFamily_generated L c Q χ hχ 0 F q hp hn hs A D

example : GeneratedTrace L c Q χ hχ 1 F q hp hn hs A D
    (iterateFamily L c Q χ hχ 1 F q hp hn hs A D).val :=
  iterateFamily_generated L c Q χ hχ 1 F q hp hn hs A D

example (i : ℕ) : GeneratedTrace L c Q χ hχ (i + 1) F q hp hn hs A D
    (iterateFamily L c Q χ hχ (i + 1) F q hp hn hs A D).val :=
  iterateFamily_generated L c Q χ hχ (i + 1) F q hp hn hs A D

example : GeneratorStep L c F q hp hn hs D.val D.property.1 Q χ
    (step L c F q hp hn hs D.val D.property.1 Q χ A D.property.2 hχ) :=
  step_generated L c F q hp hn hs D.val D.property.1 Q χ A D.property.2 hχ

end KTheory.Bass.TensorGeneratedRecipe
