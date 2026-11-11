/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Colib.Topology.Prespectrum.TelescopeDiagramMap
noncomputable section
open CategoryTheory Topology
universe u v w
namespace Topology.LoopPrespectrum.Telescope
variable {C : Type u} [Category.{v} C]
    (F G : ℕ → C ⥤ LoopPrespectrum.{w})
    (τ : ∀ i, F i ⟶ F (i + 1)) (σ : ∀ i, G i ⟶ G (i + 1))
    (a : ∀ i, F i ⟶ G i) (h : ∀ i, a i ≫ σ i = τ i ≫ a (i + 1))

example : diagramFunctor F τ ⟶ diagramFunctor G σ := diagramMap F G τ σ a h

example (X : C) (k i : ℕ) (s : unitInterval)
    (x : ((F i).obj X).space k) :
    ((diagramMap F G τ σ a h).app X).map k
        (cylinder (fun j ↦ (F j).obj X) (fun j ↦ (τ j).app X) k i (s, x)) =
      cylinder (fun j ↦ (G j).obj X) (fun j ↦ (σ j).app X) k i
        (s, ((a i).app X).map k x) :=
  diagramMap_cylinder F G τ σ a h X k i s x

example (i : ℕ) :
    diagramInclusion F τ i ≫ diagramMap F G τ σ a h = a i ≫ diagramInclusion G σ i :=
  diagramInclusion_diagramMap F G τ σ a h i

end Topology.LoopPrespectrum.Telescope
end
