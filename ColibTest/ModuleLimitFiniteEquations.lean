module

import Colib.AlgebraicGeometry.Modules.Limits.FiniteEquations

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.AlgebraicGeometry.ModuleLimits

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] (c : Cone D) (hc : IsLimit c)
  (i : I) [CompactSpace (D.obj i)]

-- The two equations use one transition, including when their module sources differ.
example (F G : Fin 2 → (D.obj i).Modules)
    [∀ a, (F a).IsFinitePresentation] [∀ a, (G a).IsFinitePresentation]
    (f g : ∀ a, F a ⟶ G a)
    (h : ∀ a, (Scheme.Modules.pullback (c.π.app i)).map (f a) =
      (Scheme.Modules.pullback (c.π.app i)).map (g a)) :
    ∃ (j : I) (e : j ⟶ i),
      ((Scheme.Modules.pullback (D.map e)).map (f 0) =
        (Scheme.Modules.pullback (D.map e)).map (g 0)) ∧
      ((Scheme.Modules.pullback (D.map e)).map (f 1) =
        (Scheme.Modules.pullback (D.map e)).map (g 1)) := by
  obtain ⟨j, e, he⟩ := exists_pullback_map_eq_of_isLimit_finite D c hc i F G f g h
  exact ⟨j, e, he 0, he 1⟩

-- Empty families do not introduce a nonemptiness assumption on the equation index.
example (F G : Empty → (D.obj i).Modules)
    [∀ a, (F a).IsFinitePresentation] [∀ a, (G a).IsFinitePresentation]
    (f g : ∀ a, F a ⟶ G a) :
    ∃ (j : I) (e : j ⟶ i), ∀ a,
      (Scheme.Modules.pullback (D.map e)).map (f a) =
        (Scheme.Modules.pullback (D.map e)).map (g a) :=
  exists_pullback_map_eq_of_isLimit_finite D c hc i F G f g (fun a => nomatch a)
