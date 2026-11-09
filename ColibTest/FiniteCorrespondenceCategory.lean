module

import Colib.AlgebraicGeometry.Correspondences.Graph.Functor

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

variable (k : Type u) [Field k]

example : Category (Cor k) := inferInstance

example : Preadditive (Cor k) := inferInstance

example {X Y Z W : Cor k} (α : X ⟶ Y) (β : Y ⟶ Z) (γ : Z ⟶ W) :
    (α ≫ β) ≫ γ = α ≫ β ≫ γ := Category.assoc α β γ

example {X Y : Cor k} (α : X ⟶ Y) : 𝟙 X ≫ α = α := Category.id_comp α

example {X Y : Cor k} (α : X ⟶ Y) : α ≫ 𝟙 Y = α := Category.comp_id α

example {X Y Z : Cor k} (α α' : X ⟶ Y) (β : Y ⟶ Z) :
    (α + α') ≫ β = α ≫ β + α' ≫ β := Preadditive.add_comp _ _ _ _ _ _

example (X : Scheme.SmoothSite (Spec (.of k))) :
    (Cor.graphFunctor k).map (𝟙 X) = 𝟙 ((Cor.graphFunctor k).obj X) :=
  (Cor.graphFunctor k).map_id X

example {X Y Z : Scheme.SmoothSite (Spec (.of k))} (φ : X ⟶ Y) (ψ : Y ⟶ Z) :
    (Cor.graphFunctor k).map (φ ≫ ψ) =
      (Cor.graphFunctor k).map φ ≫ (Cor.graphFunctor k).map ψ :=
  (Cor.graphFunctor k).map_comp φ ψ
