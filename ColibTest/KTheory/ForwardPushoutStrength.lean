module
import Colib.KTheory.Bass.ForwardPushoutStrength
noncomputable section
open CategoryTheory Topology Topology.LoopPrespectrum
universe u v w
namespace KTheory.Bass.PushoutStrength
variable {C : Type u} [Category.{v} C]
  {F₀ F₁ F₂ : C ⥤ LoopPrespectrum.{w}} (f : F₀ ⟶ F₁) (g : F₀ ⟶ F₂)

variable (Q : C ⥤ Arrow (Arrow C))
example (X : C) :
    HomotopyPushout.inl (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) ≫ comparison f g Q X =
      (((strictDiagramFunctor Q).map (left f g)).app X) :=
  comparison_left f g Q X

example (X : C) :
    HomotopyPushout.inr (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) ≫ comparison f g Q X =
      (((strictDiagramFunctor Q).map (right f g)).app X) :=
  comparison_right f g Q X

example (X : C) (n : ℕ) (r : unitInterval)
    (x : (((strictDiagramFunctor Q).obj F₀).obj X).space n) :
    (comparison f g Q X).map n
      (HomotopyPushout.cylinder (((strictDiagramFunctor Q).map f).app X)
        (((strictDiagramFunctor Q).map g).app X) n (r, x)) =
      (strictDiagramMapHomotopy (glue f g) (glue_naturality f g) Q X).level n (r, x) :=
  comparison_overlap f g Q X n r x

example {X Y : C} (k : X ⟶ Y) :
    (pushout ((strictDiagramFunctor Q).map f) ((strictDiagramFunctor Q).map g)).map k ≫
        comparison f g Q Y =
      comparison f g Q X ≫ ((strictDiagramFunctor Q).obj (pushout f g)).map k :=
  comparison_naturality f g Q k

end KTheory.Bass.PushoutStrength
