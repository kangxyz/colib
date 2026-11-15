/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Inclusion
public import StacksFrontier.CategoryTheory.Monoidal.TensorPow

/-! # Stable objects as tensor products with powers of the inverse twist -/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Stabilization

open MonoidalCategory BraidedCategory
open scoped MonoidalCategory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
variable (L : C) [(tensorRight L).Full] [(tensorRight L).Faithful]
variable (hL : (β_ L L).hom = 𝟙 _)

local notation "S" => Stabilization (tensorRight L)
local notation "T" => tensorRight L
local notation "K" => inclusion (tensorRight L)
local notation "R" => inverseTensorObject L

/-- The inverse twist power has numerator isomorphic to the unit and the given denominator. -/
def inverseTensorPowerIso (n : ℕ) :
    letI := monoidalCategory L hL
    tensorPow R n ≅ (atLevel T n).obj (𝟙_ C) := by
  letI := monoidalCategory L hL
  induction n with
  | zero => exact Iso.refl _
  | succ n ih =>
    exact (ih ⊗ᵢ Iso.refl R) ≪≫
      numeratorIso L
        (show (((atLevel T n).obj (𝟙_ C)) ⊗ R).level =
          ((atLevel T (n + 1)).obj (𝟙_ C)).level from rfl)
        (ρ_ (𝟙_ C))

/-- Every stable object is the tensor of its included numerator and an inverse twist power. -/
def inverseTensorPowerPresentation (X : S) :
    letI := monoidalCategory L hL
    X ≅ (K).obj X.obj ⊗ tensorPow R X.level := by
  letI := monoidalCategory L hL
  obtain ⟨A, n⟩ := X
  refine ?_ ≪≫ (Iso.refl ((K).obj A) ⊗ᵢ (inverseTensorPowerIso L hL n).symm)
  exact (numeratorIso L
    (show (((K).obj A) ⊗ (atLevel T n).obj (𝟙_ C)).level = (⟨A, n⟩ : S).level from
      Nat.zero_add n) (ρ_ A)).symm

/-- Essential-surjectivity premise for the symmetric monoidal inversion property. -/
lemma inverseTensorPower_essSurj (X : S) :
    letI := monoidalCategory L hL
    ∃ (A : C) (n : ℕ), Nonempty (X ≅ (K).obj A ⊗ tensorPow R n) :=
  letI := monoidalCategory L hL
  ⟨X.obj, X.level, ⟨inverseTensorPowerPresentation L hL X⟩⟩

/-- The chosen inverse twist has trivial self-braiding. -/
lemma inverseTensorObject_braiding :
    letI := monoidalCategory L hL
    letI := symmetricCategory L hL
    (β_ R R).hom = 𝟙 _ := by
  let := monoidalCategory L hL
  let := symmetricCategory L hL
  have hb : (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 _ := by
    apply (cancel_mono (λ_ (𝟙_ C)).hom).mp
    rw [braiding_leftUnitor, Category.id_comp]
    monoidal
  have h : (tensorObj L R R).level = (tensorObj L R R).level := rfl
  let b : (tensorObj L R R).obj ⟶ (tensorObj L R R).obj := (β_ (𝟙_ C) (𝟙_ C)).hom
  change numeratorHom L h b = 𝟙 (tensorObj L R R)
  have hb' : b = 𝟙 (tensorObj L R R).obj := hb
  rw [hb']
  exact numeratorHom_id L (tensorObj L R R)

end CategoryTheory.Stabilization
