/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Prespectrum.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Yoneda

/-!
# Adjoint bonding maps of sequential prespectra

Transpose each bonding map through the specified suspension adjunction.
The resulting maps describe the same morphism squares and define the
full subcategory of Ω-spectra.
-/

@[expose] public section

universe v u

namespace CategoryTheory.SequentialPrespectrum

variable {C : Type u} [Category.{v} C] {S R : C ⥤ C} (adj : S ⊣ R)

/-- The adjoint of the original bonding map in degree `n`. -/
def adjointBonding (X : SequentialPrespectrum S) (n : ℕ) :
    X.level n ⟶ R.obj (X.level (n + 1)) :=
  adj.homEquiv _ _ (X.bonding n)

/-- Compatibility of maps with the bonding maps is equivalent to
compatibility with their actual transposes. -/
theorem comm_iff_adjointBonding {X Y : SequentialPrespectrum S}
    (f : ∀ n, X.level n ⟶ Y.level n) (n : ℕ) :
    X.bonding n ≫ f (n + 1) = S.map (f n) ≫ Y.bonding n ↔
      adjointBonding adj X n ≫ R.map (f (n + 1)) =
        f n ≫ adjointBonding adj Y n := by
  let e := adj.homEquiv (X.level n) (Y.level (n + 1))
  have h₁ : e (X.bonding n ≫ f (n + 1)) =
      adjointBonding adj X n ≫ R.map (f (n + 1)) :=
    adj.homEquiv_naturality_right (X.bonding n) (f (n + 1))
  have h₂ : e (S.map (f n) ≫ Y.bonding n) =
      f n ≫ adjointBonding adj Y n :=
    adj.homEquiv_naturality_left (f n) (Y.bonding n)
  rw [← h₁, ← h₂]
  exact ⟨congrArg e, fun h ↦ e.injective h⟩

/-- The adjoint bonding maps are natural in the prespectrum. -/
@[reassoc]
theorem adjointBonding_naturality {X Y : SequentialPrespectrum S} (f : X ⟶ Y) (n : ℕ) :
    adjointBonding adj X n ≫ R.map (f.app (n + 1)) =
      f.app n ≫ adjointBonding adj Y n :=
  (comm_iff_adjointBonding adj f.app n).1 (f.comm n)

/-- Transposing the bonding maps gives a map from each evaluation functor
to the right adjoint applied to the next evaluation. -/
@[simps]
def adjointBondingNatTrans (n : ℕ) :
    evaluation (S := S) n ⟶ evaluation (S := S) (n + 1) ⋙ R where
  app X := adjointBonding adj X n
  naturality _ _ f := (adjointBonding_naturality adj f n).symm

/-- A prespectrum has the Ω-spectrum property if every adjoint bonding map
is invertible in the chosen category. -/
def IsOmegaSpectrum : ObjectProperty (SequentialPrespectrum S) :=
  fun X ↦ ∀ n, IsIso (adjointBonding adj X n)

/-- Test the actual adjoint bonding maps through the original suspension
adjunction. The test is precomposition with the suspension of a map into
the given level followed by the original bonding map. -/
theorem isOmegaSpectrum_iff_bijective_bonding (Y : SequentialPrespectrum S) :
    IsOmegaSpectrum adj Y ↔
      ∀ (n : ℕ) (X : C), Function.Bijective
        (fun f : X ⟶ Y.level n ↦ S.map f ≫ Y.bonding n) := by
  change (∀ n, IsIso (adjointBonding adj Y n)) ↔ _
  apply forall_congr' fun n ↦ ?_
  rw [isIso_iff_yoneda_map_bijective]
  apply forall_congr' fun X ↦ ?_
  let e := adj.homEquiv X (Y.level (n + 1))
  have h : (fun f : X ⟶ Y.level n ↦ f ≫ adjointBonding adj Y n) =
      e ∘ (fun f : X ⟶ Y.level n ↦ S.map f ≫ Y.bonding n) := by
    funext f
    exact (adj.homEquiv_naturality_left f (Y.bonding n)).symm
  rw [h]
  exact Function.Bijective.of_comp_iff' e.bijective _

/-- The Ω-spectrum condition is invariant under prespectrum isomorphism. -/
theorem isOmegaSpectrum_iff_of_iso {X Y : SequentialPrespectrum S} (e : X ≅ Y) :
    IsOmegaSpectrum adj X ↔ IsOmegaSpectrum adj Y := by
  change (∀ n, IsIso (adjointBonding adj X n)) ↔ ∀ n, IsIso (adjointBonding adj Y n)
  exact forall_congr' fun n ↦
    (adjointBondingNatTrans adj n).isIso_app_iff_of_iso e

/-- The full subcategory whose objects satisfy the Ω-spectrum property
for the specified adjunction. -/
abbrev OmegaSpectrum := (IsOmegaSpectrum adj).FullSubcategory

end CategoryTheory.SequentialPrespectrum
