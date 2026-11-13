/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Prespectrum.AdjointBonding
public import Colib.CategoryTheory.Prespectrum.Free
public import Mathlib.CategoryTheory.Localization.Bousfield
import Colib.Util.References
import Mathlib.CategoryTheory.Yoneda

/-!
# Locality for the free prespectrum comparisons

The adjoint bonding maps are isomorphisms precisely when precomposition
by every free prespectrum comparison induces a bijection. This is the
Hom calculation underlying stabilization at these comparisons.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory.SequentialPrespectrum

variable {C : Type u} [Category.{v} C] {S R : C ⥤ C} (adj : S ⊣ R)
  [HasInitial C] [PreservesColimit (Functor.empty.{0} C) S]

/-- Precomposition with the actual free comparison transposes to
postcomposition with the adjoint bonding map. -/
theorem bijective_precomp_freeAtSuccComparison_iff
    (Y : SequentialPrespectrum S) (n : ℕ) (X : C) :
    Function.Bijective
      (fun f : (freeAt (S := S) n).obj X ⟶ Y ↦ freeAtSuccComparison n X ≫ f) ↔
    Function.Bijective (fun f : X ⟶ Y.level n ↦ f ≫ adjointBonding adj Y n) := by
  let a := (freeAtAdjunction (S := S) n).homEquiv X Y
  let b := ((freeAtAdjunction (S := S) (n + 1)).homEquiv (S.obj X) Y).trans
    (adj.homEquiv X (Y.level (n + 1)))
  let p := fun f : (freeAt (S := S) n).obj X ⟶ Y ↦ freeAtSuccComparison n X ≫ f
  let q := fun f : X ⟶ Y.level n ↦ f ≫ adjointBonding adj Y n
  have h : b ∘ p = q ∘ a := by
    funext f
    change adj.homEquiv X (Y.level (n + 1))
      ((freeAtAdjunction (S := S) (n + 1)).homEquiv (S.obj X) Y
        (freeAtSuccComparison n X ≫ f)) = q (a f)
    rw [freeAtAdjunction_homEquiv_comparison]
    exact adj.homEquiv_naturality_left (a f) (Y.bonding n)
  change Function.Bijective p ↔ Function.Bijective q
  calc
    Function.Bijective p ↔ Function.Bijective (b ∘ p) :=
      (Function.Bijective.of_comp_iff' b.bijective p).symm
    _ ↔ Function.Bijective (q ∘ a) := by rw [h]
    _ ↔ Function.Bijective q := Function.Bijective.of_comp_iff q a.bijective

/-- A prespectrum is an Ω-spectrum exactly when all the actual free
prespectrum comparisons induce bijections into it. -/
@[colib_tag "COL-1116",
  colib_ref "Hovey2001Spectra" "Section 1, Definition 1.2" "ingredient"
    "Free prespectra and evaluation in a specified degree",
  colib_ref "Hovey2001Spectra" "Section 3, Definition 3.3 and Theorem 3.4" "adaptation"
    "The ordinary Hom criterion obtained from the free comparison and the adjoint bonding map"]
theorem isOmegaSpectrum_iff_bijective_precomp_freeAtSuccComparison
    (Y : SequentialPrespectrum S) :
    IsOmegaSpectrum adj Y ↔
      ∀ (n : ℕ) (X : C), Function.Bijective
        (fun f : (freeAt (S := S) n).obj X ⟶ Y ↦ freeAtSuccComparison n X ≫ f) := by
  constructor
  · intro h n X
    have hₙ : IsIso (adjointBonding adj Y n) := h n
    apply (bijective_precomp_freeAtSuccComparison_iff adj Y n X).2
    exact (isIso_iff_yoneda_map_bijective _).1 hₙ X
  · intro h n
    apply isIso_of_yoneda_map_bijective
    intro X
    exact (bijective_precomp_freeAtSuccComparison_iff adj Y n X).1 (h n X)

/-- The actual free comparison is detected as an equivalence by every
Ω-spectrum. This is a Hom test in the category of sequential prespectra. -/
theorem isLocal_freeAtSuccComparison (n : ℕ) (X : C) :
    ObjectProperty.isLocal (IsOmegaSpectrum adj) (freeAtSuccComparison (S := S) n X) := by
  intro Y hY
  exact (isOmegaSpectrum_iff_bijective_precomp_freeAtSuccComparison adj Y).1 hY n X

end CategoryTheory.SequentialPrespectrum

attribute [colib_tag "COL-1116"]
  CategoryTheory.SequentialPrespectrum.freeAtAdjunction
  CategoryTheory.SequentialPrespectrum.freeAtSuccComparison
