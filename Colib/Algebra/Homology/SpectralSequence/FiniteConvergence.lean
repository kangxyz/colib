/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Mathlib.Algebra.Homology.SpectralObject.Page
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Images and finite convergence of spectral objects

The canonical factorization through a page term of a spectral object is an
epi-mono factorization of the map between the two larger windows. For a finite
filtration this map can then be compared with the associated graded piece.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

variable {C ι : Type*} [Category* C] [Abelian C] [Category* ι]
  (X : SpectralObject C ι)
  {i₀ i₁ i₂ i₃ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₁₂ : i₀ ⟶ i₂) (f₂₃ : i₁ ⟶ i₃) (h₁₂ : f₁ ≫ f₂ = f₁₂) (h₂₃ : f₂ ≫ f₃ = f₂₃)

/-- The diagonal map between the two windows defining a page term. -/
abbrev pageWindowMorphism : mk₁ f₁₂ ⟶ mk₁ f₂₃ :=
  twoδ₁Toδ₀ f₁ f₂ f₁₂ h₁₂ ≫ twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃

variable (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂)

/-- The canonical maps into and out of a page term factor the diagonal window map. -/
@[reassoc]
lemma toCycles_πE_comp_ιE_fromOpcycles :
    (X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) ≫
      (X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁) =
    (X.H n₁).map (pageWindowMorphism f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃) := by
  simp only [Category.assoc, πE_ιE_assoc, toCycles_i_assoc, p_fromOpcycles, pageWindowMorphism,
    Functor.map_comp]

/-- A page term of a spectral object is canonically the image of its diagonal window map. -/
def pageImageIso : X.E f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≅
    image ((X.H n₁).map (pageWindowMorphism f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃)) := by
  letI : StrongEpi (X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) :=
    strongEpi_of_epi _
  exact image.isoStrongEpiMono _ _
    (X.toCycles_πE_comp_ιE_fromOpcycles f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

/-- The image comparison preserves the canonical inclusion into the target window. -/
@[reassoc (attr := simp)]
lemma pageImageIso_hom_comp_image_ι :
    (X.pageImageIso f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂).hom ≫
      Limits.image.ι ((X.H n₁).map (pageWindowMorphism f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃)) =
        X.ιE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂ ≫ X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₁ := by
  have : StrongEpi (X.toCycles f₁ f₂ f₁₂ h₁₂ n₁ ≫ X.πE f₁ f₂ f₃ n₀ n₁ n₂ hn₁ hn₂) :=
    strongEpi_of_epi _
  exact image.isoStrongEpiMono_hom_comp_ι _ _
    (X.toCycles_πE_comp_ιE_fromOpcycles f₁ f₂ f₃ f₁₂ f₂₃ h₁₂ h₂₃ n₀ n₁ n₂ hn₁ hn₂)

end CategoryTheory.Abelian.SpectralObject

namespace CategoryTheory.Subobject

variable {C : Type*} [Category* C] [Abelian C]

/-- For nested subobjects `V ≤ U` of `B`, `U/V` identifies with the image of `U → B/V`. -/
def cokernelOfLEIsoImage {B : C} {U V : Subobject B} (h : V ≤ U) :
    cokernel (ofLE V U h) ≅ image (U.arrow ≫ cokernel.π V.arrow) := by
  let S := ShortComplex.mk (ofLE V U h) (U.arrow ≫ cokernel.π V.arrow) (by simp)
  let lift {A : C} (u : A ⟶ S.X₂) (hu : u ≫ S.g = 0) : A ⟶ S.X₁ :=
    Abelian.monoLift V.arrow (u ≫ U.arrow) (by simpa [S] using hu)
  have hS : S.Exact := by
    refine ShortComplex.exact_of_f_is_kernel S (KernelFork.IsLimit.ofι _ _ lift ?_ ?_)
    · intro A u hu
      apply (cancel_mono U.arrow).1
      change (lift u hu ≫ ofLE V U h) ≫ U.arrow = u ≫ U.arrow
      simp only [Category.assoc, ofLE_arrow, lift, Abelian.monoLift_comp]
    · intro A u hu m hm
      apply (cancel_mono V.arrow).1
      calc
        m ≫ V.arrow = (m ≫ S.f) ≫ U.arrow := by simp [S]
        _ = u ≫ U.arrow := by rw [hm]
        _ = lift u hu ≫ V.arrow := (Abelian.monoLift_comp _ _ _).symm
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS.isColimitImage

end CategoryTheory.Subobject
