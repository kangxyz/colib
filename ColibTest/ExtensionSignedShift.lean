/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Homology.Embedding.SignedShift

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Preadditive A] [HasZeroObject A]

example (K : ChainComplex A ℕ) (q : ℕ) :
    K.extend (ComplexShape.embeddingUpIntLE (q : ℤ)) ≅
      (K.extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧ :=
  HomologicalComplex.ExtensionSignedShift.iso K q

example (K : ChainComplex A ℕ) (q r : ℕ) :
    (HomologicalComplex.ExtensionSignedShift.iso K q).hom.f ((q : ℤ) - r) =
      ((q : ℤ) * r).negOnePow •
        ((K.extendXIso (ComplexShape.embeddingUpIntLE (q : ℤ))
          (i' := (q : ℤ) - r) (ComplexShape.embeddingUpIntLE_f (q : ℤ) r)).hom ≫
          (HomologicalComplex.ExtensionSignedShift.shiftedXIso K q r rfl).inv) :=
  HomologicalComplex.ExtensionSignedShift.iso_hom_f K q r

example {K L : ChainComplex A ℕ} (φ : K ⟶ L) (q : ℕ) :
    HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntLE (q : ℤ)) ≫
        (HomologicalComplex.ExtensionSignedShift.iso L q).hom =
      (HomologicalComplex.ExtensionSignedShift.iso K q).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-(q : ℤ))).map
          (HomologicalComplex.extendMap φ (ComplexShape.embeddingUpIntLE 0)) :=
  HomologicalComplex.ExtensionSignedShift.iso_naturality φ q

example (K : ChainComplex A ℕ) (q : ℕ) (i : ℤ) (hi : (q : ℤ) < i) :
    IsZero (((K.extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).X i) :=
  HomologicalComplex.ExtensionSignedShift.isZero_shifted_X K q i hi

example (K : ChainComplex A ℕ) (q r s : ℕ) :
    ((K.extend (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).d
        ((q : ℤ) - r) ((q : ℤ) - s) =
      (-(q : ℤ)).negOnePow •
        ((HomologicalComplex.ExtensionSignedShift.shiftedXIso K q r rfl).hom ≫
          K.d r s ≫ (HomologicalComplex.ExtensionSignedShift.shiftedXIso K q s rfl).inv) :=
  HomologicalComplex.ExtensionSignedShift.shifted_d K q r s
