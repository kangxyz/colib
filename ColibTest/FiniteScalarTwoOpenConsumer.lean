/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarAffineZero

/-!
A source-only consumer connecting two actual tensor-coordinate zero opens to
an original affine zero neighborhood. It does not produce the tensor zeros
or their unique fibres from presentation geometry.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers
open scoped TensorProduct

universe v u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {k B E L : Type u} [Field k] [CommRing B] [Field E] [Field L]
  [Algebra k B] [Algebra.Smooth k B]
  [Algebra k E] [Module.Finite k E] [Algebra.IsSeparable k E]
  [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L]

local instance : Algebra.Smooth E (B ⊗[k] E) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k E B)

local instance : Algebra.Smooth L (B ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)

example (P : PresheafWithTransfers.{v} k) (s : sections P (Cor.mk (affineSite k B)))
    (x : PrimeSpectrum B) (yE : PrimeSpectrum (B ⊗[k] E)) (yL : PrimeSpectrum (B ⊗[k] L))
    (huE : ∀ z : PrimeSpectrum (B ⊗[k] E),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] E)) z = x → z = yE)
    (huL : ∀ z : PrimeSpectrum (B ⊗[k] L),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) z = x → z = yL)
    (OE : (Spec (.of (B ⊗[k] E))).Opens) (hOE : IsAffineOpen OE) (hyE : yE ∈ OE)
    (OL : (Spec (.of (B ⊗[k] L))).Opens) (hOL : IsAffineOpen OL) (hyL : yL ∈ OL)
    (hzE : transfer (finiteSeparableExtension E P) ((Cor.graphFunctor E).map
        (homMk (X := mk (OE.ι ≫ (affineSite E (B ⊗[k] E)).hom))
          (Y := affineSite E (B ⊗[k] E)) OE.ι rfl)) (affineScalarSection (L := E) P s) = 0)
    (hzL : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (homMk (X := mk (OL.ι ≫ (affineSite L (B ⊗[k] L)).hom))
          (Y := affineSite L (B ⊗[k] L)) OL.ι rfl)) (affineScalarSection (L := L) P s) = 0)
    (hd : (Module.finrank k E).Coprime (Module.finrank k L)) :
    ∃ U : (Spec (.of B)).Opens, IsAffineOpen U ∧ x ∈ U ∧
      transfer P ((Cor.graphFunctor k).map
        (homMk (X := mk (U.ι ≫ (affineSite k B).hom)) (Y := affineSite k B) U.ι rfl)) s = 0 := by
  obtain ⟨V, _, hV, zV⟩ :=
    exists_native_scalar_zero_open_of_affine_zero_open P s x yE huE OE hOE hyE hzE
  obtain ⟨W, _, hW, zW⟩ :=
    exists_native_scalar_zero_open_of_affine_zero_open P s x yL huL OL hOL hyL hzL
  exact exists_affine_zero_open_of_coprime_scalar_zero_opens
    P (affineSite k B) s x V W hV hW zV zW hd
