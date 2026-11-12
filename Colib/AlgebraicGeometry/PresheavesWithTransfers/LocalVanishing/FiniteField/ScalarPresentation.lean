/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarAffineZero
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteSeparableExtensionHI
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Presentation.OriginalOpen

/-!
# Scalar presentation zeros on whole-fibre neighborhoods

The presentation is used on its tensor-spectrum target. The resulting
zero open is transported to the native scalar base change and contains
the whole scalar fibre of the marked original point.

Adapted from `Motivic/Cohomology/A1/LocalVanishing/FiniteField/ScalarPresentationLocalZero.lean`
at `motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `cc9dd75aa49aae35207bb5f7c7c2e65cf51d6c70`.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.Scheme.RelativeCurve
open scoped TensorProduct

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {k B L : Type u} [Field k] [CommRing B] [Field L]
  [Algebra k B] [Algebra.Smooth k B] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local instance : Algebra.Smooth L (B ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)

/-- A scalar presentation gives a native zero open around a unique whole scalar fibre. -/
theorem exists_scalar_zero_open_of_affine_presentation
    {A : SmoothSite (Spec (.of k))}
    (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{v} k) (hP : P.IsA1Invariant)
    (s : sections P (Cor.mk (affineSite k B)))
    (hs : transfer P ((Cor.graphFunctor k).map a) s = 0)
    (x : PrimeSpectrum B) (y : PrimeSpectrum (B ⊗[k] L))
    (hunique : ∀ z : PrimeSpectrum (B ⊗[k] L),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) z = x → z = y)
    {Y Z : Scheme.{u}} (p : Y ⟶ (affineSite L (B ⊗[k] L)).left)
    (z : Z ⟶ (affineSite L (B ⊗[k] L)).left) [IsClosedImmersion z] (i : Z ⟶ Y)
    (e : OriginalEtalePresentation L (affineSite L (B ⊗[k] L)).hom p
      (pullback.snd a.left (Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L)))))
      z i y) :
    ∃ V : ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left.Opens,
      IsAffineOpen V ∧
      (finiteScalarProjection (E := L) (affineSite k B)).left ⁻¹' {x} ⊆
        (V : Set ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left) ∧
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (homMk (X := mk (V.ι ≫ ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).hom))
          (Y := (fieldBaseChange (algebraMap k L)).obj (affineSite k B)) V.ι rfl))
        (transfer P ((Cor.graphFunctor k).map
          (fieldBaseChangeForgetProjection (L := L) (affineSite k B))) s) = 0 := by
  let XS := affineSite L (B ⊗[k] L)
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L)))
  let AS := mk (pullback.snd a.left ρ ≫ XS.hom)
  let aS : AS ⟶ XS := homMk (pullback.snd a.left ρ) rfl
  have : IsAffine XS.left := inferInstanceAs (IsAffine (Spec (.of (B ⊗[k] L))))
  have : IsOpenImmersion aS.left := inferInstanceAs (IsOpenImmersion (pullback.snd a.left ρ))
  obtain ⟨O, hO, hy, hzero⟩ := e.exists_zero_on_original_open p aS z i y
    (finiteSeparableExtension L P) (finiteSeparableExtension_isA1Invariant L P hP)
    (affineScalarSection (L := L) P s)
    (affineScalarSection_restriction_eq_zero (L := L) a P s hs)
  exact exists_native_scalar_zero_open_of_affine_zero_open P s x y hunique O hO hy hzero

end AlgebraicGeometry.PresheafWithTransfers
