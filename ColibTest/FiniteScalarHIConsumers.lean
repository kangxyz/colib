/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteSeparableExtensionHI
import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarAffineZero

/-! Source-only consumers. None of these examples has been run by the source owner. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.SmoothSite
open AlgebraicGeometry.PresheafWithTransfers
open scoped TensorProduct

universe v u

section AnyBase

variable {S T : Scheme.{u}} (r : T ⟶ S)

example : additiveGroupBaseChangeMap r ≫ (additiveGroupObject S).hom =
    (additiveGroupObject T).hom ≫ r := additiveGroupBaseChangeMap_over r

example : IsPullback (additiveGroupObject T).hom
    (additiveGroupBaseChangeMap r) r (additiveGroupObject S).hom :=
  additiveGroupBaseChangeMap_isPullback r

end AnyBase

section FiniteSeparableHI

variable {k : Type u} (L : Type u) [Field k] [Field L] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]
  (P : PresheafWithTransfers.{v} k)

example (X : SmoothSite (Spec (.of L))) :
    (finiteSeparableForgetBase k L).obj (product X (additiveGroupObject (Spec (.of L)))) ≅
      product ((finiteSeparableForgetBase k L).obj X) (additiveGroupObject (Spec (.of k))) :=
  finiteSeparableForgetBaseA1Iso k L X

example (X : SmoothSite (Spec (.of L))) :
    (finiteSeparableForgetBaseA1Iso k L X).hom ≫
      productFst ((finiteSeparableForgetBase k L).obj X) (additiveGroupObject (Spec (.of k))) =
    (finiteSeparableForgetBase k L).map (productFst X (additiveGroupObject (Spec (.of L)))) :=
  finiteSeparableForgetBaseA1Iso_hom_projection k L X

example (X : SmoothSite (Spec (.of L))) :
    A1.projectionPullback (.of L) ((toPresheaf L).obj (finiteSeparableExtension L P)) X =
      A1.projectionPullback (.of k) ((toPresheaf k).obj P)
        ((finiteSeparableForgetBase k L).obj X) ≫
          ((toPresheaf k).obj P).map (finiteSeparableForgetBaseA1Iso k L X).hom.op :=
  finiteSeparableExtension_projection L P X

example (hP : P.IsA1Invariant) : (finiteSeparableExtension L P).IsA1Invariant :=
  finiteSeparableExtension_isA1Invariant L P hP

-- This has no trace, Cartesian trace, fibre-specialization, or strict-invariance premise.
example (hP : P.IsA1Invariant) (X : SmoothSite (Spec (.of L))) :
    IsIso (A1.projectionPullback (.of L)
      ((toPresheaf L).obj (finiteSeparableExtension L P)) X) :=
  finiteSeparableExtension_isA1Invariant L P hP X

end FiniteSeparableHI

section AffineFiber

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {k B L : Type u} [Field k] [CommRing B] [Field L]
  [Algebra k B] [Algebra.Smooth k B] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local instance : Algebra.Smooth L (B ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)

example (x : PrimeSpectrum B) (y : PrimeSpectrum (B ⊗[k] L))
    (hunique : ∀ z : PrimeSpectrum (B ⊗[k] L),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) z = x → z = y)
    (t : ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left)
    (ht : (finiteScalarProjection (E := L) (affineSite k B)).left t = x) :
    t = (affineScalarIso k B L).inv.left y :=
  affineScalar_fiber_eq_of_unique x y hunique t ht

example (x : PrimeSpectrum B) (y : PrimeSpectrum (B ⊗[k] L))
    (hunique : ∀ z : PrimeSpectrum (B ⊗[k] L),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) z = x → z = y)
    (V : ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left.Opens)
    (hy : (affineScalarIso k B L).inv.left y ∈ V) :
    (finiteScalarProjection (E := L) (affineSite k B)).left ⁻¹' {x} ⊆
      (V : Set ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left) :=
  affineScalar_fiber_subset_of_unique x y hunique V hy


example
    {A : SmoothSite (Spec (.of k))} (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{v} k) (s : sections P (Cor.mk (affineSite k B)))
    (hs : transfer P ((Cor.graphFunctor k).map a) s = 0) :
    let ρ := Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L)))
    let XS := affineSite L (B ⊗[k] L)
    let AS := mk (pullback.snd a.left ρ ≫ XS.hom)
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
      (homMk (X := AS) (Y := XS) (pullback.snd a.left ρ) rfl))
      (affineScalarSection (L := L) P s) = 0 :=
  affineScalarSection_restriction_eq_zero a P s hs

example
    (P : PresheafWithTransfers.{v} k) (s : sections P (Cor.mk (affineSite k B)))
    (x : PrimeSpectrum B) (y : PrimeSpectrum (B ⊗[k] L))
    (hunique : ∀ z : PrimeSpectrum (B ⊗[k] L),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) z = x → z = y)
    (O : (Spec (.of (B ⊗[k] L))).Opens) (hO : IsAffineOpen O) (hy : y ∈ O)
    (hz : transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (homMk (X := mk (O.ι ≫ (affineSite L (B ⊗[k] L)).hom))
          (Y := affineSite L (B ⊗[k] L)) O.ι rfl)) (affineScalarSection (L := L) P s) = 0) :
    ∃ V : ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left.Opens,
      IsAffineOpen V ∧
      (finiteScalarProjection (E := L) (affineSite k B)).left ⁻¹' {x} ⊆
        (V : Set ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left) ∧
      transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
        (homMk (X := mk (V.ι ≫ ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).hom))
          (Y := (fieldBaseChange (algebraMap k L)).obj (affineSite k B)) V.ι rfl))
        (transfer P ((Cor.graphFunctor k).map
          (fieldBaseChangeForgetProjection (L := L) (affineSite k B))) s) = 0 :=
  exists_native_scalar_zero_open_of_affine_zero_open P s x y hunique O hO hy hz

end AffineFiber
