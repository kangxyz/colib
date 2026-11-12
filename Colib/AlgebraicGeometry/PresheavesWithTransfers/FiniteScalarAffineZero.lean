/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.FiniteScalarLocalZero
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.IsoOpen
public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.ScalarFiber

/-!
# Actual affine scalar sections and whole-fibre zero-open transport

An original restricted zero is transported through the real scalar pullback
and the canonical tensor-spectrum isomorphism. Conversely, an actual affine
zero neighborhood in tensor coordinates transports to a native scalar zero
open containing the entire original fibre when that fibre has a unique point.

These are the independent coefficient and open-transport parts of motivic's
`ScalarPresentationLocalZero`, not a replacement for its geometric
presentation-zero theorem. The zero neighborhood remains an explicit input
of the transport result. Neither theorem below assumes HI, coefficient sheaf
separation, a supplied section iso or a supplied map-compatibility equation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme.SmoothSite
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

/-- The actual extended section, expressed in the canonical affine tensor coordinates. -/
def affineScalarSection (P : PresheafWithTransfers.{v} k)
    (s : sections P (Cor.mk (affineSite k B))) :
    sections (finiteSeparableExtension L P) (Cor.mk (affineSite L (B ⊗[k] L))) :=
  transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map (affineScalarIso k B L).inv)
    (transfer P ((Cor.graphFunctor k).map
      (fieldBaseChangeForgetProjection (L := L) (affineSite k B))) s)

/-- An original open restricted zero remains zero on its actual tensor-coordinate pullback. -/
theorem affineScalarSection_restriction_eq_zero
    {A : SmoothSite (Spec (.of k))} (a : A ⟶ affineSite k B) [IsOpenImmersion a.left]
    (P : PresheafWithTransfers.{v} k) (s : sections P (Cor.mk (affineSite k B)))
    (hs : transfer P ((Cor.graphFunctor k).map a) s = 0) :
    let ρ := Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L)))
    let XS := affineSite L (B ⊗[k] L)
    let AS := mk (pullback.snd a.left ρ ≫ XS.hom)
    transfer (finiteSeparableExtension L P) ((Cor.graphFunctor L).map
      (homMk (X := AS) (Y := XS) (pullback.snd a.left ρ) rfl))
      (affineScalarSection (L := L) P s) = 0 := by
  let F := fieldBaseChange (algebraMap k L)
  let Q := finiteSeparableExtension L P
  let XS := affineSite L (B ⊗[k] L)
  let i := affineScalarIso k B L
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap B (B ⊗[k] L)))
  let AS := mk (pullback.snd a.left ρ ≫ XS.hom)
  let aS : AS ⟶ XS := homMk (pullback.snd a.left ρ) rfl
  let H := affineScalarMap_isPullback k B L a
  have hc : H.isoPullback.inv ≫ (F.map a).left ≫ i.hom.left = pullback.snd a.left ρ := by
    simpa only [Category.assoc] using H.isoPullback_inv_snd
  let c : AS ⟶ F.obj A := homMk H.isoPullback.inv (by
    change H.isoPullback.inv ≫ (F.obj A).hom = pullback.snd a.left ρ ≫ XS.hom
    rw [← MorphismProperty.Over.w (F.map a), ← MorphismProperty.Over.w i.hom]
    simpa only [Category.assoc] using congrArg (fun f => f ≫ XS.hom) hc)
  have hca : c ≫ F.map a = aS ≫ i.inv := by
    apply (cancel_mono i.hom).mp
    apply MorphismProperty.Over.Hom.ext
    change (H.isoPullback.inv ≫ (F.map a).left) ≫ i.hom.left =
      (pullback.snd a.left ρ ≫ i.inv.left) ≫ i.hom.left
    have hi : i.inv.left ≫ i.hom.left = 𝟙 _ :=
      congrArg (fun f => f.left) i.inv_hom_id
    simp only [Category.assoc]
    erw [hi, Category.comp_id]
    simpa only [Category.assoc] using hc
  have h0 := native_scalar_restriction_eq_zero_of_restriction_eq_zero (L := L) P a s hs
  have ht := congrArg (transfer Q ((Cor.graphFunctor L).map c)) h0
  rw [map_zero] at ht
  rw [← ConcreteCategory.comp_apply, ← transfer_comp, ← Functor.map_comp,
    hca, Functor.map_comp, transfer_comp, ConcreteCategory.comp_apply] at ht
  exact ht

/-- An actual tensor-coordinate zero neighborhood gives a native full-fibre scalar zero open. -/
theorem exists_native_scalar_zero_open_of_affine_zero_open
    (P : PresheafWithTransfers.{v} k) (s : sections P (Cor.mk (affineSite k B)))
    (x : PrimeSpectrum B) (y : PrimeSpectrum (B ⊗[k] L))
    (hunique : ∀ z : PrimeSpectrum (B ⊗[k] L),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) z = x → z = y)
    (O : (affineSite L (B ⊗[k] L)).left.Opens) (hO : IsAffineOpen O) (hy : y ∈ O)
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
          (fieldBaseChangeForgetProjection (L := L) (affineSite k B))) s) = 0 := by
  let i := affineScalarIso k B L
  let sL := transfer P ((Cor.graphFunctor k).map
    (fieldBaseChangeForgetProjection (L := L) (affineSite k B))) s
  have hi : i.hom.left (i.inv.left y) = y :=
    congrArg (fun f => f.left y) i.inv_hom_id
  obtain ⟨V, hV, hyV, hzero⟩ := exists_affine_zero_open_of_iso
    (finiteSeparableExtension L P) i sL (i.inv.left y) O hO (by rwa [hi]) hz
  exact ⟨V, hV, affineScalar_fiber_subset_of_unique x y hunique V hyV, hzero⟩

end AlgebraicGeometry.PresheafWithTransfers
