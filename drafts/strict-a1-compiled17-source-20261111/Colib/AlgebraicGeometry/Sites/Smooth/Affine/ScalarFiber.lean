/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Affine.ScalarCoordinates
public import Colib.AlgebraicGeometry.Sites.Smooth.ScalarExtension.Finite.Basic

/-!
# The entire native scalar fibre in actual affine tensor coordinates

The canonical tensor-spectrum isomorphism preserves the original projection.
If all points over the original mark in the tensor coordinates equal y, then
every point of the native scalar fibre equals the inverse image of y. Thus
an open containing that point contains the entire fibre, not just one chosen
lift. This is the geometric retention step in motivic's
`exists_scalar_zero_open_of_affine_presentation`, separated from its
presentation-zero producer.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {k B L : Type u} [Field k] [CommRing B] [Field L]
  [Algebra k B] [Algebra.Smooth k B] [Algebra k L]
  [Module.Finite k L] [Algebra.IsSeparable k L]

local instance : Algebra.Smooth L (B ⊗[k] L) :=
  Algebra.Smooth.of_equiv (Algebra.TensorProduct.commRight k L B)

/-- Uniqueness in tensor coordinates identifies every point of the native scalar fibre. -/
theorem affineScalar_fiber_eq_of_unique
    (x : PrimeSpectrum B) (y : PrimeSpectrum (B ⊗[k] L))
    (hunique : ∀ z : PrimeSpectrum (B ⊗[k] L),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) z = x → z = y)
    (t : ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left)
    (ht : (finiteScalarProjection (E := L) (affineSite k B)).left t = x) :
    t = (affineScalarIso k B L).inv.left y := by
  let i := affineScalarIso k B L
  have hproj := congrArg (fun f => f t) (affineScalarIso_hom_original k B L)
  have hpoint : PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) (i.hom.left t) = x :=
    hproj.trans ht
  have h := congrArg (fun q => i.inv.left q) (hunique _ hpoint)
  have hid := congrArg (fun f => f.left t) i.hom_inv_id
  exact hid.symm.trans h

/-- A native open retaining the unique tensor point retains the full original scalar fibre. -/
theorem affineScalar_fiber_subset_of_unique
    (x : PrimeSpectrum B) (y : PrimeSpectrum (B ⊗[k] L))
    (hunique : ∀ z : PrimeSpectrum (B ⊗[k] L),
      PrimeSpectrum.comap (algebraMap B (B ⊗[k] L)) z = x → z = y)
    (V : ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left.Opens)
    (hy : (affineScalarIso k B L).inv.left y ∈ V) :
    (finiteScalarProjection (E := L) (affineSite k B)).left ⁻¹' {x} ⊆
      (V : Set ((fieldBaseChange (algebraMap k L)).obj (affineSite k B)).left) := by
  intro t ht
  rw [affineScalar_fiber_eq_of_unique x y hunique t ht]
  exact hy

end AlgebraicGeometry.Scheme.SmoothSite
