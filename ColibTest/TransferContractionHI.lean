/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.SheavesWithTransfers.Contraction
import Colib.AlgebraicGeometry.PresheavesWithTransfers.RepresentableLarge
import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus

/-!
# Large-coefficient consumers of the actual HI contraction

Unconditional statements use the existing large signed representable and reduced
torus. HI consumers retain actual sheaves with transfers in universe `u + 1` and
all signed correspondences. No representable or reduced torus is asserted to be HI.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme AlgebraicGeometry.PresheafWithTransfers
open AlgebraicGeometry.Scheme.SmoothSite.Contraction

universe u

namespace TransferContractionHITest

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "T" => SmoothSite.multiplicativeGroupObject S

/-- The original coefficient model is compared at its actual projection. -/
example (P : PresheafWithTransfers.{u + 1} k) :
    IsA1Invariant P ↔ ∀ X : SmoothSite S,
      IsIso (transfer P ((Cor.graphFunctor k).map
        (SmoothSite.productFst X (polynomialAffineLine (.of k))))) :=
  isA1Invariant_iff_polynomial_projection P

/-- Every actual polynomial evaluation section is retained by the native comparison. -/
example (X : SmoothSite S) (a : k) :
    nativeAffineSection (.of k) X a ≫ (affineCylinderPolynomialIso (.of k) X).hom =
      polynomialAffineSection (.of k) X a :=
  nativeAffineSection_polynomialIso (.of k) X a

/-- The current large reduced torus receives a genuine transfer-natural unit splitting. -/
example (q : ℕ) :
    torusConstant (reducedTorus k q) ≫ torusUnit (reducedTorus k q) =
      𝟙 (baseSections (reducedTorus k q)) :=
  torusConstant_unit (reducedTorus k q)

/-- A negative signed representable cycle has its actual constant class killed. -/
example (Z X : Cor k)
    (β : Cor.mk (SmoothSite.product X.toSmoothSite (SmoothSite.base S)) ⟶ Z) :
    (toContraction ((representableLarge k).obj Z)).hom.app (op X)
      ((torusConstant ((representableLarge k).obj Z)).hom.app (op X) (ULift.up (-β))) = 0 := by
  have h := congrArg (fun η => η.hom.app (op X))
    (torusConstant_toContraction ((representableLarge k).obj Z))
  exact ConcreteCategory.congr_hom h (ULift.up (-β))

variable (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant)

/-- The source-only producer constructs the actual sheaf, with no sheafification replacement. -/
example : SheafWithTransfers.{u + 1} k := SheafWithTransfers.contraction F hF

example : (SheafWithTransfers.contraction F hF).obj = contraction F.obj := rfl

/-- The exact original polynomial-projection HI survives on the same sheaf. -/
example (X : SmoothSite S) :
    IsIso (transfer (SheafWithTransfers.contraction F hF).obj
      ((Cor.graphFunctor k).map (SmoothSite.productFst X (polynomialAffineLine (.of k))))) :=
  (isA1Invariant_iff_polynomial_projection _).mp
    (SheafWithTransfers.contraction_isA1Invariant F hF) X

/-- Forward on a representative is subtraction of precisely its genuine unit-constant value. -/
example (X : Cor k) (s : sections (torusSections F.obj) X) :
    (kernel.ι (torusUnit F.obj)).hom.app (op X)
      ((contractionIsoKernel F.obj hF).hom.hom.app (op X)
        ((toContraction F.obj).hom.app (op X) s)) =
      s - (torusConstant F.obj).hom.app (op X) ((torusUnit F.obj).hom.app (op X) s) := by
  have h := congrArg (fun η => η.hom.app (op X))
    (contractionIsoKernel_hom_projection F.obj hF)
  exact ConcreteCategory.congr_hom h s

/-- Inverse on a genuine kernel section is its inclusion followed by the original quotient. -/
example (X : Cor k) (s : sections (contractionKernel F.obj) X) :
    (contractionIsoKernel F.obj hF).inv.hom.app (op X) s =
      (toContraction F.obj).hom.app (op X)
        ((kernel.ι (torusUnit F.obj)).hom.app (op X) s) := rfl

/-- Kernel comparison commutes with negative, arbitrary signed finite correspondences. -/
example {X Y : Cor k} (α : X ⟶ Y) :
    transfer (contraction F.obj) (-α) ≫
      (contractionIsoKernel F.obj hF).hom.hom.app (op X) =
      (contractionIsoKernel F.obj hF).hom.hom.app (op Y) ≫
        transfer (contractionKernel F.obj) (-α) :=
  transfer_naturality (contractionIsoKernel F.obj hF).hom (-α)

/-- The actual quotient sheaf keeps the already constructed exterior transfer on classes. -/
example {X Y : Cor k} (α : X ⟶ Y) (s : sections (torusSections F.obj) Y) :
    transfer (SheafWithTransfers.contraction F hF).obj (-α)
        ((toContraction F.obj).hom.app (op Y) (-s)) =
      (toContraction F.obj).hom.app (op X)
        (transfer F.obj (Stacks.Chow.nativeExterior X.toSmoothSite Y.toSmoothSite T (-α))
          (-s)) :=
  contraction_transfer_apply F.obj (-α) (-s)

end TransferContractionHITest
