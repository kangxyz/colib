/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.Basic
public import Colib.CategoryTheory.Preadditive.AdditiveFunctorAbelian
public import Colib.CategoryTheory.Preadditive.CokernelAdditive
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Actual transfer-presheaf cokernels and section quotients

The native additive-functor cokernel is evaluated by its actual forgetful
functor and Mathlib evaluation. Sections are the ordinary group quotient by
the original coefficient-map image, with its canonical quotient map.

This generalizes the objectwise quotient argument in motivic_source_a6805c4,
`Motivic/Transfers/Presheaf/Contraction.lean: contractionSectionsIsoQuotient`.
No affine-line, Laurent cylinder, contraction or sheaf cokernel is constructed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- Evaluating the actual categorical cokernel gives the original section quotient. -/
@[colib_tag "COL-0380", colib_ref "motivic_source_a6805c4"
  "Motivic/Transfers/Presheaf/Contraction.lean:119-125"
  "adaptation" "General native transfer-presheaf cokernel, before any geometric contraction"]
def cokernelSectionsIsoQuotient {P Q : PresheafWithTransfers.{v} k}
    (η : P ⟶ Q) (X : Cor k) :
    sections (cokernel η) X ≅
      AddCommGrpCat.of (sections Q X ⧸ (η.hom.app (op X)).hom.range) :=
  PreservesCokernel.iso
      (forget ⋙ (evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X)) η ≪≫
    AddCommGrpCat.cokernelIsoQuotient (η.hom.app (op X))

/-- The comparison sends the categorical projection to the original quotient map. -/
@[reassoc (attr := simp)]
theorem cokernel_π_sectionsIsoQuotient_hom {P Q : PresheafWithTransfers.{v} k}
    (η : P ⟶ Q) (X : Cor k) :
    (cokernel.π η).hom.app (op X) ≫ (cokernelSectionsIsoQuotient η X).hom =
      AddCommGrpCat.ofHom (QuotientAddGroup.mk' (η.hom.app (op X)).hom.range) := by
  let E := forget ⋙ (evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X)
  change E.map (cokernel.π η) ≫
    ((PreservesCokernel.iso E η).hom ≫
      (AddCommGrpCat.cokernelIsoQuotient (η.hom.app (op X))).hom) = _
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

/-- Every native cokernel section has a representative in the target presheaf. -/
theorem cokernel_π_app_surjective {P Q : PresheafWithTransfers.{v} k}
    (η : P ⟶ Q) (X : Cor k) :
    Function.Surjective ((cokernel.π η).hom.app (op X)) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mp
  change Epi ((forget ⋙ (evaluation (Cor k)ᵒᵖ AddCommGrpCat).obj (op X)).map
    (cokernel.π η))
  infer_instance

/-- The quotient projection commutes with every actual signed correspondence. -/
@[reassoc]
theorem cokernel_π_transfer {P Q : PresheafWithTransfers.{v} k}
    (η : P ⟶ Q) {X Y : Cor k} (α : X ⟶ Y) :
    transfer Q α ≫ (cokernel.π η).hom.app (op X) =
      (cokernel.π η).hom.app (op Y) ≫ transfer (cokernel η) α :=
  transfer_naturality (cokernel.π η) α

attribute [colib_ref "MVW2006"
  "Lecture 2, Theorem 2.3, p. 13"
  "adaptation" "Objectwise cokernels in additive presheaves with transfers"]
  cokernelSectionsIsoQuotient

attribute [colib_tag "COL-0380"]
  cokernel_π_sectionsIsoQuotient_hom
  cokernel_π_app_surjective
  cokernel_π_transfer

end AlgebraicGeometry.PresheafWithTransfers
