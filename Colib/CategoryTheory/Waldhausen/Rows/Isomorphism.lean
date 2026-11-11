/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.CategoryTheory.Waldhausen.Rows.Basic
public import Colib.Util.References
public import Colib.CategoryTheory.Waldhausen.ExactFunctorIso

/-!
# Transport of actual quotient rows through diagram isomorphisms

An isomorphism of the entire underlying interval diagrams transports the original zero objects,
cofibrations and quotient pushouts. This allows an independently constructed row to be lifted
only after its actual row conditions have been proved.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace CategoryTheory.Waldhausen.QuotientRows
variable {C : Type u} [Category.{v} C] (W : Structure C)

/-- A whole diagram isomorphism transports all original quotient-row conditions. -/
@[colib_ref "quillen" "Quillen c561118b: Rows/Isomorphism.lean:26"
  "adaptation" "Original tensor-zero objects and unchanged whole quotient-row proof."]
theorem IsRow.of_iso {n : SimplexCategory} {F G : Interval n ⥤ C}
    (hF : IsRow W F) (e : F ≅ G) : IsRow W G where
  zero i := (hF.zero i).of_iso (e.app _).symm
  cofibration i j k hij hjk :=
    (W.cof.arrow_mk_iso_iff
      (Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality _).symm)).mp
        (hF.cofibration i j k hij hjk)
  quotient i j k hij hjk :=
    (hF.quotient i j k hij hjk).of_iso (e.app _) (e.app _) (e.app _) (e.app _)
      (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _) (e.hom.naturality _)

end CategoryTheory.Waldhausen.QuotientRows
