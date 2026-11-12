/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.AlgebraicGeometry.Modules.UnitEndScalar

/-!
# A frame is determined by its value on one normalized section

If either frame sends a global section to one, that section generates the module.
Equality of the two normalized values therefore determines the entire frame on the
original scheme, including nilpotents. No reducedness or geometric hypotheses are needed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

/-- Two frames sending the same global section to one are the same isomorphism. -/
theorem frame_eq_of_same_section_one {X : Scheme.{u}} {M : X.Modules}
    (e e' : M ≅ SheafOfModules.unit X.ringCatSheaf) (s : Γ(M, ⊤))
    (hs : Hom.app e.hom ⊤ s = (1 : Γ(X, ⊤)))
    (hs' : Hom.app e'.hom ⊤ s = (1 : Γ(X, ⊤))) : e = e' := by
  have hinv : Hom.app e.inv ⊤ (1 : Γ(X, ⊤)) = s := by
    rw [← hs]
    exact congrArg (fun θ : M ⟶ M => Hom.app θ ⊤ s) e.hom_inv_id
  have h : e.inv ≫ e'.hom = 𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
    apply unitScalar_injective
    change Hom.app e'.hom ⊤ (Hom.app e.inv ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤))
    rw [hinv]
    exact hs'
  apply Iso.ext
  calc
    e.hom = e.hom ≫ 𝟙 _ := (Category.comp_id e.hom).symm
    _ = e.hom ≫ (e.inv ≫ e'.hom) := congrArg (fun θ => e.hom ≫ θ) h.symm
    _ = e'.hom := e.hom_inv_id_assoc e'.hom

end AlgebraicGeometry.Scheme.Modules
