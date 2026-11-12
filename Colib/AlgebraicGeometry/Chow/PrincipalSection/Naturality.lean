/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection

/-!
# Naturality of a section's affine-line map

Pulling back a global section gives the composite of its original affine-line
map with the given morphism.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Polynomial

universe u

namespace AlgebraicGeometry.Scheme

variable {R : Type u} [CommRing R]

private theorem sectionToAffineLine_appTop {A : Scheme.{u}}
    (f : A ⟶ Spec (.of R)) (s : Γ(A, ⊤)) :
    (ΓSpecIso (.of R[X])).inv ≫ (sectionToAffineLine f s).appTop =
      CommRingCat.ofHom (Polynomial.eval₂RingHom
        (f.appTop.hom.comp (ΓSpecIso (.of R)).inv.hom) s) :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The affine-line map of a pulled-back section is the composite with the original map. -/
theorem sectionToAffineLine_comp {A D : Scheme.{u}}
    (v : D ⟶ A) (f : A ⟶ Spec (.of R)) (s : Γ(A, ⊤)) :
    sectionToAffineLine (v ≫ f) (v.appTop s) = v ≫ sectionToAffineLine f s := by
  apply ext_to_Spec
  simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop, ← Category.assoc,
    sectionToAffineLine_appTop]
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro a
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
  · simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]

end AlgebraicGeometry.Scheme
