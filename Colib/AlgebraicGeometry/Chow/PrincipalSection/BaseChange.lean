/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.PrincipalSection.Naturality

/-!
# Base change of the whole zero scheme of a section

The affine-line map of the restricted section is the actual composite.
Its zero fibre is Cartesian over the original zero fibre, including the
scheme structure.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

open AffineLineFiber

variable {k : Type u} [Field k] {P D : Scheme.{u}}
  (b : P ⟶ Spec (.of k)) (a : D ⟶ P) (s : Γ(P, ⊤))

local notation "F" => sectionToAffineLine b s
set_option quotPrecheck false in
local notation "Fₐ" => sectionToAffineLine (a ≫ b) (a.appTop s)

/-- The original pullback map on the entire zero schemes. -/
def sectionZeroBaseChangeMap : fiber Fₐ 0 ⟶ fiber F 0 :=
  pullback.lift (pullback.fst (point (0 : k)) Fₐ) (inclusion Fₐ 0 ≫ a) (by
    rw [Category.assoc, ← sectionToAffineLine_comp a b s]
    exact pullback.condition)

@[reassoc (attr := simp)] theorem sectionZeroBaseChangeMap_fst :
    sectionZeroBaseChangeMap b a s ≫ pullback.fst (point (0 : k)) F =
      pullback.fst (point (0 : k)) Fₐ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem sectionZeroBaseChangeMap_inclusion :
    sectionZeroBaseChangeMap b a s ≫ inclusion F 0 = inclusion Fₐ 0 ≫ a :=
  pullback.lift_snd _ _ _

/-- The actual restricted zero scheme is the pullback along the original map. -/
theorem isPullback_sectionZeroBaseChangeMap :
    IsPullback (sectionZeroBaseChangeMap b a s) (inclusion Fₐ 0) (inclusion F 0) a := by
  have h : IsPullback (sectionZeroBaseChangeMap b a s ≫ pullback.fst (point (0 : k)) F)
      (inclusion Fₐ 0) (point (0 : k)) (a ≫ F) := by
    rw [sectionZeroBaseChangeMap_fst, ← sectionToAffineLine_comp a b s]
    exact IsPullback.of_hasPullback _ _
  exact h.of_right (sectionZeroBaseChangeMap_inclusion b a s) (IsPullback.of_hasPullback _ _)

end AlgebraicGeometry.Scheme
