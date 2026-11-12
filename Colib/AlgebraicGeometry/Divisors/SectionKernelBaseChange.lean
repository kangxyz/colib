/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.DifferenceSheaf

/-!
# Section kernels under arbitrary base change

The base-changed section is the actual pullback lift. Its image ideal is the
scheme-theoretic inverse image of the original section kernel, without a
flatness or reducedness hypothesis on the base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X S T : Scheme.{u}} (q : X ⟶ S) (g : T ⟶ S)
  (s : S ⟶ X) (hs : s ≫ q = 𝟙 S)

/-- The actual section of the base-changed scheme `X ×_S T`. -/
def baseChangedSection : T ⟶ pullback q g :=
  pullback.lift (g ≫ s) (𝟙 T) (by simp [Category.assoc, hs])

/-- Projection of the base-changed section to the original scheme. -/
@[reassoc (attr := simp)]
theorem baseChangedSection_fst :
    baseChangedSection q g s hs ≫ pullback.fst q g = g ≫ s :=
  pullback.lift_fst _ _ _

/-- The base-changed morphism is a section of the actual second projection. -/
@[reassoc (attr := simp)]
theorem baseChangedSection_snd :
    baseChangedSection q g s hs ≫ pullback.snd q g = 𝟙 T :=
  pullback.lift_snd _ _ _

/-- A section and its base-changed section form a Cartesian square. -/
theorem isPullback_baseChangedSection :
    IsPullback (baseChangedSection q g s hs) g (pullback.fst q g) s := by
  refine IsPullback.of_right ?_ (baseChangedSection_fst q g s hs)
    (IsPullback.of_hasPullback q g).flip
  rw [baseChangedSection_snd, hs]
  exact IsPullback.id_horiz g

/-- The kernel ideal of a base-changed section is the actual inverse-image ideal. -/
theorem ker_baseChangedSection [IsSeparated q] :
    (baseChangedSection q g s hs).ker = s.ker.comap (pullback.fst q g) := by
  have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
  have h := isPullback_baseChangedSection q g s hs
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

end AlgebraicGeometry.Scheme
