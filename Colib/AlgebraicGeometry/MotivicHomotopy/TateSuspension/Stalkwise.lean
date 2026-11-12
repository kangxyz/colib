/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.TateSuspension.Functor
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.CategoryTheory.Sites.Simplicial.SmashWeakEquivalence

/-!
# Tate suspension in the Nisnevich homotopy category

Smashing with the lifted pointed Tate quotient preserves the original
stalkwise weak equivalences on the smooth Nisnevich site. This gives the
induced functor and its comparison with the original Tate smash.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.PointedSimplicialPresheaf
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.MotivicHomotopy

variable (R : CommRingCat.{u})

local notation "Cᵣ" => SmoothSite (Spec R)
local notation "Jᵣ" => SmoothSite.nisnevichTopology (Spec R)
local notation "Qₛ" => toStalkwiseHomotopyCategory Cᵣ Jᵣ

/-- The actual Tate presheaf suspension preserves Nisnevich stalkwise weak equivalences. -/
@[colib_tag "COL-1035",
  colib_ref "Jardine2000MotivicSpectra" "Section 1.3, Lemma 1.5, p. 459" "ingredient"
    "Stalkwise gluing for the product and the union of the two axes"]
theorem stalkwiseWeakEquivalences_tatePresheafSuspension_map
    {X Y : PointedSimplicialPresheaf.{u + 1} Cᵣ} {f : X ⟶ Y}
    (hf : stalkwiseWeakEquivalences Cᵣ Jᵣ f) :
    stalkwiseWeakEquivalences Cᵣ Jᵣ ((tatePresheafSuspension R).map f) :=
  stalkwiseWeakEquivalences_smashRightFunctor_map Jᵣ (liftedTateSphere R) hf

private theorem tateStalkwiseInverts :
    (stalkwiseWeakEquivalences Cᵣ Jᵣ).IsInvertedBy (tatePresheafSuspension R ⋙ Qₛ) :=
  fun _ _ f hf ↦ isIso_toStalkwiseHomotopyCategory_map Cᵣ ((tatePresheafSuspension R).map f)
    (stalkwiseWeakEquivalences_tatePresheafSuspension_map R hf)

/-- Tate suspension on the chosen stalkwise homotopy category. -/
@[no_expose]
def tateStalkwiseSuspension :
    StalkwiseHomotopyCategory.{u + 1} Cᵣ Jᵣ ⥤ StalkwiseHomotopyCategory.{u + 1} Cᵣ Jᵣ :=
  Localization.lift (tatePresheafSuspension R ⋙ Qₛ) (tateStalkwiseInverts R) Qₛ

/-- The stalkwise lift agrees with the actual Tate smash on presheaves. -/
@[colib_tag "COL-1035", no_expose]
def tateStalkwiseSuspensionCompIso :
    Qₛ ⋙ tateStalkwiseSuspension R ≅ tatePresheafSuspension R ⋙ Qₛ :=
  Localization.fac (tatePresheafSuspension R ⋙ Qₛ) (tateStalkwiseInverts R) Qₛ

end AlgebraicGeometry.MotivicHomotopy
