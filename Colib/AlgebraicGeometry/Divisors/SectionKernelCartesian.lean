/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Original section kernels in a specified Cartesian square

The construction uses the supplied schemes and sections, not chosen replacements by
categorical pullback objects. Their full kernel ideals are the literal inverse images.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A specified pullback of a closed immersion retains its full kernel ideal. -/
theorem ker_eq_comap_of_isPullback
    {Z' Z X' X : Scheme.{u}} (i' : Z' ⟶ X') (g : Z' ⟶ Z)
    (f : X' ⟶ X) (i : Z ⟶ X) [IsClosedImmersion i]
    (h : IsPullback i' g f i) : i'.ker = i.ker.comap f := by
  rw [← h.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]

/-- Compatible original sections of a Cartesian family form a Cartesian section square. -/
theorem isPullback_section_of_isPullback
    {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (q' : X' ⟶ S')
    (q : X ⟶ S) (g : S' ⟶ S) (h : IsPullback f q' q g)
    (s' : S' ⟶ X') (s : S ⟶ X)
    (hs' : s' ≫ q' = 𝟙 S') (hs : s ≫ q = 𝟙 S)
    (hsec : s' ≫ f = g ≫ s) : IsPullback s' g f s := by
  refine IsPullback.of_right ?_ hsec h.flip
  rw [hs', hs]
  exact IsPullback.id_horiz g

/-- The original section kernel in a separated Cartesian family is the exact inverse image,
with no flatness or reducedness assumption on the change of base. -/
theorem ker_section_of_isPullback
    {X' X S' S : Scheme.{u}} (f : X' ⟶ X) (q' : X' ⟶ S')
    (q : X ⟶ S) (g : S' ⟶ S) [IsSeparated q] (h : IsPullback f q' q g)
    (s' : S' ⟶ X') (s : S ⟶ X)
    (hs' : s' ≫ q' = 𝟙 S') (hs : s ≫ q = 𝟙 S)
    (hsec : s' ≫ f = g ≫ s) : s'.ker = s.ker.comap f := by
  have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
  have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
  exact ker_eq_comap_of_isPullback s' g f s
    (isPullback_section_of_isPullback f q' q g h s' s hs' hs hsec)

end AlgebraicGeometry.Scheme
