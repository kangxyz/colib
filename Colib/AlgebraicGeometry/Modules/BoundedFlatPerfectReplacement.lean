/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfect
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories

/-!
# Actual Bounded Above Flat Perfect Replacements

Native flat covers and the actual bounded-above resolution theorem produce original
quasi-isomorphism augmentations. A cohomology upper bound suffices, with no change in that bound.
For a termwise bounded target the augmentation is degreewise epimorphic. This is object
replacement, not relative factorization of an arbitrary map or an assumed approximation theorem.

Adapted from `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Replacement.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, using Stacks Tags 03EW and 05T7.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect
open scoped ZeroObject

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

private def flatSheaves (X : RingedSpace.{u, u}) : ObjectProperty (OXMod.{u, u, u} X) :=
  fun M => AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) M

private instance flatSheaves_containsZero : (flatSheaves X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, isFlat_of_isZero _ (isZero_zero _)⟩

private theorem exists_epi_flatSheaves (M : OXMod.{u, u, u} X) :
    ∃ (N : OXMod.{u, u, u} X) (_ : flatSheaves X N) (p : N ⟶ M), Epi p := by
  obtain ⟨N, p, hN, hp⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat X.sheaf M
  exact ⟨N, hN, p, hp⟩

/-- A cohomologically upper-bounded perfect complex receives an actual flat replacement. -/
@[colib_tag "COL-0323", stacks 05T7 "Part (2), applied to native flat sheaf covers",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Replacement.lean:37-52"
    "adaptation" "Actual augmentation from a bounded-above flat perfect complex with sharp bound"]
theorem exists_boundedAboveFlatPerfectComplex_of_isLE
    (K : CochainComplex (OXMod.{u, u, u} X) ℤ) (hK : IsPerfectComplex K)
    (b : ℤ) [K.IsLE b] :
    ∃ (P : CochainComplex (OXMod.{u, u, u} X) ℤ) (p : P ⟶ K),
      QuasiIso p ∧ boundedAboveFlatPerfectComplex X P ∧ P.IsStrictlyLE b := by
  obtain ⟨P, p, hp, hf, hb⟩ :=
    (CochainComplex.exists_quasiIso_prop (flatSheaves X) exists_epi_flatSheaves b).2 K
  exact ⟨P, p, hp, ⟨(isPerfectComplex_iff_of_quasiIso p hp).2 hK, ⟨b, hb⟩, hf⟩, hb⟩

/-- A termwise upper-bounded perfect complex has a degreewise-surjective flat augmentation. -/
@[stacks 05T7 "Part (1), retaining the original degreewise epimorphism"]
theorem exists_epi_boundedAboveFlatPerfectComplex_of_isStrictlyLE
    (K : CochainComplex (OXMod.{u, u, u} X) ℤ) (hK : IsPerfectComplex K)
    (b : ℤ) [K.IsStrictlyLE b] :
    ∃ (P : CochainComplex (OXMod.{u, u, u} X) ℤ) (p : P ⟶ K),
      (∀ n, Epi (p.f n)) ∧ QuasiIso p ∧
        boundedAboveFlatPerfectComplex X P ∧ P.IsStrictlyLE b := by
  obtain ⟨P, p, he, hp, hf, hb⟩ :=
    (CochainComplex.exists_quasiIso_prop (flatSheaves X) exists_epi_flatSheaves b).1 K
  exact ⟨P, p, he, hp, ⟨(isPerfectComplex_iff_of_quasiIso p hp).2 hK, ⟨b, hb⟩, hf⟩, hb⟩

/-- An actual map from an upper-bounded source factors through target good truncation. -/
def boundedAboveMapToTruncLE
    {K L : CochainComplex (OXMod.{u, u, u} X) ℤ} (f : K ⟶ L)
    (b : ℤ) [K.IsStrictlyLE b] : K ⟶ L.truncLE b :=
  inv (K.ιTruncLE b) ≫ CochainComplex.truncLEMap f b

@[reassoc]
theorem boundedAboveMapToTruncLE_comp
    {K L : CochainComplex (OXMod.{u, u, u} X) ℤ} (f : K ⟶ L)
    (b : ℤ) [K.IsStrictlyLE b] : boundedAboveMapToTruncLE f b ≫ L.ιTruncLE b = f := by
  dsimp [boundedAboveMapToTruncLE]
  rw [Category.assoc, CochainComplex.ιTruncLE_naturality]
  simp

end AlgebraicGeometry.RingedSpace
