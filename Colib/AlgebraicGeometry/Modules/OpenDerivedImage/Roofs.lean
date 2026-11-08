/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.Basic
public import Colib.Algebra.Homology.DerivedCategory.EqualityDenominators

/-!
# Homotopy roofs from global perfect models

The geometric roof input concerns only two global native perfect complexes. Given that input,
actual localization denominators produce two genuine homotopies with one common target.
This intermediate result does not assert the geometric roof existence theorem.

Adapted from Quillen's `OpenDerivedImage/Roofs.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage

universe u d

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules]

local notation "R" => Functor.mapHomologicalComplex (restrictFunctor j) (ComplexShape.up ℤ)

/-- The geometric roof input only involves two globally perfect models.
Its denominator is required weak on the original open, not globally weak. -/
def HasDerivedRoofs : Prop :=
  ∀ (A P : CochainComplex X.Modules ℤ),
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) A →
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) P →
    ∀ α : (DerivedCategory.Q (C := U.Modules)).obj ((R).obj A) ⟶
      (DerivedCategory.Q (C := U.Modules)).obj ((R).obj P),
      ∃ (A' : CochainComplex X.Modules ℤ) (q : A' ⟶ A) (a : A' ⟶ P),
        RingedSpace.IsPerfectComplex (X := X.toRingedSpace) A' ∧ QuasiIso ((R).map q) ∧
        (DerivedCategory.Q (C := U.Modules)).map ((R).map q) ≫ α =
          (DerivedCategory.Q (C := U.Modules)).map ((R).map a)

/-- Genuine module/geometric roofs between global models give a complete
original homotopy roof for arbitrary sheaf-complex targets. The remaining
all-sheaf denominators are legitimate localization denominators only. -/
theorem exists_homotopy_roof (hroof : HasDerivedRoofs j)
    (P : CochainComplex X.Modules ℤ)
    (hP : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) P)
    (B B' : CochainComplex U.Modules ℤ)
    (hB' : complexObjects j B') (w : (R).obj P ⟶ B) [QuasiIso w] (b : B' ⟶ B) :
    ∃ (A : CochainComplex X.Modules ℤ) (M N : CochainComplex U.Modules ℤ)
      (a : A ⟶ P) (p : (R).obj A ⟶ M) (t : B' ⟶ M)
      (s : B ⟶ N) (q : M ⟶ N),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) A ∧
      RingedSpace.IsPerfectComplex (X := U.toRingedSpace) M ∧
      RingedSpace.IsPerfectComplex (X := U.toRingedSpace) N ∧
      QuasiIso p ∧ QuasiIso t ∧ QuasiIso s ∧
      Nonempty (Homotopy (p ≫ q) ((R).map a ≫ w ≫ s)) ∧
      Nonempty (Homotopy (t ≫ q) (b ≫ s)) := by
  obtain ⟨A₀, M, p₀, t, hA₀, hM, hp₀, ht⟩ := exists_weak_cospan j hB'
  let D := DerivedCategory.Q (C := U.Modules)
  let β : D.obj M ⟶ D.obj B := inv (D.map t) ≫ D.map b
  let α : D.obj ((R).obj A₀) ⟶ D.obj ((R).obj P) :=
    D.map p₀ ≫ β ≫ inv (D.map w)
  obtain ⟨A, r, a, hA, hr, ha⟩ := hroof A₀ P hA₀ hP α
  let p := (R).map r ≫ p₀
  have hp : QuasiIso p := inferInstance
  obtain ⟨N, q, s, hDenIso1, hFac1⟩ := DerivedCategory.left_fac β
  have hs : QuasiIso s :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).1 hDenIso1
  have he : (β) ≫ DerivedCategory.Q.map s = DerivedCategory.Q.map q := by
    let := hDenIso1
    rw [hFac1, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hw : QuasiIso (C := U.Modules) w := inferInstance
  have hB : RingedSpace.IsPerfectComplex (X := U.toRingedSpace) B :=
    (Complex.isPerfectComplex_restrictOpenImmersion j P hP).of_quasiIso w hw
  have hN : RingedSpace.IsPerfectComplex (X := U.toRingedSpace) N := hB.of_quasiIso s hs
  change D.map ((R).map r) ≫ α = D.map ((R).map a) at ha
  change β ≫ D.map s = D.map q at he
  have heq₁ : D.map (p ≫ q) = D.map ((R).map a ≫ w ≫ s) := by
    simp only [Functor.map_comp]
    rw [← ha, ← he]
    simp [p, α, Category.assoc]
  have heq₂ : D.map (t ≫ q) = D.map (b ≫ s) := by
    rw [Functor.map_comp, ← he]
    simp [β]
  obtain ⟨N', z, hz, ⟨H₁⟩, ⟨H₂⟩⟩ :=
    CochainComplex.exists_post_quasiIso_two_homotopies_of_derived_eq
      (C := U.Modules) (p ≫ q) ((R).map a ≫ w ≫ s)
      (t ≫ q) (b ≫ s) heq₁ heq₂
  exact ⟨A, M, N', a, p, t, s ≫ z, q ≫ z, hA, hM,
    hN.of_quasiIso z hz, hp, ht, inferInstance,
    ⟨by simpa only [Category.assoc] using H₁⟩,
    ⟨by simpa only [Category.assoc] using H₂⟩⟩

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
