/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.RingTheory.Polynomial.LaurentSquare
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Actual polynomial and Laurent coefficient pushouts

The original universal maps are polynomial evaluation and Laurent evaluation at the
literal forward coordinate unit. Native ring maps replace only the source's aliases.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace CommRingCat.PolynomialLaurent

/-- The original polynomial evaluation realizes coefficient extension as a pushout. -/
@[colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/BaseChange.lean:52"
  "adaptation" "Original coefficient pushout, same evaluation and literal forward coordinate"]
lemma polynomial_isPushout {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPushout f (CommRingCat.ofHom Polynomial.C) (CommRingCat.ofHom Polynomial.C)
      (CommRingCat.ofHom (Polynomial.mapRingHom f.hom)) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (polynomial_coefficient_square f))
  apply PushoutCocone.isColimitAux'
  intro s
  let d : CommRingCat.of (Polynomial S) ⟶ s.pt :=
    CommRingCat.ofHom (Polynomial.eval₂RingHom s.inl.hom (s.inr Polynomial.X))
  refine ⟨d, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact Polynomial.eval₂_C _ _
  · apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      change Polynomial.eval₂ s.inl.hom (s.inr Polynomial.X) ((Polynomial.C r).map f.hom) = s.inr
        (Polynomial.C r)
      rw [Polynomial.map_C, Polynomial.eval₂_C]
      exact congrArg (fun h ↦ h r) s.condition
    · change Polynomial.eval₂ s.inl.hom (s.inr Polynomial.X) (Polynomial.X.map f.hom) =
        s.inr Polynomial.X
      rw [Polynomial.map_X, Polynomial.eval₂_X]
  · intro h hl hr
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro a
      change h (Polynomial.C a) = Polynomial.eval₂ s.inl.hom (s.inr Polynomial.X) (Polynomial.C a)
      rw [Polynomial.eval₂_C]
      exact congrArg (fun k ↦ k a) hl
    · change h Polynomial.X = Polynomial.eval₂ s.inl.hom (s.inr Polynomial.X) Polynomial.X
      rw [Polynomial.eval₂_X]
      have hx := congrArg (fun k ↦ k Polynomial.X) hr
      change h (Polynomial.X.map f.hom) = s.inr Polynomial.X at hx
      simpa only [Polynomial.map_X] using hx

/-- The native Laurent coefficient map preserves every original constant. -/
@[simp, colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/BaseChange.lean:95"
  "adaptation" "Original coefficient pushout, same evaluation and literal forward coordinate"]
lemma laurentMap_C {R S : CommRingCat.{u}} (f : R ⟶ S) (r : R) :
    (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom)) (LaurentPolynomial.C r) =
      LaurentPolynomial.C (f r) :=
  AddMonoidAlgebra.mapRingHom_single f.hom 0 r

/-- The native Laurent coefficient map fixes every original monomial. -/
@[simp, colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/BaseChange.lean:99"
  "adaptation" "Original coefficient pushout, same evaluation and literal forward coordinate"]
lemma laurentMap_T {R S : CommRingCat.{u}} (f : R ⟶ S) (n : ℤ) :
    (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom)) (LaurentPolynomial.T n) =
      LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ f.hom (AddMonoidAlgebra.single n 1) = AddMonoidAlgebra.single
    n 1
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

/-- Laurent ring maps are determined by the original coefficients and T itself. -/
@[colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/BaseChange.lean:106"
  "adaptation" "Original coefficient pushout, same evaluation and literal forward coordinate"]
lemma laurent_hom_ext {R A : Type u} [CommRing R] [CommRing A]
    (f g : LaurentPolynomial R →+* A)
    (hC : ∀ r, f (LaurentPolynomial.C r) = g (LaurentPolynomial.C r))
    (hT : f (LaurentPolynomial.T 1) = g (LaurentPolynomial.T 1)) : f = g := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (Polynomial.X : Polynomial R))
  apply Polynomial.ringHom_ext
  · intro r
    change f (Polynomial.toLaurent (Polynomial.C r)) = g (Polynomial.toLaurent (Polynomial.C r))
    rw [Polynomial.toLaurent_C]
    exact hC r
  · change f (Polynomial.toLaurent Polynomial.X) = g (Polynomial.toLaurent Polynomial.X)
    rw [Polynomial.toLaurent_X]
    exact hT

/-- The actual coordinate unit with its literal inverse coordinate. -/
@[colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/BaseChange.lean:121"
  "adaptation" "Original coefficient pushout, same evaluation and literal forward coordinate"]
def coordinateUnit (R : CommRingCat.{u}) : (LaurentPolynomial R)ˣ :=
  ⟨LaurentPolynomial.T 1, LaurentPolynomial.T (-1), by
    rw [← LaurentPolynomial.T_add]; norm_num, by
    rw [← LaurentPolynomial.T_add]; norm_num⟩

/-- Laurent coefficient extension commutes with the original constant inclusions. -/
@[colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/BaseChange.lean:126"
  "adaptation" "Original coefficient pushout, same evaluation and literal forward coordinate"]
lemma laurent_square {R S : CommRingCat.{u}} (f : R ⟶ S) :
    f ≫ CommRingCat.ofHom (LaurentPolynomial.C : S →+* LaurentPolynomial S) = CommRingCat.ofHom
      (LaurentPolynomial.C : R →+* LaurentPolynomial R) ≫ CommRingCat.ofHom
      (AddMonoidAlgebra.mapRingHom ℤ f.hom) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (laurentMap_C f r).symm

/-- Laurent coefficient extension is the actual original ring pushout. -/
@[colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/BaseChange.lean:134"
  "adaptation" "Original coefficient pushout, same evaluation and literal forward coordinate"]
lemma laurent_isPushout {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPushout f (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))
      (CommRingCat.ofHom (LaurentPolynomial.C : S →+* LaurentPolynomial S)) (CommRingCat.ofHom
      (AddMonoidAlgebra.mapRingHom ℤ f.hom)) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (laurent_square f))
  apply PushoutCocone.isColimitAux'
  intro s
  let t : s.ptˣ := Units.map s.inr.hom.toMonoidHom (coordinateUnit R)
  let d : CommRingCat.of (LaurentPolynomial S) ⟶ s.pt :=
    CommRingCat.ofHom (LaurentPolynomial.eval₂ s.inl.hom t)
  have ht : (t : s.pt) = s.inr (LaurentPolynomial.T 1) := rfl
  refine ⟨d, ?_, ?_, ?_⟩
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact LaurentPolynomial.eval₂_C _ _ _
  · apply CommRingCat.hom_ext
    apply laurent_hom_ext
    · intro r
      change LaurentPolynomial.eval₂ s.inl.hom t ((CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom
        ℤ f.hom)) (LaurentPolynomial.C r)) = s.inr
        (LaurentPolynomial.C r)
      rw [laurentMap_C, LaurentPolynomial.eval₂_C]
      exact congrArg (fun h ↦ h r) s.condition
    · change LaurentPolynomial.eval₂ s.inl.hom t ((CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom
      ℤ f.hom)) (LaurentPolynomial.T 1)) =
        s.inr (LaurentPolynomial.T 1)
      rw [laurentMap_T, LaurentPolynomial.eval₂_T, zpow_one, ht]
  · intro h hl hr
    apply CommRingCat.hom_ext
    apply laurent_hom_ext
    · intro a
      change h (LaurentPolynomial.C a) = LaurentPolynomial.eval₂ s.inl.hom t (LaurentPolynomial.C a)
      rw [LaurentPolynomial.eval₂_C]
      exact congrArg (fun k ↦ k a) hl
    · change h (LaurentPolynomial.T 1) = LaurentPolynomial.eval₂ s.inl.hom t (LaurentPolynomial.T 1)
      rw [LaurentPolynomial.eval₂_T, zpow_one, ht]
      have hx := congrArg (fun k ↦ k (LaurentPolynomial.T 1)) hr
      change h ((CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ f.hom)) (LaurentPolynomial.T 1))
        = _ at hx
      rwa [laurentMap_T] at hx

/-- The actual native polynomial coefficient maps preserve composition. -/
@[simp, colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/BaseChange.lean:171"
  "adaptation" "Original coefficient pushout, same evaluation and literal forward coordinate"]
lemma polynomialMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    CommRingCat.ofHom (Polynomial.mapRingHom (f ≫ g).hom) = CommRingCat.ofHom
      (Polynomial.mapRingHom f.hom) ≫ CommRingCat.ofHom (Polynomial.mapRingHom g.hom) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact (Polynomial.map_map f.hom g.hom p).symm

/-- The actual native Laurent coefficient maps preserve composition. -/
@[simp, colib_ref "aglib"
  "Aglib/Algebra/Polynomial/Laurent/BaseChange.lean:178"
  "adaptation" "Original coefficient pushout, same evaluation and literal forward coordinate"]
lemma laurentMap_comp {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (f ≫ g).hom) = CommRingCat.ofHom
      (AddMonoidAlgebra.mapRingHom ℤ f.hom) ≫ CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ
      g.hom) := by
  apply CommRingCat.hom_ext
  exact AddMonoidAlgebra.mapRingHom_comp g.hom f.hom

end CommRingCat.PolynomialLaurent
