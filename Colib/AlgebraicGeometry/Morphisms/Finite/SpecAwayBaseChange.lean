/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Finite base change to an actual localization spectrum

Finiteness over a target open suffices after any base change factoring through
that open. The localization specialization uses the native isomorphism with
the basic open, rather than identifying their scheme objects definitionally.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace AlgebraicGeometry

/-- A base change through an open uses finiteness only on that open. -/
theorem isFinite_pullback_fst_of_morphismRestrict
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsFinite (f ∣_ U)] (k : Y' ⟶ Y) (e : Y' ⟶ U.toScheme)
    (he : e ≫ U.ι = k) : IsFinite (pullback.fst k f) := by
  have hOuter : IsPullback (pullback.snd k f) (pullback.fst k f) f (e ≫ U.ι) := by
    rw [he]
    exact (IsPullback.of_hasPullback k f).flip
  exact MorphismProperty.of_isPullback (P := @IsFinite)
    (hOuter.of_right' (isPullback_morphismRestrict f U).flip) inferInstance

/-- The actual base change to Spec R[1/t] is finite when the original morphism
is finite over D(t); no global finiteness of the original morphism is required. -/
theorem isFinite_pullback_fst_specAway_of_morphismRestrict
    {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (t : R)
    [IsFinite (f ∣_ PrimeSpectrum.basicOpen t)] :
    IsFinite (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t)))) f) := by
  apply isFinite_pullback_fst_of_morphismRestrict f (PrimeSpectrum.basicOpen t)
    (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away t))))
    (basicOpenIsoSpecAway t).inv
  rw [← basicOpenIsoSpecAway_hom_SpecMap t, Iso.inv_hom_id_assoc]

end AlgebraicGeometry
