/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.Morphisms.Etale.Neighborhood.AffineScalarClosedSquare

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

example {X Y X' : Scheme.{u}} (p : Y ⟶ X) (a : X' ⟶ X) (U : X.Opens)
    [IsFinite (p ∣_ U)] : IsFinite ((pullback.snd p a) ∣_ a ⁻¹ᵁ U) :=
  finite_pullback_on_original_chart p a U

example (B S : Type u) [CommRing B] [CommRing S] [Algebra B S] (J : Ideal B) :
    Set.range (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (J.map (algebraMap B S))))) =
      (Spec.map (CommRingCat.ofHom (algebraMap B S))) ⁻¹'
        Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
  range_spec_quotient_map_baseChange B S J

example (B S : Type u) [CommRing B] [CommRing S] [Algebra B S]
    (J : Ideal B) {Y : Scheme.{u}} (p : Y ⟶ Spec (.of B))
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    IsPullback (quotientBaseChangeEtaleLift B S J p s hs) (𝟙 _)
      (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap B S))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap B S))))) :=
  quotientBaseChangeEtaleLift_isPullback B S J p s hs H

example (B S : Type u) [CommRing B] [CommRing S] [Algebra B S]
    (J : Ideal B) {A : Scheme.{u}} (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (hcover : ∀ x : Spec (.of B), x ∈ Set.range a ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    ∀ x : Spec (.of S),
      x ∈ Set.range (pullback.snd a (Spec.map (CommRingCat.ofHom (algebraMap B S)))) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (J.map (algebraMap B S))))) :=
  quotientBaseChange_punctured_cover B S J a hcover
