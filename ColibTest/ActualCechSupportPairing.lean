/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.IncidencePairing

/-!
# Actual Čech support and incidence consumers

These statements retain signed coefficients, both graph composites and actual
point lifts. The generic support scheme has no reducedness, flatness, integrality
or nonemptiness assumption. The incidence test uses the original Tor cycle.
Native in-package consumer of the actual support and incidence pairing.
-/

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Cor CategoryTheory CategoryTheory.Limits
open TopologicalSpace Stacks.Chow Function.locallyFinsuppWithin

attribute [local instance] isIntegral_integralComponentAt Classical.propDecidable

universe u

variable (k : Type u) [Field k]
  {T X Y V : Scheme.SmoothSite (Spec (.of k))}

section Integral

variable (D : Scheme.{u}) [IsIntegral D]
  (m₁ m₂ : D ⟶ pullback T.hom V.hom) [IsFinite m₁] [IsFinite m₂]
  [IsFinite (m₁ ≫ pullback.fst T.hom V.hom)]
  [IsFinite (m₂ ≫ pullback.fst T.hom V.hom)]
  (hm₁ : Set.range (m₁ ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
  (hm₂ : Set.range (m₂ ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
  (q : V ⟶ Y) [Etale q.left]
  (hs : m₁ ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
  (ht : m₁ ≫ pullback.snd T.hom V.hom ≫ q.left =
    m₂ ≫ pullback.snd T.hom V.hom ≫ q.left)

example : (weightedSupportImage k D m₁ hm₁).val =
    single (m₁ (genericPoint D)) (m₁.residueDegree (genericPoint D) : ℤ) := rfl

example : (weightedSupportImage k D m₁ hm₁).val =
    finiteCyclePushforward m₁ (single (genericPoint D) 1) :=
  weightedSupportImage_val k D m₁ hm₁

include hs ht in
example :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) =
      (-3 : ℤ) • (weightedSupportImage k D m₁ hm₁ - weightedSupportImage k D m₂ hm₂) :=
  exists_cech_boundary_of_common_support k D m₁ m₂ hm₁ hm₂ q hs ht (-3)

end Integral

section WholeSupport

variable (W : Scheme.{u}) (hW : (genericPoints W).Finite)
  (m₁ m₂ : W ⟶ pullback T.hom V.hom) [IsFinite m₁] [IsFinite m₂]
  [IsFinite (m₁ ≫ pullback.fst T.hom V.hom)]
  (hm₁ : ∀ x : genericPoints W,
    Set.range (((integralComponentAt x.val).subschemeι ≫ m₁) ≫
      pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
  (q : V ⟶ Y) [Etale q.left]
  (hs : m₁ ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
  (ht : m₁ ≫ pullback.snd T.hom V.hom ≫ q.left =
    m₂ ≫ pullback.snd T.hom V.hom ≫ q.left)

include hm₁ hs ht in
example (c : genericPoints W → ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q)).val =
        finiteCyclePushforward m₁ (AlgebraicCycle.ofGenericCoefficients hW (-c)) ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward m₂ (AlgebraicCycle.ofGenericCoefficients hW (-c)) ∧
      ∀ b, β.val b ≠ 0 → ∀ z : (integralComponentAt b).subscheme, ∃ w : W,
        (m₁ ≫ pullback.fst T.hom V.hom) w =
          ((integralComponentAt b).subschemeι ≫
            pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom) z ∧
        (m₁ ≫ pullback.snd T.hom V.hom) w =
          ((integralComponentAt b).subschemeι ≫
            pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
            (Scheme.SmoothSite.etalePullbackFst q q).left) z ∧
        (m₂ ≫ pullback.snd T.hom V.hom) w =
          ((integralComponentAt b).subschemeι ≫
            pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
            (Scheme.SmoothSite.etalePullbackSnd q q).left) z :=
  exists_cech_pairing_of_generic_coefficients_with_point_lift
    k W hW m₁ m₂ hm₁ q hs ht (-c)

end WholeSupport

section Incidence

variable (a : pullback (C := Scheme) T.hom X.hom) (b : pullback (C := Scheme) X.hom V.hom)
  (ha : IsFiniteCorrespondencePoint T.hom X.hom a)
  (hb : IsFiniteCorrespondencePoint X.hom V.hom b)
  (m₂ : correspondenceIncidence T.hom X.hom V.hom a b ⟶ pullback T.hom V.hom)
  [IsFinite m₂] (q : V ⟶ Y) [Etale q.left]
  (hs : correspondenceIncidenceMap T.hom X.hom V.hom a b ≫ pullback.fst T.hom V.hom =
    m₂ ≫ pullback.fst T.hom V.hom)
  (ht : correspondenceIncidenceMap T.hom X.hom V.hom a b ≫
    pullback.snd T.hom V.hom ≫ q.left = m₂ ≫ pullback.snd T.hom V.hom ≫ q.left)

include hs ht in
example :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) =
        incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward m₂ (AlgebraicCycle.ofGenericCoefficients
          (finite_genericPoints_correspondenceIncidence_of_smooth T.hom X.hom V.hom a b hb)
          (correspondenceIncidenceTorCoefficient k T.hom X.hom V.hom a b)) :=
  exists_cech_pairing_of_incidenceTor k a b ha hb m₂ q hs ht

end Incidence
