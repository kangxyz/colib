/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.Contraction

/-!
# Native signed Čech contraction consumers

These consumers retain the original generic coefficients and Tor cycle, all
three graph/pushforward identities, and all-point properties under a finite
signed sum. The concrete family test has no assumed Čech pairing identity.

-/

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Cor CategoryTheory CategoryTheory.Limits
open TopologicalSpace Stacks.Chow
open scoped BigOperators

attribute [local instance] isIntegral_integralComponentAt

universe u v

variable (k : Type u) [Field k]
  {T X Y V : Scheme.SmoothSite (Spec (.of k))}

example (W : Scheme.{u}) (hW : (genericPoints W).Finite)
    (m : W ⟶ pullback T.hom V.hom) [IsFinite m]
    [IsFinite (m ≫ pullback.fst T.hom V.hom)]
    (hm : ∀ x : genericPoints W,
      Set.range (((integralComponentAt x.val).subschemeι ≫ m) ≫
        pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
    (q : V ⟶ Y) (j : W ⟶ pullback T.hom Y.hom) [IsFinite j]
    (hj₁ : j ≫ pullback.fst T.hom Y.hom = m ≫ pullback.fst T.hom V.hom)
    (hj₂ : j ≫ pullback.snd T.hom Y.hom = m ≫ pullback.snd T.hom V.hom ≫ q.left)
    (c : genericPoints W → ℤ) (n : ℤ) (α : Cor.mk T ⟶ Cor.mk V)
    (hα : α.val = finiteCyclePushforward m (AlgebraicCycle.ofGenericCoefficients hW (n • c))) :
    (α ≫ (graphFunctor k).map q).val =
      finiteCyclePushforward j (AlgebraicCycle.ofGenericCoefficients hW (n • c)) :=
  comp_graph_val_of_generic_coefficients k W hW m hm q j hj₁ hj₂ (n • c) α hα

example (a : pullback (C := Scheme) T.hom X.hom) (b : pullback (C := Scheme) X.hom V.hom)
    (ha : IsFiniteCorrespondencePoint T.hom X.hom a)
    (hb : IsFiniteCorrespondencePoint X.hom V.hom b)
    (q : V ⟶ Y) [Etale q.left] (C : Scheme.{u})
    (r : correspondenceIncidence T.hom X.hom V.hom a b ⟶ C) [IsFinite r]
    (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsClosedImmersion j]
    (hsrc : s ≫ pullback.fst T.hom V.hom = j ≫ pullback.fst T.hom Y.hom)
    (htgt : s ≫ pullback.snd T.hom V.hom ≫ q.left = j ≫ pullback.snd T.hom Y.hom)
    (hrsource : r ≫ s ≫ pullback.fst T.hom V.hom =
      correspondenceIncidenceLeft T.hom X.hom V.hom a b)
    (hrtarget : r ≫ j ≫ pullback.snd T.hom Y.hom =
      correspondenceIncidenceRight T.hom X.hom V.hom a b ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) =
        incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward s (finiteCyclePushforward r
          (incidenceTorCycle T.hom X.hom V.hom a b hb)) ∧
      ((incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb : Cor.mk T ⟶ Cor.mk V) ≫
        (graphFunctor k).map q).val =
        finiteCyclePushforward j (finiteCyclePushforward r
          (incidenceTorCycle T.hom X.hom V.hom a b hb)) :=
  exists_cech_incidence_pairing_over_common_support
    k a b ha hb q C r s j hsrc htgt hrsource hrtarget

example {I : Type v} [Fintype I] (α : Cor.mk T ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (C : Scheme.{u}) (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsClosedImmersion j]
    (γ : I → (Cor.mk T ⟶ Cor.mk V)) (δ : I → AlgebraicCycle C ℤ) (n : I → ℤ)
    (Q : ∀ v : pullback (C := Scheme) T.hom (Scheme.SmoothSite.etalePullback q q).hom,
      (integralComponentAt v).subscheme → Prop)
    (hα : ∑ i, n i • γ i = α)
    (hpair : ∀ i, ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) = γ i ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward s (δ i) ∧
      (γ i ≫ (graphFunctor k).map q).val = finiteCyclePushforward j (δ i) ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme, Q v z)
    (hzero : α ≫ (graphFunctor k).map q = 0) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) = α ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme, Q v z :=
  exists_cech_boundary_of_finite_presentation_with_point_property
    k α q C s j γ δ n Q hα hpair hzero

example {I : Type v} [Fintype I] (α : Cor.mk T ⟶ Cor.mk V)
    (a : I → pullback (C := Scheme) T.hom X.hom) (b : I → pullback (C := Scheme) X.hom V.hom)
    (ha : ∀ i, IsFiniteCorrespondencePoint T.hom X.hom (a i))
    (hb : ∀ i, IsFiniteCorrespondencePoint X.hom V.hom (b i))
    (n : I → ℤ) (q : V ⟶ Y) [Etale q.left] (C : Scheme.{u})
    (r : ∀ i, correspondenceIncidence T.hom X.hom V.hom (a i) (b i) ⟶ C)
    [∀ i, IsFinite (r i)]
    (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsClosedImmersion j]
    (hsrc : s ≫ pullback.fst T.hom V.hom = j ≫ pullback.fst T.hom Y.hom)
    (htgt : s ≫ pullback.snd T.hom V.hom ≫ q.left = j ≫ pullback.snd T.hom Y.hom)
    (hrsource : ∀ i, r i ≫ s ≫ pullback.fst T.hom V.hom =
      correspondenceIncidenceLeft T.hom X.hom V.hom (a i) (b i))
    (hrtarget : ∀ i, r i ≫ j ≫ pullback.snd T.hom Y.hom =
      correspondenceIncidenceRight T.hom X.hom V.hom (a i) (b i) ≫ q.left)
    (hα : ∑ i, n i • incidenceTorCorrespondence T.hom X.hom V.hom
      (a i) (b i) (ha i) (hb i) = α)
    (hzero : α ≫ (graphFunctor k).map q = 0) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) = α ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme,
        ∃ i, ∃ w : correspondenceIncidence T.hom X.hom V.hom (a i) (b i),
          correspondenceIncidenceLeft T.hom X.hom V.hom (a i) (b i) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom) z ∧
          correspondenceIncidenceRight T.hom X.hom V.hom (a i) (b i) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackFst q q).left) z ∧
          ((r i ≫ s) ≫ pullback.snd T.hom V.hom) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackSnd q q).left) z :=
  exists_cech_boundary_of_incidence_presentation_with_point_lift
    k α a b ha hb n q C r s j hsrc htgt hrsource hrtarget hα hzero
