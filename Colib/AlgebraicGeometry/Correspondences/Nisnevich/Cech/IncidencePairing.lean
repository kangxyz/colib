/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.Cech.SupportPairing

/-!
# Čech pairing of the original generic incidence coefficients

The actual whole-support map gives a Čech correspondence for every signed
coefficient function on the finite generic set of a scheme. Its two projections
are the exact native finite pushforwards. The two uses of the graph comparison
produce the same correspondence because their native cycles are equal, rather
than by an assumed abstract comparison or a new presentation.

Specializing to the genuine incidence scheme uses its original alternating Tor
coefficient function verbatim. Neither it nor the common support is replaced by
a reduction, and coefficients of coincident image points add with their signs.
The finite generic set is proved from incidence geometry in the application.
Every point of every surviving integral image support still lifts to that same
incidence scheme. This is not a local-exactness or Nisnevich-lifting theorem.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Cech/IncidencePairing.lean`.
The explicit finite-generic-set interface weakens the original Noetherian
hypothesis and is supplied by the existing native incidence theorem.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] isIntegral_integralComponentAt

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {T Y V : Scheme.SmoothSite (Spec (.of k))}

section GenericPairing

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

include hm₁ hs ht

/-- Every original signed generic coefficient and both finite pushforwards are
retained, together with actual lifts of all points of all surviving image supports. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/IncidencePairing.lean: \
exists_cech_pairing_of_generic_coefficients_with_point_lift"
  "adaptation" "native generic coefficients on the whole scheme, with both finite pushforwards \
and point lifts"]
theorem exists_cech_pairing_of_generic_coefficients_with_point_lift (c : genericPoints W → ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q)).val =
        finiteCyclePushforward m₁ (AlgebraicCycle.ofGenericCoefficients hW c) ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward m₂ (AlgebraicCycle.ofGenericCoefficients hW c) ∧
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
            (Scheme.SmoothSite.etalePullbackSnd q q).left) z := by
  let P := Scheme.SmoothSite.etalePullback q q
  let m := cechSupportMap k W m₁ m₂ q hs ht
  have hm : m ≫ pullback.fst T.hom P.hom = m₁ ≫ pullback.fst T.hom V.hom :=
    cechSupportMap_fst k W m₁ m₂ q hs ht
  have hadm (x : genericPoints W) : IsFiniteCorrespondencePoint T.hom P.hom (m x.val) := by
    apply isFiniteCorrespondencePoint_finiteMap T.hom P.hom m x.val
    · rw [Category.assoc, hm]
      infer_instance
    · simp only [Category.assoc, hm]
      have hx := hm₁ x
      simp only [Category.assoc] at hx
      exact hx
  obtain ⟨β₁, hβ₁, h₁⟩ := exists_graph_factorization_of_generic_support_map T.hom P.hom V.hom
    (Scheme.SmoothSite.etalePullbackFst q q).left
    (MorphismProperty.Over.w (Scheme.SmoothSite.etalePullbackFst q q))
    (finite_genericPoints k (Cor.mk P)) m m₁
    (cechSupportMap_graph_fst k W m₁ m₂ q hs ht) hW c hadm
  obtain ⟨β₂, hβ₂, h₂⟩ := exists_graph_factorization_of_generic_support_map T.hom P.hom V.hom
    (Scheme.SmoothSite.etalePullbackSnd q q).left
    (MorphismProperty.Over.w (Scheme.SmoothSite.etalePullbackSnd q q))
    (finite_genericPoints k (Cor.mk P)) m m₂
    (cechSupportMap_graph_snd k W m₁ m₂ q hs ht) hW c hadm
  have heq : β₁ = β₂ := Subtype.ext (hβ₁.trans hβ₂.symm)
  refine ⟨β₁, h₁, ?_, ?_⟩
  · rw [heq]
    exact h₂
  · exact cechSupportMap_point_lift k W m₁ m₂ q hs ht
      (AlgebraicCycle.ofGenericCoefficients hW c) β₁ hβ₁

/-- The same coefficient-cycle construction, retaining both exact graph pushforwards. -/
theorem exists_cech_pairing_of_generic_coefficients (c : genericPoints W → ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q)).val =
        finiteCyclePushforward m₁ (AlgebraicCycle.ofGenericCoefficients hW c) ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward m₂ (AlgebraicCycle.ofGenericCoefficients hW c) := by
  obtain ⟨β, h₁, h₂, _⟩ := exists_cech_pairing_of_generic_coefficients_with_point_lift
    k W hW m₁ m₂ hm₁ q hs ht c
  exact ⟨β, h₁, h₂⟩

/-- The boundary is the first-minus-second pushforward of the original signed cycle. -/
theorem exists_cech_boundary_of_generic_coefficients (c : genericPoints W → ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q)).val -
        (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
      finiteCyclePushforward m₁ (AlgebraicCycle.ofGenericCoefficients hW c) -
        finiteCyclePushforward m₂ (AlgebraicCycle.ofGenericCoefficients hW c) := by
  obtain ⟨β, h₁, h₂⟩ := exists_cech_pairing_of_generic_coefficients
    k W hW m₁ m₂ hm₁ q hs ht c
  exact ⟨β, congrArg₂
    (fun x y : AlgebraicCycle (pullback (C := Scheme) T.hom V.hom) ℤ => x - y) h₁ h₂⟩

end GenericPairing

section IncidenceTor

variable {X : Scheme.SmoothSite (Spec (.of k))}
  (a : pullback (C := Scheme) T.hom X.hom) (b : pullback (C := Scheme) X.hom V.hom)
  (ha : IsFiniteCorrespondencePoint T.hom X.hom a)
  (hb : IsFiniteCorrespondencePoint X.hom V.hom b)
  (m₂ : correspondenceIncidence T.hom X.hom V.hom a b ⟶ pullback T.hom V.hom)
  [IsFinite m₂] (q : V ⟶ Y) [Etale q.left]
  (hs : correspondenceIncidenceMap T.hom X.hom V.hom a b ≫ pullback.fst T.hom V.hom =
    m₂ ≫ pullback.fst T.hom V.hom)
  (ht : correspondenceIncidenceMap T.hom X.hom V.hom a b ≫
      pullback.snd T.hom V.hom ≫ q.left = m₂ ≫ pullback.snd T.hom V.hom ≫ q.left)

include hs ht

/-- The original alternating Tor coefficients give the actual incidence correspondence
on the first side, their exact finite pushforward on the second, and full point lifts. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/IncidencePairing.lean: \
exists_cech_pairing_of_incidenceTor_with_point_lift"
  "adaptation" "the original native incidence scheme and signed Tor cycle, with actual \
residue-degree pushforwards"]
theorem exists_cech_pairing_of_incidenceTor_with_point_lift :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) =
        incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward m₂ (incidenceTorCycle T.hom X.hom V.hom a b hb) ∧
      ∀ v, β.val v ≠ 0 → ∀ z : (integralComponentAt v).subscheme,
        ∃ w : correspondenceIncidence T.hom X.hom V.hom a b,
          correspondenceIncidenceLeft T.hom X.hom V.hom a b w =
            ((integralComponentAt v).subschemeι ≫
              pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom) z ∧
          correspondenceIncidenceRight T.hom X.hom V.hom a b w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackFst q q).left) z ∧
          (m₂ ≫ pullback.snd T.hom V.hom) w =
            ((integralComponentAt v).subschemeι ≫
              pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
              (Scheme.SmoothSite.etalePullbackSnd q q).left) z := by
  have : IsFinite (correspondenceIncidenceMap T.hom X.hom V.hom a b) :=
    isFinite_correspondenceIncidenceMap T.hom X.hom V.hom a b ha hb
  have : IsFinite (correspondenceIncidenceLeft T.hom X.hom V.hom a b) :=
    isFinite_correspondenceIncidenceLeft T.hom X.hom V.hom a b ha hb
  have : IsFinite (correspondenceIncidenceMap T.hom X.hom V.hom a b ≫
      pullback.fst T.hom V.hom) := by
    rw [correspondenceIncidenceMap_fst]
    infer_instance
  obtain ⟨β, h₁, h₂, hpoint⟩ := exists_cech_pairing_of_generic_coefficients_with_point_lift
    k (correspondenceIncidence T.hom X.hom V.hom a b)
    (finite_genericPoints_correspondenceIncidence_of_smooth T.hom X.hom V.hom a b hb)
    (correspondenceIncidenceMap T.hom X.hom V.hom a b) m₂
    (fun x => by
      simp only [Category.assoc, correspondenceIncidenceMap_fst]
      exact range_integralComponent_correspondenceIncidenceLeft_mem_of_smooth
          T.hom X.hom V.hom a b ha hb x.val x.property)
    q hs ht (correspondenceIncidenceTorCoefficient k T.hom X.hom V.hom a b)
  refine ⟨β, ?_, h₂, ?_⟩
  · apply Subtype.ext
    exact h₁.trans (incidenceTorCorrespondence_val T.hom X.hom V.hom a b ha hb).symm
  · simpa only [correspondenceIncidenceMap_fst, correspondenceIncidenceMap_snd] using hpoint

/-- The original incidence-Tor endpoint, retaining both actual cycle projections. -/
theorem exists_cech_pairing_of_incidenceTor :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) =
        incidenceTorCorrespondence T.hom X.hom V.hom a b ha hb ∧
      (β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)).val =
        finiteCyclePushforward m₂ (incidenceTorCycle T.hom X.hom V.hom a b hb) := by
  obtain ⟨β, h₁, h₂, _⟩ := exists_cech_pairing_of_incidenceTor_with_point_lift
    k a b ha hb m₂ q hs ht
  exact ⟨β, h₁, h₂⟩

end IncidenceTor

end AlgebraicGeometry.Cor
