/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-!
# Actual finite supports in an étale Čech relation

Two finite images of one integral scheme, with equal source maps and equal
postcomposed target maps, give a finite correspondence to the actual Čech
pullback. Its two graph composites retain the original residue degrees. Every
point of each native integral support of the result lifts to the original
scheme, not just to a generic point or a residue-field extension.

The construction also records the literal common-support map for the generic
coefficient and original incidence Tor consumer. No target map is assumed finite.
The source scheme in that construction is arbitrary, including nonreduced schemes.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/Cech/SupportPairing.lean`.
Native `finiteCorrespondences`, `integralComponentAt` and `finiteCyclePushforward`
replace the custom integral-cycle and generator presentations. The integral-source
endpoint does not need the original Noetherian hypothesis. This is a support
pairing, not local exactness or the existence of compatible Nisnevich sections.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open Function.locallyFinsuppWithin

attribute [local instance] isIntegral_integralComponentAt
attribute [local instance] Classical.propDecidable

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {T Y V : Scheme.SmoothSite (Spec (.of k))}

section CommonMap

variable (W : Scheme.{u}) (m₁ m₂ : W ⟶ pullback T.hom V.hom)
  (q : V ⟶ Y) [Etale q.left]
  (hs : m₁ ≫ pullback.fst T.hom V.hom = m₂ ≫ pullback.fst T.hom V.hom)
  (ht : m₁ ≫ pullback.snd T.hom V.hom ≫ q.left =
    m₂ ≫ pullback.snd T.hom V.hom ≫ q.left)

/-- The literal map from the whole common support to the source times the Čech pullback. -/
def cechSupportMap : W ⟶ pullback T.hom (Scheme.SmoothSite.etalePullback q q).hom :=
  pullback.lift (m₁ ≫ pullback.fst T.hom V.hom)
    (pullback.lift (m₁ ≫ pullback.snd T.hom V.hom)
      (m₂ ≫ pullback.snd T.hom V.hom)
        (by simpa only [Category.assoc] using ht)) (by
        change _ = (pullback.lift _ _ _) ≫ (pullback.snd q.left q.left ≫ V.hom)
        rw [← Category.assoc, pullback.lift_snd, hs]
        simp only [Category.assoc, pullback.condition])

@[reassoc]
theorem cechSupportMap_fst :
    cechSupportMap k W m₁ m₂ q hs ht ≫
      pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom =
      m₁ ≫ pullback.fst T.hom V.hom := by
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem cechSupportMap_snd_fst :
    cechSupportMap k W m₁ m₂ q hs ht ≫
      pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
      (Scheme.SmoothSite.etalePullbackFst q q).left =
      m₁ ≫ pullback.snd T.hom V.hom := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f : W ⟶ pullback q.left q.left => f ≫ pullback.fst q.left q.left)
      (pullback.lift_snd _ _ _)).trans (pullback.lift_fst _ _ _))

@[reassoc]
theorem cechSupportMap_snd_snd :
    cechSupportMap k W m₁ m₂ q hs ht ≫
      pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
      (Scheme.SmoothSite.etalePullbackSnd q q).left =
      m₂ ≫ pullback.snd T.hom V.hom := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f : W ⟶ pullback q.left q.left => f ≫ pullback.snd q.left q.left)
      (pullback.lift_snd _ _ _)).trans (pullback.lift_snd _ _ _))

instance cechSupportMap_isFinite [IsFinite (m₁ ≫ pullback.fst T.hom V.hom)] :
    IsFinite (cechSupportMap k W m₁ m₂ q hs ht) := by
  have : IsFinite (cechSupportMap k W m₁ m₂ q hs ht ≫
      pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom) := by
    rw [cechSupportMap_fst]
    infer_instance
  exact IsFinite.of_comp _ (pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom)

/-- The first projection is the actual original finite support map. -/
theorem cechSupportMap_graph_fst :
    cechSupportMap k W m₁ m₂ q hs ht ≫
      pullback.map T.hom (Scheme.SmoothSite.etalePullback q q).hom T.hom V.hom
        (𝟙 T.left) (Scheme.SmoothSite.etalePullbackFst q q).left (𝟙 _)
        (by simp) (by simpa using
          (MorphismProperty.Over.w (Scheme.SmoothSite.etalePullbackFst q q)).symm) = m₁ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst]
    exact (Category.assoc _ _ _).symm.trans
      ((Category.comp_id _).trans (cechSupportMap_fst k W m₁ m₂ q hs ht))
  · simpa only [Category.assoc, pullback.map, pullback.lift_snd] using
      cechSupportMap_snd_fst k W m₁ m₂ q hs ht

/-- The second projection is the other original finite support map. -/
theorem cechSupportMap_graph_snd :
    cechSupportMap k W m₁ m₂ q hs ht ≫
      pullback.map T.hom (Scheme.SmoothSite.etalePullback q q).hom T.hom V.hom
        (𝟙 T.left) (Scheme.SmoothSite.etalePullbackSnd q q).left (𝟙 _)
        (by simp) (by simpa using
          (MorphismProperty.Over.w (Scheme.SmoothSite.etalePullbackSnd q q)).symm) = m₂ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst]
    exact (Category.assoc _ _ _).symm.trans
      ((Category.comp_id _).trans ((cechSupportMap_fst k W m₁ m₂ q hs ht).trans hs))
  · simpa only [Category.assoc, pullback.map, pullback.lift_snd] using
      cechSupportMap_snd_snd k W m₁ m₂ q hs ht

/-- Every point of every surviving integral image support lifts to the whole
original scheme. Cancellation and coincident images do not weaken this statement. -/
theorem cechSupportMap_point_lift [IsFinite (m₁ ≫ pullback.fst T.hom V.hom)]
    (c : AlgebraicCycle W ℤ)
    (β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q))
    (hβ : β.val = finiteCyclePushforward (cechSupportMap k W m₁ m₂ q hs ht) c) :
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
  intro b hb z
  let m := cechSupportMap k W m₁ m₂ q hs ht
  have hb' : b ∈ (finiteCyclePushforward m c).support := by
    change finiteCyclePushforward m c b ≠ 0
    rw [← hβ]
    exact hb
  obtain ⟨x, _, hx⟩ := finiteCyclePushforward_support_subset m c hb'
  have hz : (integralComponentAt b).subschemeι z ∈
      ((integralComponentAt b).support : Set (pullback (C := Scheme) T.hom
        (Scheme.SmoothSite.etalePullback q q).hom)) := by
    rw [← (integralComponentAt b).range_subschemeι]
    exact ⟨z, rfl⟩
  have himage := finiteCyclePushforward_image_support m x
  rw [hx] at himage
  rw [← himage] at hz
  obtain ⟨w, _, hw⟩ := hz
  refine ⟨w, ?_, ?_, ?_⟩
  · have he := congrArg (fun f : W ⟶ T.left => f w)
      (cechSupportMap_fst k W m₁ m₂ q hs ht)
    change (pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom) (m w) = _ at he
    rw [hw] at he
    exact he.symm
  · have he := congrArg (fun f : W ⟶ V.left => f w)
      (cechSupportMap_snd_fst k W m₁ m₂ q hs ht)
    change (Scheme.SmoothSite.etalePullbackFst q q).left
      ((pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom) (m w)) = _ at he
    rw [hw] at he
    exact he.symm
  · have he := congrArg (fun f : W ⟶ V.left => f w)
      (cechSupportMap_snd_snd k W m₁ m₂ q hs ht)
    change (Scheme.SmoothSite.etalePullbackSnd q q).left
      ((pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom) (m w)) = _ at he
    rw [hw] at he
    exact he.symm

end CommonMap

section IntegralImage

variable (D : Scheme.{u}) [IsIntegral D]
  (m : D ⟶ pullback T.hom V.hom) [IsFinite m]
  [IsFinite (m ≫ pullback.fst T.hom V.hom)]
  (hm : Set.range (m ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)

include hm in
/-- The generic image of an actual integral finite support is admissible. -/
theorem isFiniteCorrespondencePoint_supportImage :
    IsFiniteCorrespondencePoint T.hom V.hom (m (genericPoint D)) := by
  apply isFiniteCorrespondencePoint_finiteMap T.hom V.hom m (genericPoint D)
  · rw [Category.assoc]
    infer_instance
  · simp only [Category.assoc, finiteCyclePushforward_range_integralComponentAt,
      coe_support_integralComponentAt, genericPoint_closure, Set.image_univ]
    change Set.range (m ≫ pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left
    exact hm

/-- The native prime image weighted by its actual residue degree. -/
def weightedSupportImage : Cor.mk T ⟶ Cor.mk V :=
  singleFiniteCorrespondence T.hom V.hom (m (genericPoint D))
    (isFiniteCorrespondencePoint_supportImage k D m hm) (m.residueDegree (genericPoint D) : ℤ)

/-- Forgetting admissibility gives the exact finite pushforward of the integral prime cycle. -/
theorem weightedSupportImage_val :
    (weightedSupportImage k D m hm).val =
      finiteCyclePushforward m (single (genericPoint D) 1) := by
  rw [finiteCyclePushforward_single, one_mul]
  rfl

end IntegralImage

section IntegralPairing

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

include hs ht

/-- The actual Čech pair has both degree-weighted graph composites and a lift for
every point of every surviving support component. No reduced-support replacement is made. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/Cech/SupportPairing.lean: \
exists_cech_pairing_of_common_support_with_point_lift"
  "adaptation" "native finite images, both graph composites, actual support-point lifts and \
residue degrees"]
theorem exists_cech_pairing_of_common_support_with_point_lift :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) =
        weightedSupportImage k D m₁ hm₁ ∧
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) =
        weightedSupportImage k D m₂ hm₂ ∧
      ∀ b, β.val b ≠ 0 → ∀ z : (integralComponentAt b).subscheme, ∃ d : D,
        (m₁ ≫ pullback.fst T.hom V.hom) d =
          ((integralComponentAt b).subschemeι ≫
            pullback.fst T.hom (Scheme.SmoothSite.etalePullback q q).hom) z ∧
        (m₁ ≫ pullback.snd T.hom V.hom) d =
          ((integralComponentAt b).subschemeι ≫
            pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
            (Scheme.SmoothSite.etalePullbackFst q q).left) z ∧
        (m₂ ≫ pullback.snd T.hom V.hom) d =
          ((integralComponentAt b).subschemeι ≫
            pullback.snd T.hom (Scheme.SmoothSite.etalePullback q q).hom ≫
            (Scheme.SmoothSite.etalePullbackSnd q q).left) z := by
  let P := Scheme.SmoothSite.etalePullback q q
  let m : D ⟶ pullback T.hom P.hom := cechSupportMap k D m₁ m₂ q hs ht
  let : IsFinite m := cechSupportMap_isFinite k D m₁ m₂ q hs ht
  have hm : m ≫ pullback.fst T.hom P.hom = m₁ ≫ pullback.fst T.hom V.hom :=
    cechSupportMap_fst k D m₁ m₂ q hs ht
  have : IsFinite (m ≫ pullback.fst T.hom P.hom) := by rw [hm]; infer_instance
  have hmr : Set.range (m ≫ pullback.fst T.hom P.hom) ∈ irreducibleComponents T.left := by
    rw [hm]
    exact hm₁
  refine ⟨weightedSupportImage k (T := T) (V := P) D m hmr, ?_, ?_, ?_⟩
  · apply Subtype.ext
    change (incidenceTorPairing T.hom P.hom V.hom
      (weightedSupportImage k (T := T) (V := P) D m hmr)
      (graphCorrespondenceOfComponents P.hom V.hom
        (Scheme.SmoothSite.etalePullbackFst q q).left
        (MorphismProperty.Over.w (Scheme.SmoothSite.etalePullbackFst q q))
        (finite_genericPoints k (Cor.mk P)))).val = (weightedSupportImage k D m₁ hm₁).val
    rw [weightedSupportImage_val]
    simpa only [weightedSupportImage, one_mul] using
      incidenceTorPairing_finiteImage_single_graph_right_val T.hom P.hom V.hom
        (Scheme.SmoothSite.etalePullbackFst q q).left
        (MorphismProperty.Over.w (Scheme.SmoothSite.etalePullbackFst q q))
        (finite_genericPoints k (Cor.mk P)) m m₁
        (cechSupportMap_graph_fst k D m₁ m₂ q hs ht) (genericPoint D)
        (isFiniteCorrespondencePoint_supportImage k D m hmr) 1
  · apply Subtype.ext
    change (incidenceTorPairing T.hom P.hom V.hom
      (weightedSupportImage k (T := T) (V := P) D m hmr)
      (graphCorrespondenceOfComponents P.hom V.hom
        (Scheme.SmoothSite.etalePullbackSnd q q).left
        (MorphismProperty.Over.w (Scheme.SmoothSite.etalePullbackSnd q q))
        (finite_genericPoints k (Cor.mk P)))).val = (weightedSupportImage k D m₂ hm₂).val
    rw [weightedSupportImage_val]
    simpa only [weightedSupportImage, one_mul] using
      incidenceTorPairing_finiteImage_single_graph_right_val T.hom P.hom V.hom
        (Scheme.SmoothSite.etalePullbackSnd q q).left
        (MorphismProperty.Over.w (Scheme.SmoothSite.etalePullbackSnd q q))
        (finite_genericPoints k (Cor.mk P)) m m₂
        (cechSupportMap_graph_snd k D m₁ m₂ q hs ht) (genericPoint D)
        (isFiniteCorrespondencePoint_supportImage k D m hmr) 1
  · exact cechSupportMap_point_lift k D m₁ m₂ q hs ht
      (single (genericPoint D) 1) _ (weightedSupportImage_val k D m hmr)

/-- The same constructed pair, retaining its two actual graph composites. -/
theorem exists_cech_pairing_of_common_support :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) =
        weightedSupportImage k D m₁ hm₁ ∧
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) =
        weightedSupportImage k D m₂ hm₂ := by
  obtain ⟨β, h₁, h₂, _⟩ := exists_cech_pairing_of_common_support_with_point_lift
    k D m₁ m₂ hm₁ hm₂ q hs ht
  exact ⟨β, h₁, h₂⟩

/-- Arbitrary signed multiplicities survive the first-minus-second Čech boundary. -/
theorem exists_cech_boundary_of_common_support (n : ℤ) :
    ∃ β : Cor.mk T ⟶ Cor.mk (Scheme.SmoothSite.etalePullback q q),
      β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q) -
        β ≫ (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q) =
      n • (weightedSupportImage k D m₁ hm₁ - weightedSupportImage k D m₂ hm₂) := by
  obtain ⟨β, h₁, h₂⟩ := exists_cech_pairing_of_common_support k D m₁ m₂ hm₁ hm₂ q hs ht
  let γ : Cor.mk (Scheme.SmoothSite.etalePullback q q) ⟶ Cor.mk V :=
    (graphFunctor k).map (Scheme.SmoothSite.etalePullbackFst q q)
  let δ : Cor.mk (Scheme.SmoothSite.etalePullback q q) ⟶ Cor.mk V :=
    (graphFunctor k).map (Scheme.SmoothSite.etalePullbackSnd q q)
  change β ≫ γ = weightedSupportImage k D m₁ hm₁ at h₁
  change β ≫ δ = weightedSupportImage k D m₂ hm₂ at h₂
  refine ⟨n • β, ?_⟩
  change (n • β) ≫ γ - (n • β) ≫ δ = _
  rw [Preadditive.zsmul_comp, Preadditive.zsmul_comp, h₁, h₂, smul_sub]

end IntegralPairing

end AlgebraicGeometry.Cor
