/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CompositionHomotopyNaturality
public import Colib.KTheory.Waldhausen.Iterated.EndotransformationContraction
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumHomotopyNaturality
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumTransformationTransport


/-!
# Naturality of the original endotransformation contraction

Chosen-zero preservation and the universal properties of the actual zero objects identify the
original zero endotransformation under strict exact whiskering. The composition triangle and
uniform time operations then identify the existing cancellation expression pointwise. No new
contraction is chosen. Both homotopy times remain independent; degree zero retains its original
based-loop coordinate through the imported whole-level naturality statements.
-/
@[expose] public section

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology CategoryTheory.Functor Topology.LoopPrespectrum
open scoped Topology unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory SSet
universe u

/-- Exact heterogeneous equality of the original generic Eq.mp transport. -/
private theorem original_mp_heq {α β : Sort u} (e : α = β) (x : α) :
    HEq (Eq.mp e x) x := by
  cases e
  rfl

namespace Topology.LoopPrespectrum

/- The following private lemmas concern evaluation of existing operations. In particular,
   the cast lemma removes only endpoint-index transport, never either time coordinate. -/

private theorem comparison_apply_eq_of_heq {E B : LoopPrespectrum.{u}}
    {f g : E ⟶ B} {H K H' K' : Homotopy f g}
    (hH : H = H') (hK : K = K') (J : H.RelHomotopy K) (J' : H'.RelHomotopy K')
    (he : HEq J J') (n : ℕ) (r s : unitInterval) (x : E.space n) :
    J.level n (r, (s, x)) = J'.level n (r, (s, x)) := by
  subst hH
  subst hK
  cases he
  rfl

private theorem comparison_cast_apply {E B : LoopPrespectrum.{u}} {f g : E ⟶ B}
    {H K H' K' : Homotopy f g} (hH : H = H') (hK : K = K')
    (e : H.RelHomotopy K = H'.RelHomotopy K') (J : H.RelHomotopy K)
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (cast e J).level n (r, (s, x)) = J.level n (r, (s, x)) := by
  subst hH
  subst hK
  rfl

private theorem transRefl_eq_reparam {E B : LoopPrespectrum.{u}} {f g : E ⟶ B}
    (H : Homotopy f g) :
    H.trans (Homotopy.refl g) = H.reparam
      ⟨fun s ↦ ⟨Path.Homotopy.transReflReparamAux s,
        Path.Homotopy.transReflReparamAux_mem_I s⟩, by fun_prop⟩
      (Subtype.ext Path.Homotopy.transReflReparamAux_zero)
      (Subtype.ext Path.Homotopy.transReflReparamAux_one) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have hp := Path.Homotopy.trans_refl_reparam (H.path n x)
  rw [← Homotopy.path_refl g n x, ← Homotopy.path_trans] at hp
  exact DFunLike.congr_fun hp s

private theorem transAssoc_eq_reparam {E B : LoopPrespectrum.{u}} {f g h k : E ⟶ B}
    (H : Homotopy f g) (K : Homotopy g h) (L : Homotopy h k) :
    (H.trans K).trans L = (H.trans (K.trans L)).reparam
      ⟨fun s ↦ ⟨Path.Homotopy.transAssocReparamAux s,
        Path.Homotopy.transAssocReparamAux_mem_I s⟩, by fun_prop⟩
      (Subtype.ext Path.Homotopy.transAssocReparamAux_zero)
      (Subtype.ext Path.Homotopy.transAssocReparamAux_one) := by
  apply Homotopy.ext
  funext n
  apply ContinuousMap.ext
  rintro ⟨s, x⟩
  have hp := Path.Homotopy.trans_assoc_reparam (H.path n x) (K.path n x) (L.path n x)
  simp only [← Homotopy.path_trans] at hp
  exact DFunLike.congr_fun hp s

section Evaluation
variable {E B E' B' : LoopPrespectrum.{u}}
  {f g h k : E ⟶ B} {f' g' h' k' : E' ⟶ B'}
  {n : ℕ} {x : E.space n} {x' : E'.space n} {p : B.space n → B'.space n}

private theorem track_trans_natural
    {H : Homotopy f g} {K : Homotopy g h}
    {H' : Homotopy f' g'} {K' : Homotopy g' h'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x)))
    (hK : ∀ s, K'.level n (s, x') = p (K.level n (s, x))) :
    ∀ s, (H'.trans K').level n (s, x') = p ((H.trans K).level n (s, x)) := by
  intro s
  change ((H'.levelHomotopy n).trans (K'.levelHomotopy n)) (s, x') =
    p (((H.levelHomotopy n).trans (K.levelHomotopy n)) (s, x))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hH _
  · exact hK _

private theorem track_symm_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ s, H'.symm.level n (s, x') = p (H.symm.level n (s, x)) :=
  fun s ↦ hH (unitInterval.symm s)

private theorem comparison_refl_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.refl H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.refl H).level n (r, (s, x))) := fun _ s ↦ hH s

private theorem comparison_symm_natural
    {H K : Homotopy f g} {H' K' : Homotopy f' g'}
    {J : H.RelHomotopy K} {J' : H'.RelHomotopy K'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x)))) :
    ∀ r s, J'.symm.level n (r, (s, x')) = p (J.symm.level n (r, (s, x))) :=
  fun r s ↦ hJ (unitInterval.symm r) s

private theorem comparison_trans_natural
    {H K L : Homotopy f g} {H' K' L' : Homotopy f' g'}
    {J : H.RelHomotopy K} {M : K.RelHomotopy L}
    {J' : H'.RelHomotopy K'} {M' : K'.RelHomotopy L'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x))))
    (hM : ∀ r s, M'.level n (r, (s, x')) = p (M.level n (r, (s, x)))) :
    ∀ r s, (J'.trans M').level n (r, (s, x')) =
      p ((J.trans M).level n (r, (s, x))) := by
  intro r s
  change ((J'.level n).trans (M'.level n)) (r, (s, x')) =
    p (((J.level n).trans (M.level n)) (r, (s, x)))
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split
  · exact hJ _ s
  · exact hM _ s

private theorem comparison_hcomp_natural
    {H K : Homotopy f g} {L M : Homotopy g h}
    {H' K' : Homotopy f' g'} {L' M' : Homotopy g' h'}
    {J : H.RelHomotopy K} {N : L.RelHomotopy M}
    {J' : H'.RelHomotopy K'} {N' : L'.RelHomotopy M'}
    (hJ : ∀ r s, J'.level n (r, (s, x')) = p (J.level n (r, (s, x))))
    (hN : ∀ r s, N'.level n (r, (s, x')) = p (N.level n (r, (s, x)))) :
    ∀ r s, (J'.hcomp N').level n (r, (s, x')) =
      p ((J.hcomp N).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.hcomp
  change (ContinuousMap.Homotopy.trans _ _) (s, (r, x')) =
    p ((ContinuousMap.Homotopy.trans _ _) (s, (r, x)))
  rw [ContinuousMap.Homotopy.trans_apply, ContinuousMap.Homotopy.trans_apply]
  split
  · exact hJ r _
  · exact hN r _

private theorem comparison_transRefl_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.transRefl H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.transRefl H).level n (r, (s, x))) := by
  intro r s
  unfold Homotopy.RelHomotopy.transRefl
  simp only [eq_mp_eq_cast, comparison_cast_apply, transRefl_eq_reparam]
  exact hH _

private theorem comparison_transAssoc_natural
    {H : Homotopy f g} {K : Homotopy g h} {L : Homotopy h k}
    {H' : Homotopy f' g'} {K' : Homotopy g' h'} {L' : Homotopy h' k'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x)))
    (hK : ∀ s, K'.level n (s, x') = p (K.level n (s, x)))
    (hL : ∀ s, L'.level n (s, x') = p (L.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.transAssoc H' K' L').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.transAssoc H K L).level n (r, (s, x))) := by
  intro r s
  have hT := track_trans_natural hH (track_trans_natural hK hL)
  unfold Homotopy.RelHomotopy.transAssoc
  simp only [eq_mp_eq_cast, comparison_cast_apply, transAssoc_eq_reparam]
  exact hT _

private theorem comparison_reflTransSymm_natural
    {H : Homotopy f g} {H' : Homotopy f' g'}
    (hH : ∀ s, H'.level n (s, x') = p (H.level n (s, x))) :
    ∀ r s, (Homotopy.RelHomotopy.reflTransSymm H').level n (r, (s, x')) =
      p ((Homotopy.RelHomotopy.reflTransSymm H).level n (r, (s, x))) := by
  intro r s
  exact hH _

end Evaluation
end Topology.LoopPrespectrum

namespace CategoryTheory.Waldhausen.IteratedS

variable {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W)

/-- Mapping the two original arrows through the chosen zero gives the same zero endomorphism. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:203"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem zeroEndotransformation_postcomp (J : W ⟶ T) :
    whiskerRight (zeroEndotransformation F) J.hom.toFunctor =
      zeroEndotransformation (F ≫ J) := by
  ext A
  change J.hom.toFunctor.map (W.obj.waldhausen.isZero.from_ (F.hom.toFunctor.obj A) ≫
    W.obj.waldhausen.isZero.to_ (F.hom.toFunctor.obj A)) =
      T.obj.waldhausen.isZero.from_ (J.hom.toFunctor.obj (F.hom.toFunctor.obj A)) ≫
        T.obj.waldhausen.isZero.to_ (J.hom.toFunctor.obj (F.hom.toFunctor.obj A))
  have h₀ : J.hom.toFunctor.map (W.obj.waldhausen.isZero.from_ (F.hom.toFunctor.obj A)) =
      T.obj.waldhausen.isZero.from_ (J.hom.toFunctor.obj (F.hom.toFunctor.obj A)) ≫
        eqToHom J.property.symm := (J.hom.isExact.zero W.obj.waldhausen.isZero).eq_of_tgt _ _
  have h₁ : J.hom.toFunctor.map (W.obj.waldhausen.isZero.to_ (F.hom.toFunctor.obj A)) =
      eqToHom J.property ≫ T.obj.waldhausen.isZero.to_ (J.hom.toFunctor.obj (F.hom.toFunctor.obj
        A)) :=
    (J.hom.isExact.zero W.obj.waldhausen.isZero).eq_of_src _ _
  rw [Functor.map_comp, h₀, h₁]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- Prewhiskering retains the literal two-arrow factorization through the chosen target zero. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:221"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem zeroEndotransformation_precomp (J : T ⟶ V) :
    whiskerLeft J.hom.toFunctor (zeroEndotransformation F) =
      zeroEndotransformation (J ≫ F) := rfl

/-- Precomposition preserves weakness of the actual chosen zero endotransformation. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:226"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem zeroEndotransformation_precomp_weak
    (hz : ∀ A, W.obj.waldhausen.weq
      ((zeroEndotransformation (V := V) (W := W) F).app A)) (J : T ⟶ V) :
    ∀ A : T.obj.Obj, W.obj.waldhausen.weq
      ((zeroEndotransformation (V := T) (W := W) (J ≫ F)).app A) := by
  intro A
  rw [← zeroEndotransformation_precomp F J]
  exact hz (J.hom.toFunctor.obj A)

/-- Exact postcomposition preserves weakness of the actual chosen-zero endotransformation. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:236"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem zeroEndotransformation_postcomp_weak
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : W ⟶ T) :
    ∀ A, T.obj.waldhausen.weq ((zeroEndotransformation (F ≫ J)).app A) := by
  intro A
  rw [← zeroEndotransformation_postcomp F J]
  exact J.hom.isExact.weak _ (hz A)

/-- Equal original weak transformations retain their exact whole source track. -/
private theorem absorption_source_eq_via_levels
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) :
    prespectrumTransformationHomotopy (F := F) (G := F)
      (η ≫ zeroEndotransformation F)
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hz A)) =
    prespectrumTransformationHomotopy (F := F) (G := F)
      (zeroEndotransformation F) hz := by
  apply Topology.LoopPrespectrum.Homotopy.ext
  funext m
  exact prespectrumTransformationHomotopy_level_eq_of_heq
    (F := F) (F' := F) (G := F) (G' := F) rfl rfl
    (η ≫ zeroEndotransformation F) (zeroEndotransformation F)
    (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hz A)) hz
    (heq_of_eq (zeroEndotransformation_absorb F η)) m

/-- The original absorption triangle is the actual endpoint cast of its original comparison. -/
private theorem absorption_heq_via_delta_mp_explicit
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) :
    HEq (prespectrumEndotransformationAbsorptionTriangle F η hη hz)
      (prespectrumTransformationCompositionHomotopy (F := F) (G := F) (H := F) η
        (zeroEndotransformation F) hη hz) := by
  delta prespectrumEndotransformationAbsorptionTriangle
  exact original_mp_heq
    (α := (prespectrumTransformationHomotopy (F := F) (G := F)
      (η ≫ zeroEndotransformation F)
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hz A))).RelHomotopy
        ((prespectrumTransformationHomotopy (F := F) (G := F) η hη).trans
          (prespectrumTransformationHomotopy (F := F) (G := F)
            (zeroEndotransformation F) hz)))
    (β := (prespectrumTransformationHomotopy (F := F) (G := F)
      (zeroEndotransformation F) hz).RelHomotopy
        ((prespectrumTransformationHomotopy (F := F) (G := F) η hη).trans
          (prespectrumTransformationHomotopy (F := F) (G := F)
            (zeroEndotransformation F) hz)))
    _ (prespectrumTransformationCompositionHomotopy (F := F) (G := F) (H := F) η
      (zeroEndotransformation F) hη hz)

/-- The absorption identification changes no point of the original composition triangle. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:284"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationAbsorptionTriangle_apply
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationAbsorptionTriangle F η hη hz).level n (r, (s, x)) =
      (prespectrumTransformationCompositionHomotopy (F := F) (G := F) (H := F) η
        (zeroEndotransformation F) hη hz).level n (r, (s, x)) := by
  exact Topology.LoopPrespectrum.comparison_apply_eq_of_heq
    (E := prespectrum V) (B := prespectrum W)
    (f := prespectrumMap F) (g := prespectrumMap F)
    (H := prespectrumTransformationHomotopy (F := F) (G := F)
      (zeroEndotransformation F) hz)
    (H' := prespectrumTransformationHomotopy (F := F) (G := F)
      (η ≫ zeroEndotransformation F)
      (fun A ↦ W.obj.waldhausen.weq.comp_mem _ _ (hη A) (hz A)))
    (K := (prespectrumTransformationHomotopy (F := F) (G := F) η hη).trans
      (prespectrumTransformationHomotopy (F := F) (G := F)
        (zeroEndotransformation F) hz))
    (K' := (prespectrumTransformationHomotopy (F := F) (G := F) η hη).trans
      (prespectrumTransformationHomotopy (F := F) (G := F)
        (zeroEndotransformation F) hz))
    (absorption_source_eq_via_levels F η hη hz).symm rfl
    (prespectrumEndotransformationAbsorptionTriangle F η hη hz)
    (prespectrumTransformationCompositionHomotopy (F := F) (G := F) (H := F) η
      (zeroEndotransformation F) hη hz)
    (absorption_heq_via_delta_mp_explicit F η hη hz) n r s x

/-- Equality of the actual second transformation preserves its original triangle at every point. -/
private theorem composition_point_eq_of_eq
    {V' W' : WideSubcategory preservesZero.{u}} {F' G' H' : V' ⟶ W'}
    (η : F'.hom.toFunctor ⟶ G'.hom.toFunctor) (θ θ' : G'.hom.toFunctor ⟶ H'.hom.toFunctor)
    (hη : ∀ A, W'.obj.waldhausen.weq (η.app A))
    (hθ : ∀ A, W'.obj.waldhausen.weq (θ.app A))
    (hθ' : ∀ A, W'.obj.waldhausen.weq (θ'.app A)) (he : θ = θ')
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V').space n) :
    (prespectrumTransformationCompositionHomotopy (F := F') (G := G') (H := H')
      η θ hη hθ).level n (r, (s, x)) =
    (prespectrumTransformationCompositionHomotopy (F := F') (G := G') (H := H')
      η θ' hη hθ').level n (r, (s, x)) := by
  subst θ'
  rfl

/-- The original absorption triangle commutes with exact postcomposition at both times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:327"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationAbsorptionTriangle_postcomp_level
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : W ⟶ T)
    (hz' : ∀ A, T.obj.waldhausen.weq ((zeroEndotransformation (F ≫ J)).app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationAbsorptionTriangle (F ≫ J) (whiskerRight η J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) hz').level n (r, (s, x)) =
      (prespectrumMap J).map n
        ((prespectrumEndotransformationAbsorptionTriangle F η hη hz).level n (r, (s, x))) := by
  rw [prespectrumEndotransformationAbsorptionTriangle_apply,
    prespectrumEndotransformationAbsorptionTriangle_apply]
  have hpoint := composition_point_eq_of_eq
    (F' := F ≫ J) (G' := F ≫ J) (H' := F ≫ J)
    (whiskerRight η J.hom.toFunctor)
    (whiskerRight (zeroEndotransformation F) J.hom.toFunctor)
    (zeroEndotransformation (F ≫ J))
    (fun A ↦ J.hom.isExact.weak _ (hη A)) (fun A ↦ J.hom.isExact.weak _ (hz A)) hz'
    (zeroEndotransformation_postcomp F J) n r s x
  exact hpoint.symm.trans
    (prespectrumTransformationCompositionHomotopy_postcomp_level
      (F := F) (G := F) (H := F) η (zeroEndotransformation F) hη hz J n r s x)

/-- The original absorption triangle commutes with exact precomposition at both times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:350"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationAbsorptionTriangle_precomp_level
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : T ⟶ V)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationAbsorptionTriangle (J ≫ F) (whiskerLeft J.hom.toFunctor η)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hz (J.hom.toFunctor.obj A))).level n (r, (s,
        x)) =
      (prespectrumEndotransformationAbsorptionTriangle F η hη hz).level n
        (r, (s, (prespectrumMap J).map n x)) := by
  rw [prespectrumEndotransformationAbsorptionTriangle_apply,
    prespectrumEndotransformationAbsorptionTriangle_apply]
  exact prespectrumTransformationCompositionHomotopy_precomp_level
    (F := F) (G := F) (H := F) η
    (zeroEndotransformation F) hη hz J n r s x

section CancellationEvaluation
variable {V' W' : WideSubcategory preservesZero.{u}} {F' : V' ⟶ W'}
  {η : F.hom.toFunctor ⟶ F.hom.toFunctor} {η' : F'.hom.toFunctor ⟶ F'.hom.toFunctor}
  {hη : ∀ A, W.obj.waldhausen.weq (η.app A)} {hη' : ∀ A, W'.obj.waldhausen.weq (η'.app A)}
  {hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)}
  {hz' : ∀ A, W'.obj.waldhausen.weq ((zeroEndotransformation F').app A)}

/-- Pointwise compatibility propagates through the unchanged original cancellation expression. -/
private theorem contraction_evaluation_natural
    {n : ℕ} {x : (prespectrum V).space n} {x' : (prespectrum V').space n}
    {p : (prespectrum W).space n → (prespectrum W').space n}
    (hH : ∀ s, (prespectrumTransformationHomotopy (F := F') (G := F') η' hη').level n (s, x') =
      p ((prespectrumTransformationHomotopy (F := F) (G := F) η hη).level n (s, x)))
    (hZ : ∀ s, (prespectrumTransformationHomotopy (F := F') (G := F')
      (zeroEndotransformation F') hz').level n
      (s, x') = p ((prespectrumTransformationHomotopy (F := F) (G := F)
        (zeroEndotransformation F) hz).level n (s, x)))
    (hJ : ∀ r s, (prespectrumEndotransformationAbsorptionTriangle F' η' hη' hz').level n
      (r, (s, x')) =
      p ((prespectrumEndotransformationAbsorptionTriangle F η hη hz).level n (r, (s, x)))) :
    ∀ r s, (prespectrumEndotransformationContraction F' η' hη' hz').level n (r, (s, x')) =
      p ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) := by
  unfold prespectrumEndotransformationContraction
  apply comparison_trans_natural
  · exact comparison_symm_natural (comparison_transRefl_natural hH)
  · apply comparison_trans_natural
    · exact comparison_hcomp_natural (comparison_refl_natural hH)
        (comparison_reflTransSymm_natural hZ)
    · apply comparison_trans_natural
      · exact comparison_symm_natural
          (comparison_transAssoc_natural hH hZ (track_symm_natural hZ))
      · apply comparison_trans_natural
        · exact comparison_hcomp_natural (comparison_symm_natural hJ)
            (comparison_refl_natural (track_symm_natural hZ))
        · exact comparison_symm_natural (comparison_reflTransSymm_natural hZ)

end CancellationEvaluation

/-- Exact postcomposition preserves the specified original contraction at all levels and times.
The target weak-zero witness is arbitrary, so this applies to the canonical transported witness. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:404"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationContraction_postcomp_level
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : W ⟶ T)
    (hz' : ∀ A, T.obj.waldhausen.weq ((zeroEndotransformation (F ≫ J)).app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (F ≫ J) (whiskerRight η J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) hz').level n (r, (s, x)) =
      (prespectrumMap J).map n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))) := by
  refine contraction_evaluation_natural F
    (F' := F ≫ J) (η := η) (η' := whiskerRight η J.hom.toFunctor)
    (hη := hη) (hη' := fun A ↦ J.hom.isExact.weak _ (hη A))
    (hz := hz) (hz' := hz') (n := n) (x := x) (x' := x)
    (p := (prespectrumMap J).map n) ?_ ?_ ?_ r s
  · intro t
    exact congrArg (fun K ↦ K (t, x))
      (prespectrumTransformationHomotopy_postcomp_level (F := F) (G := F) η hη J n)
  · intro t
    have he := prespectrumTransformationHomotopy_level_eq_of_heq
      (F := F ≫ J) (F' := F ≫ J) (G := F ≫ J) (G' := F ≫ J) rfl rfl
      (whiskerRight (zeroEndotransformation F) J.hom.toFunctor)
      (zeroEndotransformation (F ≫ J))
      (fun A ↦ J.hom.isExact.weak _ (hz A)) hz'
      (heq_of_eq (zeroEndotransformation_postcomp F J)) n
    have hZ := congrArg (fun K ↦ K (t, x))
      (prespectrumTransformationHomotopy_postcomp_level
        (F := F) (G := F) (zeroEndotransformation F) hz J n)
    exact (congrArg (fun K ↦ K (t, x)) he).symm.trans hZ
  · exact fun a b ↦
      prespectrumEndotransformationAbsorptionTriangle_postcomp_level F η hη hz J hz' n a b x


/-- Equal original transformations retain the same chosen contraction at both times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:437"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationContraction_level_eq_of_heq
    {V W : WideSubcategory preservesZero.{u}} {F F' : V ⟶ W} (h : F = F')
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (η' : F'.hom.toFunctor ⟶ F'.hom.toFunctor)
    (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hη' : ∀ X, W.obj.waldhausen.weq (η'.app X))
    (hz : ∀ X, W.obj.waldhausen.weq ((zeroEndotransformation F).app X))
    (hz' : ∀ X, W.obj.waldhausen.weq ((zeroEndotransformation F').app X))
    (he : HEq η η') (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x)) =
      (prespectrumEndotransformationContraction F' η' hη' hz').level n (r, (s, x)) := by
  cases h
  have hηeq : η = η' := eq_of_heq he
  cases hηeq
  have hw : hη = hη' := Subsingleton.elim _ _
  cases hw
  have hwz : hz = hz' := Subsingleton.elim _ _
  cases hwz
  rfl

/-- Point evaluation of the unchanged whole precomposition equation. -/
private theorem originalPrecompositionTrack_apply
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (J : T ⟶ V) (n : ℕ) (s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumTransformationHomotopy (F := J ≫ F) (G := J ≫ F)
      (whiskerLeft J.hom.toFunctor η) (fun A ↦ hη (J.hom.toFunctor.obj A))).level n (s, x) =
    (prespectrumTransformationHomotopy (F := F) (G := F) η hη).level n
      (s, (prespectrumMap (V := T) (W := V) J).map n x) := by
  exact congrArg
    (fun K : C(unitInterval × (prespectrum T).space n, (prespectrum W).space n) ↦ K (s, x))
    (prespectrumTransformationHomotopy_precomp_level (F := F) (G := F) η hη J n)

/-- The original zero self-track precomposes at every original time. -/
private theorem originalZeroPrecompositionTrack_apply
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A))
    (J : T ⟶ V) (n : ℕ) (s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumTransformationHomotopy (F := J ≫ F) (G := J ≫ F)
      (zeroEndotransformation (V := T) (W := W) (J ≫ F))
      (zeroEndotransformation_precomp_weak F hz J)).level n (s, x) =
    (prespectrumTransformationHomotopy (F := F) (G := F)
      (zeroEndotransformation F) hz).level n
      (s, (prespectrumMap (V := T) (W := V) J).map n x) := by
  have he := prespectrumTransformationHomotopy_level_eq_of_heq
    (F := J ≫ F) (F' := J ≫ F) (G := J ≫ F) (G' := J ≫ F) rfl rfl
    (whiskerLeft J.hom.toFunctor (zeroEndotransformation F))
    (zeroEndotransformation (V := T) (W := W) (J ≫ F))
    (fun A ↦ hz (J.hom.toFunctor.obj A)) (zeroEndotransformation_precomp_weak F hz J)
    (heq_of_eq (zeroEndotransformation_precomp F J)) n
  have hpoint := congrArg
    (fun K : C(unitInterval × (prespectrum T).space n, (prespectrum W).space n) ↦ K (s, x)) he
  exact hpoint.symm.trans
    (originalPrecompositionTrack_apply F (zeroEndotransformation F) hz J n s x)

/-- Proof-irrelevant weakness witnesses retain every value of the same chosen triangle. -/
private theorem absorptionWeakWitness_apply
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz hz' : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationAbsorptionTriangle (V := V) (W := W)
      F η hη hz).level n (r, (s, x)) =
    (prespectrumEndotransformationAbsorptionTriangle (V := V) (W := W)
      F η hη hz').level n (r, (s, x)) := by
  have h : hz = hz' := Subsingleton.elim _ _
  cases h
  rfl

/-- Both original absorption times retain the same triangle after precomposition. -/
private theorem originalAbsorptionPrecomposition_apply
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A))
    (J : T ⟶ V) (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationAbsorptionTriangle (V := T) (W := W)
      (J ≫ F) (whiskerLeft J.hom.toFunctor η) (fun A ↦ hη (J.hom.toFunctor.obj A))
      (zeroEndotransformation_precomp_weak F hz J)).level n (r, (s, x)) =
    (prespectrumEndotransformationAbsorptionTriangle (V := V) (W := W)
      F η hη hz).level n (r, (s, (prespectrumMap (V := T) (W := V) J).map n x)) := by
  have hpoint := absorptionWeakWitness_apply (V := T) (W := W)
    (J ≫ F) (whiskerLeft J.hom.toFunctor η) (fun A ↦ hη (J.hom.toFunctor.obj A))
    (zeroEndotransformation_precomp_weak F hz J) (fun A ↦ hz (J.hom.toFunctor.obj A))
    n r s x
  exact hpoint.trans
    (prespectrumEndotransformationAbsorptionTriangle_precomp_level
      (V := V) (W := W) (T := T) F η hη hz J n r s x)

/-- Exact precomposition preserves the specified original contraction at all levels and times. -/
private theorem contraction_precomp_named_weak
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : T ⟶ V)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationContraction (V := T) (W := W) (J ≫ F) (whiskerLeft
      J.hom.toFunctor η)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (zeroEndotransformation_precomp_weak F hz J)).level n
        (r, (s, x)) =
      (prespectrumEndotransformationContraction (V := V) (W := W) F η hη hz).level n
        (r, (s, (prespectrumMap (V := T) (W := V) J).map n x)) := by
  exact contraction_evaluation_natural (V := V) (W := W) (V' := T) (W' := W) F
    (F' := J ≫ F) (η := η) (η' := whiskerLeft J.hom.toFunctor η)
    (hη := hη) (hη' := fun A ↦ hη (J.hom.toFunctor.obj A))
    (hz := hz) (hz' := zeroEndotransformation_precomp_weak F hz J)
    (n := n) (x := (prespectrumMap (V := T) (W := V) J).map n x)
    (x' := x) (p := fun y : (prespectrum W).space n ↦ y)
    (fun t ↦ originalPrecompositionTrack_apply (V := V) (W := W) (T := T) F η hη J n t x)
    (fun t ↦ originalZeroPrecompositionTrack_apply (V := V) (W := W) (T := T) F hz J n t x)
    (fun a b ↦ originalAbsorptionPrecomposition_apply
      (V := V) (W := W) (T := T) F η hη hz J n a b x) r s

/-- Exact precomposition preserves the specified original contraction at all levels and times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:542"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationContraction_precomp_level
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : T ⟶ V)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationContraction (J ≫ F) (whiskerLeft J.hom.toFunctor η)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hz (J.hom.toFunctor.obj A))).level n (r, (s,
        x)) =
      (prespectrumEndotransformationContraction F η hη hz).level n
        (r, (s, (prespectrumMap J).map n x)) := by
  have hc := prespectrumEndotransformationContraction_level_eq_of_heq
    (V := T) (W := W) (F := J ≫ F) (F' := J ≫ F) rfl
    (whiskerLeft J.hom.toFunctor η) (whiskerLeft J.hom.toFunctor η)
    (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hη (J.hom.toFunctor.obj A))
    (fun A ↦ hz (J.hom.toFunctor.obj A)) (zeroEndotransformation_precomp_weak F hz J)
    (HEq.rfl) n r s x
  exact hc.trans (contraction_precomp_named_weak F η hη hz J n r s x)

end CategoryTheory.Waldhausen.IteratedS
