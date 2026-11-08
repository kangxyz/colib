/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.WeakArrow.JointFunctor
public import Colib.CategoryTheory.Waldhausen.WeakArrow.DualDetection
public import Colib.CategoryTheory.Waldhausen.ArrowCategory.Exact
public import Colib.CategoryTheory.Waldhausen.ExtensionCategory.HeterogeneousDetection
/-! # Genuine exactness of coherent opposite weak-arrow joint cylinders

Both original projections detect the actual zero objects and pushouts. For
cofibrations, the proof uses the genuine relative pushout map rather than
pointwise cofibration alone.

Implementation provenance: `Quillen/Waldhausen/WeakArrow/JointExact.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The original hypotheses, functors, component maps and independent universes are retained.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v u' v'
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CategoryTheory.Waldhausen.WeakArrow
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (V : Structure C) (W : Structure D) (Vd : Structure Cᵒᵖ) (Wd : Structure Dᵒᵖ)
  (F : C ⥤ D) (hF : IsExact V.cof V.weq W.cof W.weq F)
  (hFd : IsExact Vd.cof Vd.weq Wd.cof Wd.weq F.op)
  (hW : IsCompatibleDual W Wd)
  (Tc : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Vd))
  (Td : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl Wd))
  (compat : Tc.joint ⋙ ExtensionCategory.postcompose Vd Wd hFd ≅ F.op.mapArrow ⋙ Td.joint)

lemma jointFunctor_source_exact :
    IsExact (ArrowCategory.waldhausenStructure (dualWaldhausenStructure V W Vd Wd F hF hFd hW)).cof
      (ArrowCategory.waldhausenStructure (dualWaldhausenStructure V W Vd Wd F hF hFd hW)).weq
      (ExtensionCategory.waldhausenStructure Vd).cof (ExtensionCategory.waldhausenStructure Vd).weq
      (jointFunctor W Wd F hW V Vd hF hFd Tc Td compat ⋙
        ExtensionCategory.postcompose (dualWaldhausenStructure V W Vd Wd F hF hFd hW) Vd
          (dual_source_exact V W Vd Wd F hF hFd hW)) := by
  rw [jointFunctor_source_component]
  exact (ArrowCategory.mapArrow_exact _ _ (dual_source_exact V W Vd Wd F hF hFd hW)).comp Tc.exact

lemma jointFunctor_target_exact :
    IsExact (ArrowCategory.waldhausenStructure (dualWaldhausenStructure V W Vd Wd F hF hFd hW)).cof
      (ArrowCategory.waldhausenStructure (dualWaldhausenStructure V W Vd Wd F hF hFd hW)).weq
      (ExtensionCategory.waldhausenStructure Wd).cof (ExtensionCategory.waldhausenStructure Wd).weq
      (jointFunctor W Wd F hW V Vd hF hFd Tc Td compat ⋙
        ExtensionCategory.postcompose (dualWaldhausenStructure V W Vd Wd F hF hFd hW) Wd
          (dual_target_exact V W Vd Wd F hF hFd hW)) := by
  rw [jointFunctor_target_component]
  exact (ArrowCategory.mapArrow_exact _ _ (dual_target_exact V W Vd Wd F hF hFd hW)).comp Td.exact

lemma jointFunctor_exact :
    IsExact (ArrowCategory.waldhausenStructure (dualWaldhausenStructure V W Vd Wd F hF hFd hW)).cof
      (ArrowCategory.waldhausenStructure (dualWaldhausenStructure V W Vd Wd F hF hFd hW)).weq
      (ExtensionCategory.waldhausenStructure (dualWaldhausenStructure V W Vd Wd F hF hFd hW)).cof
      (ExtensionCategory.waldhausenStructure (dualWaldhausenStructure V W Vd Wd F hF hFd hW)).weq
      (jointFunctor W Wd F hW V Vd hF hFd Tc Td compat) where
  zero {X} hX := by
    have hc := (jointFunctor_source_exact V W Vd Wd F hF hFd hW Tc Td compat).zero hX
    have hd := (jointFunctor_target_exact V W Vd Wd F hF hFd hW Tc Td compat).zero hX
    apply IsZero.of_full_of_faithful_of_isZero (ExtensionCategory.forget _) _
    apply ArrowCategory.isZero_of_components
    · exact dual_isZero_of_components V W F hF _
        (ExtensionCategory.source_isZero Vd hc) (ExtensionCategory.source_isZero Wd hd)
    · exact dual_isZero_of_components V W F hF _
        (ExtensionCategory.middle_isZero Vd hc) (ExtensionCategory.middle_isZero Wd hd)
  cofibration f hf := by
    apply ExtensionCategory.cof_of_postcompose_pair _ Vd Wd
      (dual_source_exact V W Vd Wd F hF hFd hW)
      (dual_target_exact V W Vd Wd F hF hFd hW) (fun {_ _} _ hc hd => ⟨hc, hd⟩)
    · exact (jointFunctor_source_exact V W Vd Wd F hF hFd hW Tc Td compat).cofibration f hf
    · exact (jointFunctor_target_exact V W Vd Wd F hF hFd hW Tc Td compat).cofibration f hf
  weak f hf := by
    have hc := (jointFunctor_source_exact V W Vd Wd F hF hFd hW Tc Td compat).weak f hf
    have hd := (jointFunctor_target_exact V W Vd Wd F hF hFd hW Tc Td compat).weak f hf
    exact ⟨⟨hc.1, hd.1⟩, ⟨hc.2, hd.2⟩⟩
  pushout {A B E P} {i f g j} hi h := by
    have hc := jointFunctor_source_exact V W Vd Wd F hF hFd hW Tc Td compat
    have hd := jointFunctor_target_exact V W Vd Wd F hF hFd hW Tc Td compat
    obtain ⟨hcL, hcR⟩ := ExtensionCategory.pointwise_of_isPushout Vd (hc.cofibration i hi)
      (hc.pushout hi h)
    obtain ⟨hdL, hdR⟩ := ExtensionCategory.pointwise_of_isPushout Wd (hd.cofibration i hi)
      (hd.pushout hi h)
    apply IsPushout.of_map_of_faithful (ExtensionCategory.forget _)
    apply ExtensionCategory.arrow_isPushout
    · exact dual_isPushout_of_components W F _ _ _ _ hcL hdL
    · exact dual_isPushout_of_components W F _ _ _ _ hcR hdR
end CategoryTheory.Waldhausen.WeakArrow
