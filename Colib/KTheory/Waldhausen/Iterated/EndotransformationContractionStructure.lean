/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.KTheory.Waldhausen.Iterated.EndotransformationContractionWhiskering



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

namespace CategoryTheory.Waldhausen.IteratedS

variable {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
variable {V' W' : WideSubcategory preservesZero.{u}} {F' : V' ⟶ W'}

/-- The postcomposed original contraction retains the independent structure parameter. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:559"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationContraction_postcomp_structure
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : W ⟶ T)
    (hz' : ∀ A, T.obj.waldhausen.weq ((zeroEndotransformation (F ≫ J)).app A))
    (n : ℕ) (r s t : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction (F ≫ J) (whiskerRight η J.hom.toFunctor)
      (fun A ↦ J.hom.isExact.weak _ (hη A)) hz').level (n + 1)
        (r, (s, (prespectrum V).structureMap n x t)) =
      (prespectrum T).structureMap n ((prespectrumMap J).map n
        ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x)))) t := by
  rw [prespectrumEndotransformationContraction_postcomp_level F η hη hz J hz',
    (prespectrumEndotransformationContraction F η hη hz).comm]
  exact congrArg (fun γ ↦ γ t) ((prespectrumMap J).comm n
    ((prespectrumEndotransformationContraction F η hη hz).level n (r, (s, x))))

/-- The precomposed original contraction retains the independent structure parameter. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:575"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationContraction_precomp_structure
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : T ⟶ V)
    (n : ℕ) (r s t : unitInterval) (x : (prespectrum T).space n) :
    (prespectrumEndotransformationContraction (J ≫ F) (whiskerLeft J.hom.toFunctor η)
      (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hz (J.hom.toFunctor.obj A))).level (n + 1)
        (r, (s, (prespectrum T).structureMap n x t)) =
      (prespectrum W).structureMap n
        ((prespectrumEndotransformationContraction F η hη hz).level n
          (r, (s, (prespectrumMap J).map n x))) t := by
  rw [(prespectrumEndotransformationContraction (J ≫ F) (whiskerLeft J.hom.toFunctor η)
    (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hz (J.hom.toFunctor.obj A))).comm]
  rw [prespectrumEndotransformationContraction_precomp_level F η hη hz J]

/-- At degree zero, the original internal loop coordinate is separate from both times. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:590"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationContraction_postcomp_zero_apply
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : W ⟶ T)
    (hz' : ∀ A, T.obj.waldhausen.weq ((zeroEndotransformation (F ≫ J)).app A))
    (r s q : unitInterval) (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 T) (stagePoint 0 T) from
      (prespectrumEndotransformationContraction (F ≫ J) (whiskerRight η J.hom.toFunctor)
        (fun A ↦ J.hom.isExact.weak _ (hη A)) hz').level 0 (r, (s, γ))) q =
      SSet.toTop.map ((stages 0).map J)
        ((show Path (stagePoint 0 W) (stagePoint 0 W) from
          (prespectrumEndotransformationContraction F η hη hz).level 0 (r, (s, γ))) q) :=
  congrArg (fun p : Path (stagePoint 0 T) (stagePoint 0 T) ↦ p q)
    (prespectrumEndotransformationContraction_postcomp_level F η hη hz J hz' 0 r s γ)

/-- Precomposition at degree zero retains the same independent internal loop coordinate. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:605"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationContraction_precomp_zero_apply
    (η : F.hom.toFunctor ⟶ F.hom.toFunctor) (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hz : ∀ A, W.obj.waldhausen.weq ((zeroEndotransformation F).app A)) (J : T ⟶ V)
    (r s q : unitInterval) (γ : Path (stagePoint 0 T) (stagePoint 0 T)) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      (prespectrumEndotransformationContraction (J ≫ F) (whiskerLeft J.hom.toFunctor η)
        (fun A ↦ hη (J.hom.toFunctor.obj A)) (fun A ↦ hz (J.hom.toFunctor.obj A))).level 0
          (r, (s, γ))) q =
      (show Path (stagePoint 0 W) (stagePoint 0 W) from
        (prespectrumEndotransformationContraction F η hη hz).level 0
          (r, (s, (prespectrumMap J).map 0 γ))) q :=
  congrArg (fun p : Path (stagePoint 0 W) (stagePoint 0 W) ↦ p q)
    (prespectrumEndotransformationContraction_precomp_level F η hη hz J 0 r s γ)

/-- Equality-induced conjugation changes no value of the prescribed original contraction. -/
@[colib_ref "quillen"
  "Quillen/Waldhausen/SConstruction/Iterated/EndotransformationContractionNaturality.lean:620"
  "adaptation"
    "Original whole transformation contraction, independent times and coefficient naturality"]
theorem prespectrumEndotransformationContraction_transport_level
    {V W : WideSubcategory preservesZero.{u}} {F F' : V ⟶ W} (h : F = F')
    (η : F'.hom.toFunctor ⟶ F'.hom.toFunctor) (hη : ∀ X, W.obj.waldhausen.weq (η.app X))
    (hη' : ∀ X, W.obj.waldhausen.weq
      ((eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) h) ≫ η ≫
        eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) h.symm)).app X))
    (hz : ∀ X, W.obj.waldhausen.weq ((zeroEndotransformation F).app X))
    (hz' : ∀ X, W.obj.waldhausen.weq ((zeroEndotransformation F').app X))
    (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n) :
    (prespectrumEndotransformationContraction F
      (eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) h) ≫ η ≫
        eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) h.symm)) hη' hz).level n (r, (s, x)) =
      (prespectrumEndotransformationContraction F' η hη hz').level n (r, (s, x)) := by
  have he : HEq
      (eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) h) ≫ η ≫
        eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) h.symm)) η := by
    cases h
    exact heq_of_eq (by simp only [eqToHom_refl, Category.id_comp, Category.comp_id])
  exact prespectrumEndotransformationContraction_level_eq_of_heq
    (V := V) (W := W) (F := F) (F' := F') h
    (eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) h) ≫ η ≫
      eqToHom (congrArg (fun k : V ⟶ W ↦ k.hom.toFunctor) h.symm)) η hη' hη hz hz' he n r s x

end CategoryTheory.Waldhausen.IteratedS
