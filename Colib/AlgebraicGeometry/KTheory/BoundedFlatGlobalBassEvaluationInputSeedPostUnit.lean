/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedEvaluationCarrier
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputUnit
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedCarrier
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalUnitFactor

/-!
# Original forward-unit anchors under the actual raw Laurent postmap

Actual normalized geometric pullback preserves the pulled-back Laurent scalar. The complete
postcomposition reference therefore intertwines the two original strict evaluated units,
and every full Laurent node keeps its own shifted anchor before realization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS SmallWaldhausenCategory
open CategoryTheory.Functor.IdentityAutomorphism AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostUnit
open GlobalSectionChangeIndex CommonReferenceNerve

/-- Actual normalized raw pullback preserves precisely the pulled-back forward scalar. -/
theorem raw_preserves {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(Y, ⊤))ˣ) :
    Preserves (evaluationRawMap f).hom.toFunctor (evaluationSmallUnit (op Y) r)
      (evaluationSmallUnit (op X) (Units.map f.appTop.hom.toMonoidHom r)) :=
  GlobalUnitIdentityOperation.normalizedModel_preserves f r

private theorem post_intertwine {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ T)
    (H : V ⟶ W) (R : W ⟶ T) (e : F.hom.toFunctor ≅ (H ≫ R).hom.toFunctor)
    (α : F.hom.toFunctor ≅ F.hom.toFunctor) (δ : H.hom.toFunctor ≅ H.hom.toFunctor)
    (β : 𝟭 _ ≅ 𝟭 _) (γ : 𝟭 _ ≅ 𝟭 _)
    (hα : α = onFunctor F.hom.toFunctor γ) (hδ : δ = onFunctor H.hom.toFunctor β)
    (hR : Preserves R.hom.toFunctor β γ) :
    α ≪≫ e = e ≪≫ isoWhiskerRight δ R.hom.toFunctor := by
  subst α δ
  apply Iso.ext
  apply NatTrans.ext
  funext x
  change γ.hom.app (F.hom.toFunctor.obj x) ≫ e.hom.app x =
    e.hom.app x ≫ R.hom.toFunctor.map (β.hom.app (H.hom.toFunctor.obj x))
  rw [hR (H.hom.toFunctor.obj x)]
  exact (γ.hom.naturality (e.hom.app x)).symm

private theorem reanchor_post {V W T : WideSubcategory preservesZero.{u}} (F : V ⟶ T)
    (H : V ⟶ W) (R : W ⟶ T) (e : F.hom.toFunctor ≅ (H ≫ R).hom.toFunctor)
    (α : F.hom.toFunctor ≅ F.hom.toFunctor) (δ : H.hom.toFunctor ≅ H.hom.toFunctor)
    (h : α ≪≫ e = e ≪≫ isoWhiskerRight δ R.hom.toFunctor) (N : Node H) :
    ModelSimplex.reanchorNode α (attachPostcompNode H R F e N) =
      attachPostcompNode H R F e (ModelSimplex.reanchorNode δ N) := by
  apply congrArg (fun a => (⟨N.1 ≫ R, a⟩ : Node F))
  change α ≪≫ (e ≪≫ isoWhiskerRight N.2 R.hom.toFunctor) =
    e ≪≫ isoWhiskerRight (δ ≪≫ N.2) R.hom.toFunctor
  rw [isoWhiskerRight_trans, ← Iso.trans_assoc, ← Iso.trans_assoc, h]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original geometric Laurent scalar equation identifies the exact transported unit. -/
theorem laurent_preserves :
    Preserves (evaluationRawMap (laurent.map g)).hom.toFunctor
      (evaluationSmallUnit (op (laurent.obj Y))
        (laurentScalar (op Y)))
      (evaluationSmallUnit (op (laurent.obj X))
        (laurentScalar (op X))) := by
  have h := raw_preserves (laurent.map g) (laurentScalar (op Y))
  rw [GlobalRawBass.laurentUnit_map] at h
  exact h

/-- The entire existing postcomposition anchor intertwines both actual evaluated strict units. -/
theorem post_unit :
    InputSeedCarrier.commonUnit g ≪≫ InputMixedDesc.postSourceIso g =
      InputMixedDesc.postSourceIso g ≪≫
        isoWhiskerRight (InputSeedEvaluationCarrier.commonUnit Y)
          (evaluationRawMap (laurent.map g)).hom.toFunctor :=
  post_intertwine (InputSeedCarrier.laurentRef g) (InputSeedEvaluationCarrier.laurentRef Y)
    (evaluationRawMap (laurent.map g)) (InputMixedDesc.postSourceIso g)
    (InputSeedCarrier.commonUnit g) (InputSeedEvaluationCarrier.commonUnit Y)
    (evaluationSmallUnit (op (laurent.obj Y)) (laurentScalar (op Y)))
    (evaluationSmallUnit (op (laurent.obj X)) (laurentScalar (op X)))
    (InputSeedCarrier.commonUnit_eq_target g) (InputSeedEvaluationCarrier.commonUnit_eq_target Y)
    (laurent_preserves g)

/-- Every original Laurent node retains its complete unit anchor after the actual raw postmap. -/
theorem post_shift (N : Node (InputSeedEvaluationCarrier.laurentRef Y)) :
    ModelSimplex.reanchorNode (InputSeedCarrier.commonUnit g) (InputMixedDesc.postNode g N) =
      InputMixedDesc.postNode g
        (ModelSimplex.reanchorNode (InputSeedEvaluationCarrier.commonUnit Y) N) :=
  reanchor_post (InputSeedCarrier.laurentRef g) (InputSeedEvaluationCarrier.laurentRef Y)
    (evaluationRawMap (laurent.map g)) (InputMixedDesc.postSourceIso g)
    (InputSeedCarrier.commonUnit g) (InputSeedEvaluationCarrier.commonUnit Y) (post_unit g) N

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedPostUnit
