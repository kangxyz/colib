/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Functor.PointwiseCoproduct
public import Colib.CategoryTheory.Waldhausen.Additivity.NormalizedEndpointFamilies
public import Colib.CategoryTheory.Waldhausen.Additivity.CoproductAlgebra
public import Colib.CategoryTheory.Waldhausen.NormalizedWeakTransformation

/-!
# Actual transformations of the original additivity pushouts

Commuting squares of functors give literal maps between the original pushouts. The original
Waldhausen gluing axiom proves weakness. The two actual endpoint comparisons retain the middle
transformation and the quotient-first separated transformation, including their chosen-zero
normalizations. These are categorical squares; no realized two-parameter filler is asserted.
-/
/- Implementation provenance: Quillen/Waldhausen/Additivity/PushoutTransformation.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd. Source-only native adaptation;
   no compilation or independent-review claim is made. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable (W : Structure D) {F G F' G' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G')
  (ha : ∀ X, W.cof (a.app X)) (ha' : ∀ X, W.cof (a'.app X))
  (ηF : F ⟶ F') (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a')

/-- The literal pushout map of the original commuting square at an actual arrow. -/
def pushoutTransformationApp (f : Arrow C) :
    (pushoutFunctor W a ha).obj f ⟶ (pushoutFunctor W a' ha').obj f := by
  letI := hasPushout W a ha f.hom
  letI := hasPushout W a' ha' f.hom
  exact pushout.map (a.app f.left) (F.map f.hom) (a'.app f.left) (F'.map f.hom)
    (ηG.app f.left) (ηF.app f.right) (ηF.app f.left)
    (NatTrans.congr_app haη f.left) (ηF.naturality f.hom)

/-- The actual middle leg retains the given middle transformation. -/
@[reassoc (attr := simp)]
theorem sourceι_pushoutTransformationApp (f : Arrow C) :
    sourceι W a ha f ≫ pushoutTransformationApp W a a' ha ha' ηF ηG haη f =
      ηG.app f.left ≫ sourceι W a' ha' f := by
  let := hasPushout W a ha f.hom
  let := hasPushout W a' ha' f.hom
  simp [sourceι, pushoutTransformationApp, pushout.map]

/-- The actual target leg retains the given subobject transformation. -/
@[reassoc (attr := simp)]
theorem targetι_pushoutTransformationApp (f : Arrow C) :
    targetι W a ha f ≫ pushoutTransformationApp W a a' ha ha' ηF ηG haη f =
      ηF.app f.right ≫ targetι W a' ha' f := by
  let := hasPushout W a ha f.hom
  let := hasPushout W a' ha' f.hom
  simp [targetι, pushoutTransformationApp, pushout.map]

/-- Literal pushout maps are natural on all original arrow-category squares. -/
def pushoutTransformation : pushoutFunctor W a ha ⟶ pushoutFunctor W a' ha' where
  app := pushoutTransformationApp W a a' ha ha' ηF ηG haη
  naturality f g φ := by
    apply (pushoutFunctor_isPushout W a ha f).hom_ext
    · simp only [sourceι_naturality_assoc, sourceι_pushoutTransformationApp,
        sourceι_pushoutTransformationApp_assoc, sourceι_naturality]
      rw [← Category.assoc, ηG.naturality, Category.assoc]
    · simp only [targetι_naturality_assoc, targetι_pushoutTransformationApp,
        targetι_pushoutTransformationApp_assoc, targetι_naturality]
      rw [← Category.assoc, ηF.naturality, Category.assoc]

/-- Weakness comes from the three given weak legs and the two actual pushout squares. -/
theorem pushoutTransformation_weak
    (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X)) (f : Arrow C) :
    W.weq ((pushoutTransformation W a a' ha ha' ηF ηG haη).app f) :=
  W.gluing (ηF.app f.left) (ηG.app f.left) (ηF.app f.right)
    (pushoutTransformationApp W a a' ha ha' ηF ηG haη f) (ha _) (ha' _)
    (pushoutFunctor_isPushout W a ha f) (pushoutFunctor_isPushout W a' ha' f)
    (NatTrans.congr_app haη f.left) (ηF.naturality f.hom)
    (sourceι_pushoutTransformationApp W a a' ha ha' ηF ηG haη f)
    (targetι_pushoutTransformationApp W a a' ha ha' ηF ηG haη f)
    (hηF _) (hηG _) (hηF _)

/-- The identity endpoint keeps the original pushout comparison and middle transformation. -/
theorem pushoutTransformation_identity (X : C) :
    (pushoutTransformation W a a' ha ha' ηF ηG haη).app (Arrow.mk (𝟙 X)) ≫
        (pushoutIdentityIso W a' ha' X).hom =
      (pushoutIdentityIso W a ha X).hom ≫ ηG.app X := by
  apply (pushoutFunctor_isPushout W a ha (Arrow.mk (𝟙 X))).hom_ext
  · simp [pushoutTransformation, pushoutIdentityIso_hom]
  · simp only [pushoutTransformation, targetι_pushoutTransformationApp_assoc,
      pushoutIdentityIso_hom, targetι_comparison, targetι_comparison_assoc]
    exact (NatTrans.congr_app haη X).symm

variable {H H' : C ⥤ D} (b : G ⟶ H) (b' : G' ⟶ H') (ηH : H ⟶ H')
  (hbη : b ≫ ηH = ηG ≫ b') [HasBinaryCoproducts D]

/-- The pair-sum components preserve the original weak maps. -/
theorem splitEndpointTransformation_weak
    (hηH : ∀ X, W.weq (ηH.app X)) (hηF : ∀ X, W.weq (ηF.app X)) (X : C × C) :
    W.weq ((splitEndpointTransformation ηF ηH).app X) :=
  coprod_map_weak W _ _ (hηH _) (hηF _)

include hbη in
/-- The original zero-arrow cofiber comparison retains the actual quotient map first. -/
@[reassoc]
theorem pushoutTransformation_cofiberEndpoint (f : Arrow C)
    (hc : IsPushout (a.app f.left) (W.isZero.from_ (F.obj f.left))
      (b.app f.left) (W.isZero.to_ (H.obj f.left)))
    (hc' : IsPushout (a'.app f.left) (W.isZero.from_ (F'.obj f.left))
      (b'.app f.left) (W.isZero.to_ (H'.obj f.left)))
    (hz : F.map f.hom = W.isZero.from_ (F.obj f.left) ≫ W.isZero.to_ (F.obj f.right))
    (hz' : F'.map f.hom = W.isZero.from_ (F'.obj f.left) ≫ W.isZero.to_ (F'.obj f.right)) :
    (pushoutTransformation W a a' ha ha' ηF ηG haη).app f ≫
        (cofiberEndpointIso W a' ha' f (b'.app f.left) hc' hz').hom =
      (cofiberEndpointIso W a ha f (b.app f.left) hc hz).hom ≫
        coprod.map (ηH.app f.left) (ηF.app f.right) := by
  apply (pushoutFunctor_isPushout W a ha f).hom_ext
  · simp only [pushoutTransformation, sourceι_pushoutTransformationApp_assoc,
      sourceι_cofiberEndpointIso, sourceι_cofiberEndpointIso_assoc, coprod.inl_map]
    have hb := NatTrans.congr_app hbη f.left
    change b.app f.left ≫ ηH.app f.left = ηG.app f.left ≫ b'.app f.left at hb
    rw [← Category.assoc, ← hb, Category.assoc]
  · simp [pushoutTransformation]

section Normalized
variable (V : Structure C)
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')

/-- The pushout transformation conjugated by the two unchanged chosen-zero normalization isos. -/
def normalizedPushoutTransformation :
    normalizedPushoutFunctor V W a hs.exactF hs.exactG hs.cofibration ⟶
      normalizedPushoutFunctor V W a' hs'.exactF hs'.exactG hs'.cofibration :=
  (normalizedPushoutIso V W a hs.exactF hs.exactG hs.cofibration).inv ≫
    pushoutTransformation W a a' hs.cofibration.app_cof hs'.cofibration.app_cof ηF ηG haη ≫
    (normalizedPushoutIso V W a' hs'.exactF hs'.exactG hs'.cofibration).hom

omit [HasBinaryCoproducts D] in
/-- The entire normalized transformation remains pointwise weak. -/
theorem normalizedPushoutTransformation_weak
    (hηF : ∀ X, W.weq (ηF.app X)) (hηG : ∀ X, W.weq (ηG.app X)) (f : Arrow C) :
    W.weq ((normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app f) :=
  W.weq.comp_mem _ _ (W.weq_iso _ inferInstance)
    (W.weq.comp_mem _ _
      (pushoutTransformation_weak W a a' hs.cofibration.app_cof hs'.cofibration.app_cof
        ηF ηG haη hηF hηG f) (W.weq_iso _ inferInstance))

omit [HasBinaryCoproducts D] in
/-- The actual chosen-zero arrow component is identity under the original zero equalities. -/
theorem normalizedPushoutTransformation_zero :
    eqToHom (normalizedPushoutFunctor_obj_zero V W a hs.exactF hs.exactG hs.cofibration).symm ≫
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app
          (Arrow.mk (𝟙 V.zero)) ≫
        eqToHom (normalizedPushoutFunctor_obj_zero V W a' hs'.exactF hs'.exactG hs'.cofibration) =
      𝟙 W.zero := W.isZero.eq_of_src _ _

/-- The quotient-first transformation conjugated by the original common split normalizations. -/
def normalizedSplitEndpointTransformation :
    normalizedSplitEndpoint V W hs.exactH hs.exactF ⟶
      normalizedSplitEndpoint V W hs'.exactH hs'.exactF :=
  (normalizedSplitIso V W hs.exactH hs.exactF).inv ≫ splitEndpointTransformation ηF ηH ≫
    (normalizedSplitIso V W hs'.exactH hs'.exactF).hom

/-- The normalized quotient-first transformation retains actual weak components. -/
theorem normalizedSplitEndpointTransformation_weak
    (hηH : ∀ X, W.weq (ηH.app X)) (hηF : ∀ X, W.weq (ηF.app X)) (X : C × C) :
    W.weq ((normalizedSplitEndpointTransformation W a a' ηF b b' ηH V hs hs').app X) :=
  W.weq.comp_mem _ _ (W.weq_iso _ inferInstance)
    (W.weq.comp_mem _ _ (splitEndpointTransformation_weak W ηF ηH hηH hηF X)
      (W.weq_iso _ inferInstance))

/-- The actual normalized pair-of-zeros component is the identity of the original zero. -/
theorem normalizedSplitEndpointTransformation_zero :
    eqToHom (normalizedSplitEndpoint_obj_zero V W hs.exactH hs.exactF).symm ≫
        (normalizedSplitEndpointTransformation W a a' ηF b b' ηH V hs hs').app
          (V.zero, V.zero) ≫
        eqToHom (normalizedSplitEndpoint_obj_zero V W hs'.exactH hs'.exactF) =
      𝟙 W.zero := W.isZero.eq_of_src _ _

omit [HasBinaryCoproducts D] in
/-- The identity deformation square retains the actual inverse source-inclusion maps. -/
@[reassoc]
theorem pushoutTransformation_identityDeformation (n m : SimplexCategory)
    (A : Grid₂ n m ⥤ C) (x : Grid₂ n m) :
    (pushoutTransformation W a a' hs.cofibration.app_cof hs'.cofibration.app_cof
        ηF ηG haη).app ((intervalArrows (𝟙 n) (𝟙 n) (fun _ ↦ le_rfl) A).obj x) ≫
        (identityDeformationIso V W a' hs'.cofibration (𝟙 n) A).hom.app x =
      (identityDeformationIso V W a hs.cofibration (𝟙 n) A).hom.app x ≫
        ηG.app (A.obj x) := by
  let e := identityDeformationIso V W a hs.cofibration (𝟙 n) A
  let e' := identityDeformationIso V W a' hs'.cofibration (𝟙 n) A
  apply (cancel_epi (e.inv.app x)).1
  rw [← Category.assoc]
  change (sourceι W a hs.cofibration.app_cof _ ≫
      pushoutTransformationApp W a a' hs.cofibration.app_cof hs'.cofibration.app_cof
        ηF ηG haη _) ≫ e'.hom.app x = _
  rw [sourceι_pushoutTransformationApp]
  change (ηG.app (A.obj x) ≫ e'.inv.app x) ≫ e'.hom.app x =
    e.inv.app x ≫ e.hom.app x ≫ ηG.app (A.obj x)
  simp

omit [HasBinaryCoproducts D] in
/-- The whole normalized identity endpoint square uses the original rebased middle map. -/
theorem normalizedPushoutTransformation_identityEndpointFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((bisimplicialSSet V).obj n).obj m) :
    Functor.whiskerLeft
        (intervalArrows (𝟙 n.unop) (𝟙 n.unop) (fun _ ↦ le_rfl) A.1)
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs') ≫
        normalizedIdentityEndpointFamily V W a' hs'.exactF hs'.exactG hs'.cofibration n m A =
      normalizedIdentityEndpointFamily V W a hs.exactF hs.exactG hs.cofibration n m A ≫
        Functor.whiskerLeft A.1 (normalizedWeakTransformation hs.exactG hs'.exactG ηG) := by
  apply NatTrans.ext
  funext x
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    normalizedPushoutTransformation, normalizedIdentityEndpointFamily,
    normalizedIdentityEndpointIso, normalizedWeakTransformation, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [pushoutTransformation_identityDeformation_assoc W a a' ηF ηG haη b b' V hs hs']

include hbη in
/-- The whole normalized separated square retains the quotient-first pair transformation. -/
theorem normalizedPushoutTransformation_separatedEndpointFamily (n m : SimplexCategoryᵒᵖ)
    (A : ((SSet.OrdinalSubdivision.δ.op ⋙ bisimplicialSSet V).obj n).obj m) :
    Functor.whiskerLeft
        (intervalArrows (SSet.OrdinalJoin.left n.unop n.unop) (SSet.OrdinalJoin.right n.unop n.unop)
          (left_le_right n.unop) A.1)
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs') ≫
        normalizedSeparatedEndpointFamily V W a' b' hs' n m A =
      normalizedSeparatedEndpointFamily V W a b hs n m A ≫
        Functor.whiskerLeft (separatedPairGrid A.1)
          (normalizedSplitEndpointTransformation W a a' ηF b b' ηH V hs hs') := by
  apply NatTrans.ext
  funext x
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    normalizedPushoutTransformation, normalizedSeparatedEndpointFamily,
    normalizedSeparatedEndpointIso, normalizedSplitEndpointTransformation,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Category.assoc, Iso.hom_inv_id_app_assoc]
  simp only [separatedDeformationIso, NatIso.ofComponents_hom_app]
  rw [pushoutTransformation_cofiberEndpoint_assoc W a a' hs.cofibration.app_cof
    hs'.cofibration.app_cof ηF ηG haη b b' ηH hbη]
  rfl

end Normalized
end CategoryTheory.Waldhausen.Additivity
