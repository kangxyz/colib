/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.Algebra.Homology.RightDerivedEdgeComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.ForgetfulInclusionCohomologyPresheaf
import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompIsoSpellings
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunction

/-!
# The sections edge on the original Ext groups

For an exact inverse image and an invertible counit at the coefficient,
the sections edge computes the adjunction map on Ext. The comparison uses
the existing Ext identification of right derived sections and the actual
augmentation-preserving map of injective resolutions.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open ModuleSheafCohomology Stacks.Cohomology

universe u u' u'' v v' v'' w w' u₁ u₂ v₁

namespace Stacks.Cohomology.FreeYonedaUnivLE

section Evaluation

variable {A : Type u} {B : Type u'} {D : Type u''}
  [Category.{v} A] [Category.{v'} B] [Category.{v''} D]
  [Abelian A] [Abelian B] [Abelian D] [EnoughInjectives A]
  (F : A ⥤ B) [F.Additive] (G : B ⥤ D) [G.Additive] [G.PreservesHomology]

/-- The historical comparison used by the cohomology-presheaf bridge computes by applying the
exact evaluator to the homology of the original chosen resolution. -/
private theorem derivedForgetCompIso_hom_app (X : A) (n : ℕ) :
    (DerivedForget.rightDerivedCompIso F G n).hom.app X =
      G.map ((injectiveResolution X).isoRightDerivedObj F n).hom ≫
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (injectiveResolution X).cocomplex).sc n).mapHomologyIso G).inv ≫
        ((injectiveResolution X).isoRightDerivedObj (F ⋙ G) n).inv := by
  rw [Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution,
    Stacks.DerivedIndexing.isoRightDerivedObj_injectiveResolution_inv]
  unfold HomotopyCategory.homologyFunctorFactors
  rw [Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  unfold CategoryTheory.Functor.rightDerived
    CategoryTheory.Functor.rightDerivedToHomotopyCategory HomotopyCategory.homologyFunctor
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj (injectiveResolution X).cocomplex
  change ((K.sc n).mapHomologyIso G).inv =
    G.map (𝟙 (K.sc n).homology) ≫ ((K.sc n).mapHomologyIso G).inv ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]


/-- The evaluation comparison has the same components in the two pinned spellings. -/
theorem derivedForgetCompIso_hom_app_eq_moduleComparison (X : A) (n : ℕ) :
    (DerivedForget.rightDerivedCompIso F G n).hom.app X =
      (ModuleComparison.rightDerivedCompIso F G (F ⋙ G) (Iso.refl _) n).hom.app X := by
  rw [derivedForgetCompIso_hom_app, DerivedCompTransport.rightDerivedCompIso_hom_app,
    Stacks.DerivedIndexing.mapComplexHomologyIso_refl_hom_app,
    Stacks.DerivedIndexing.mapExactHomologyIso]
  rfl

end Evaluation

section AdjunctionCocycle

variable {D : Type u} [Category.{v} D] [Abelian D]

private def changeAugmentation {X Y : D} (I : InjectiveResolution Y) (e : X ≅ Y) :
    InjectiveResolution X where
  cocomplex := I.cocomplex
  injective := I.injective
  ι := (CochainComplex.single₀ D).map e.hom ≫ I.ι
  quasiIso := inferInstance

private theorem changeAugmentation_ι_f_zero {Y X : D} (I : InjectiveResolution Y)
    (e : X ≅ Y) : (changeAugmentation I e).ι.f 0 = e.hom ≫ I.ι.f 0 := by
  change ((CochainComplex.single₀ D).map e.hom ≫ I.ι).f 0 = _
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero]
  rfl

variable {C : Type u'} [Category.{v'} C] [Abelian C]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [HasExt.{w} C] [HasExt.{w'} D]

/-- The counit sends the image of the resolution cocycle to the target resolution. -/
private theorem adjunctionExtMapOnResolution {W : C} {W' F : D} (e : L.obj W ≅ W')
    (I : InjectiveResolution F) (J : InjectiveResolution (R.obj F))
    [IsIso (adj.counit.app F)]
    (φ : J.cocomplex ⟶ (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
    (hφ : J.ι.f 0 ≫ φ.f 0 = R.map (I.ι.f 0))
    (n : ℕ) (t : W ⟶ J.cocomplex.X n) (ht : t ≫ J.cocomplex.d n (n + 1) = 0) :
    ∃ (s : W' ⟶ I.cocomplex.X n) (hs : s ≫ I.cocomplex.d n (n + 1) = 0),
      s = e.inv ≫ L.map (t ≫ φ.f n) ≫ adj.counit.app (I.cocomplex.X n) ∧
      (Ext.mk₀ e.inv).comp (Stacks.ExtAdjunction.extMap adj W F n
        (J.extMk t (n + 1) rfl ht)) (zero_add n) = I.extMk s (n + 1) rfl hs := by
  let ε := asIso (adj.counit.app F)
  let I' := changeAugmentation I ε
  let ψ : (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex ⟶ I'.cocomplex :=
    (L.mapHomologicalComplex (ComplexShape.up ℕ)).map φ ≫
      (NatTrans.mapHomologicalComplex adj.counit (ComplexShape.up ℕ)).app I.cocomplex
  have hψ : L.map (J.ι.f 0) ≫ ψ.f 0 = I'.ι.f 0 := by
    rw [changeAugmentation_ι_f_zero]
    change L.map (J.ι.f 0) ≫ L.map (φ.f 0) ≫ adj.counit.app (I.cocomplex.X 0) =
      adj.counit.app F ≫ I.ι.f 0
    rw [← CategoryTheory.Functor.map_comp_assoc, hφ]
    exact adj.counit.naturality (I.ι.f 0)
  let τ : InjectiveResolution.Hom I' I (adj.counit.app F) :=
    ⟨𝟙 I.cocomplex, by
      simp only [HomologicalComplex.id_f, CochainComplex.single₀_map_f_zero]
      rw [changeAugmentation_ι_f_zero]
      exact Category.comp_id _⟩
  let ht' := ModuleComparison.extMk_map_comp_eq_zero L J I' ψ t rfl ht
  have hext := ModuleComparison.mapExactFunctor_extMk L J I' ψ hψ t rfl ht
  have h₁ := I'.extMk_comp_mk₀ (L.map t ≫ ψ.f n) (n + 1) rfl ht' τ
  have h₂ : (L.map t ≫ ψ.f n) ≫ τ.hom.f n = L.map (t ≫ φ.f n) ≫
      adj.counit.app (I.cocomplex.X n) := by
    change (L.map t ≫ L.map (φ.f n) ≫ adj.counit.app (I.cocomplex.X n)) ≫ 𝟙 _ = _
    rw [Category.comp_id, CategoryTheory.Functor.map_comp_assoc]
  simp only [Stacks.ExtAdjunction.extMap_apply, hext, h₁]
  let q := (L.map t ≫ ψ.f n) ≫ τ.hom.f n
  refine ⟨e.inv ≫ q, ?_, congrArg (e.inv ≫ ·) h₂, ?_⟩
  · have hq : q ≫ I.cocomplex.d n (n + 1) = 0 := by
      change ((L.map t ≫ ψ.f n) ≫ 𝟙 _) ≫ I.cocomplex.d n (n + 1) = 0
      rw [Category.comp_id]
      exact ht'
    rw [Category.assoc, hq, comp_zero]
  · exact I.mk₀_comp_extMk q (n + 1) rfl _ e.inv

end AdjunctionCocycle

section ReadCocycles

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
  {Y : A} (I : InjectiveResolution Y) (X : A) (H : A ⥤ AddCommGrpCat.{v})
  [H.Additive] (α : H ≅ preadditiveCoyoneda.obj (op X)) (n : ℕ)

private abbrev homComplex :
    CochainComplex AddCommGrpCat.{v} ℕ :=
  ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

private abbrev evaluatedComplex :
    CochainComplex AddCommGrpCat.{v} ℕ :=
  (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex

private def cocycleToEvaluatedCycles :
    (extLeftHomologyData I X n).K ⟶ (evaluatedComplex I H).cycles (n + 1) :=
  (extLeftHomologyData I X n).cyclesIso.inv ≫
    ((homComplex I X).cyclesIsoSc' n (n + 1) (n + 2) (by simp) (by simp)).inv ≫
    HomologicalComplex.cyclesMap
      ((NatTrans.mapHomologicalComplex α.inv (ComplexShape.up ℕ)).app I.cocomplex) (n + 1)

/-- The evaluated cocycle is read by applying the original corepresentation to its component. -/
private theorem cocycleToEvaluatedCycles_i :
    cocycleToEvaluatedCycles I X H α n ≫ (evaluatedComplex I H).iCycles (n + 1) =
      (extLeftHomologyData I X n).i ≫ α.inv.app (I.cocomplex.X (n + 1)) := by
  unfold cocycleToEvaluatedCycles
  simp only [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [reassoc_of% (HomologicalComplex.cyclesIsoSc'_inv_iCycles
        (homComplex I X) n (n + 1) (n + 2) (by simp) (by simp))]
  rw [reassoc_of% (ShortComplex.LeftHomologyData.cyclesIso_inv_comp_iCycles
    (extLeftHomologyData I X n))]
  rfl

variable [HasInjectiveResolutions A] [PreservesFiniteLimits H]

/-- Elementwise form of the pinned positive-degree reading of the Ext-to-sections comparison. -/
private theorem extBridge_on_cocycle
    (hπ : (extLeftHomologyData I X n).π ≫ (extFunctorObjIsoRightDerived H X α (n + 1)).hom.app Y =
      cocycleToEvaluatedCycles I X H α n ≫ (evaluatedComplex I H).homologyπ (n + 1) ≫
        (I.isoRightDerivedObj H (n + 1)).inv)
    (z : (extLeftHomologyData I X n).K) :
    (extFunctorObjIsoRightDerived H X α (n + 1)).hom.app Y ((extLeftHomologyData I X n).π z) =
      (I.isoRightDerivedObj H (n + 1)).inv
        ((evaluatedComplex I H).homologyπ (n + 1)
          (cocycleToEvaluatedCycles I X H α n z)) :=
  ConcreteCategory.congr_hom hπ z

end ReadCocycles

section Positive

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{v₁} A]
  {B : Type u₂} [Category.{v₁} B] [Abelian B] [HasExt.{v₁} B]
  (R : B ⥤ A) [R.Additive] (Q : A ⥤ AddCommGrpCat.{v₁}) [Q.Additive]
  (W : A) (W' : B) (a : Q ≅ preadditiveCoyoneda.obj (op W))
  (b : R ⋙ Q ≅ preadditiveCoyoneda.obj (op W'))
  {F : B} (J : InjectiveResolution (R.obj F)) (I : InjectiveResolution F)
  (φ : J.cocomplex ⟶ (R.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)
  (n : ℕ)

private abbrev sectionsComparison :
    evaluatedComplex J Q ⟶ evaluatedComplex I (R ⋙ Q) :=
  (Q.mapHomologicalComplex (ComplexShape.up ℕ)).map φ

/-- Comparing the underlying sections determines the equality of the two evaluated cycles. -/
private theorem compareEvaluatedCycles
    (t : (extLeftHomologyData J W n).K) (s : (extLeftHomologyData I W' n).K)
    (h : Q.map (φ.f (n + 1))
          (a.inv.app (J.cocomplex.X (n + 1)) ((extLeftHomologyData J W n).i t)) =
        b.inv.app (I.cocomplex.X (n + 1)) ((extLeftHomologyData I W' n).i s)) :
    HomologicalComplex.cyclesMap (sectionsComparison R Q J I φ) (n + 1)
        (cocycleToEvaluatedCycles J W Q a n t) =
      cocycleToEvaluatedCycles I W' (R ⋙ Q) b n s := by
  apply ((AddCommGrpCat.mono_iff_injective
    ((evaluatedComplex I (R ⋙ Q)).iCycles (n + 1))).mp inferInstance)
  have hJ := ConcreteCategory.congr_hom (cocycleToEvaluatedCycles_i J W Q a n) t
  have hI := ConcreteCategory.congr_hom (cocycleToEvaluatedCycles_i I W' (R ⋙ Q) b n) s
  have hφ := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (sectionsComparison R Q J I φ) (n + 1))
      (cocycleToEvaluatedCycles J W Q a n t)
  exact hφ.trans ((congrArg (Q.map (φ.f (n + 1))) hJ).trans (h.trans hI.symm))

variable [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  [PreservesFiniteLimits Q] [PreservesFiniteLimits (R ⋙ Q)]

/-- Paste the explicit edge and Ext-to-sections cocycle equations at the existing Ext classes. -/
private theorem compareBridgeOnCocycle
    (η : ((Q.rightDerived (n + 1)).obj (R.obj F)) ⟶ ((R ⋙ Q).rightDerived (n + 1)).obj F)
    (hη : η =
      (J.isoRightDerivedObj Q (n + 1)).hom ≫
        HomologicalComplex.homologyMap (sectionsComparison R Q J I φ) (n + 1) ≫
        (I.isoRightDerivedObj (R ⋙ Q) (n + 1)).inv)
    (hJ : (extLeftHomologyData J W n).π ≫
        (extFunctorObjIsoRightDerived Q W a (n + 1)).hom.app (R.obj F) =
      cocycleToEvaluatedCycles J W Q a n ≫ (evaluatedComplex J Q).homologyπ (n + 1) ≫
        (J.isoRightDerivedObj Q (n + 1)).inv)
    (hI : (extLeftHomologyData I W' n).π ≫
        (extFunctorObjIsoRightDerived (R ⋙ Q) W' b (n + 1)).hom.app F =
      cocycleToEvaluatedCycles I W' (R ⋙ Q) b n ≫
        (evaluatedComplex I (R ⋙ Q)).homologyπ (n + 1) ≫
        (I.isoRightDerivedObj (R ⋙ Q) (n + 1)).inv)
    (t : (extLeftHomologyData J W n).K) (s : (extLeftHomologyData I W' n).K)
    (h : Q.map (φ.f (n + 1))
          (a.inv.app (J.cocomplex.X (n + 1)) ((extLeftHomologyData J W n).i t)) =
        b.inv.app (I.cocomplex.X (n + 1)) ((extLeftHomologyData I W' n).i s)) :
    η ((extFunctorObjIsoRightDerived Q W a (n + 1)).hom.app (R.obj F)
        ((extLeftHomologyData J W n).π t)) =
      (extFunctorObjIsoRightDerived (R ⋙ Q) W' b (n + 1)).hom.app F
        ((extLeftHomologyData I W' n).π s) := by
  let hcycles := compareEvaluatedCycles R Q W W' a b J I φ n t s h
  rw [extBridge_on_cocycle J W Q a n hJ t,
    extBridge_on_cocycle I W' (R ⋙ Q) b n hI s]
  rw [hη]
  simp only [ConcreteCategory.comp_apply]
  let JJ := J.isoRightDerivedObj Q (n + 1)
  let z := (evaluatedComplex J Q).homologyπ (n + 1) (cocycleToEvaluatedCycles J W Q a n t)
  have hInv : JJ.hom (JJ.inv z) = z := ConcreteCategory.congr_hom JJ.inv_hom_id z
  rw [hInv]
  have hπ := ConcreteCategory.congr_hom
    (HomologicalComplex.homologyπ_naturality (sectionsComparison R Q J I φ) (n + 1))
    (cocycleToEvaluatedCycles J W Q a n t)
  simp only [ConcreteCategory.comp_apply] at hπ
  exact congrArg ((I.isoRightDerivedObj (R ⋙ Q) (n + 1)).inv)
    (hπ.trans (congrArg ((evaluatedComplex I (R ⋙ Q)).homologyπ (n + 1)) hcycles))


variable {L : A ⥤ B} (adj : L ⊣ R) [L.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

/-- The canonical edge and the adjunction Ext map agree on every positive-degree Ext class
under the three pinned resolution formulae. -/
private theorem comparePositiveBridge
    (e : L.obj W ≅ W') [IsIso (adj.counit.app F)]
    (hφ : J.ι.f 0 ≫ φ.f 0 = R.map (I.ι.f 0))
    (hSections : ∀ (G : B) (t : W ⟶ R.obj G),
      b.inv.app G (e.inv ≫ L.map t ≫ adj.counit.app G) = a.inv.app (R.obj G) t)
    (η : ((Q.rightDerived (n + 1)).obj (R.obj F)) ⟶ ((R ⋙ Q).rightDerived (n + 1)).obj F)
    (hη : η =
      (J.isoRightDerivedObj Q (n + 1)).hom ≫
        HomologicalComplex.homologyMap (sectionsComparison R Q J I φ) (n + 1) ≫
        (I.isoRightDerivedObj (R ⋙ Q) (n + 1)).inv)
    (hJ : (extLeftHomologyData J W n).π ≫
        (extFunctorObjIsoRightDerived Q W a (n + 1)).hom.app (R.obj F) =
      cocycleToEvaluatedCycles J W Q a n ≫ (evaluatedComplex J Q).homologyπ (n + 1) ≫
        (J.isoRightDerivedObj Q (n + 1)).inv)
    (hI : (extLeftHomologyData I W' n).π ≫
        (extFunctorObjIsoRightDerived (R ⋙ Q) W' b (n + 1)).hom.app F =
      cocycleToEvaluatedCycles I W' (R ⋙ Q) b n ≫
        (evaluatedComplex I (R ⋙ Q)).homologyπ (n + 1) ≫
        (I.isoRightDerivedObj (R ⋙ Q) (n + 1)).inv)
    (x : Ext.{v₁} W (R.obj F) (n + 1)) :
    η ((extFunctorObjIsoRightDerived Q W a (n + 1)).hom.app (R.obj F) x) =
      (extFunctorObjIsoRightDerived (R ⋙ Q) W' b (n + 1)).hom.app F
        ((Ext.mk₀ e.inv).comp (Stacks.ExtAdjunction.extMap adj W F (n + 1) x) (zero_add _)) := by
  obtain ⟨t, ht, rfl⟩ := J.extMk_surjective x (n + 2) rfl
  obtain ⟨s, hs, hsn, hse⟩ :=
    adjunctionExtMapOnResolution adj e I J φ hφ (n + 1) t ht
  have hnat := (NatTrans.naturality_apply a.inv (φ.f (n + 1)) t).symm
  have hval :
      Q.map (φ.f (n + 1)) (a.inv.app (J.cocomplex.X (n + 1)) t) =
        b.inv.app (I.cocomplex.X (n + 1)) s := by
    rw [hsn]
    exact hnat.trans (hSections (I.cocomplex.X (n + 1)) (t ≫ φ.f (n + 1))).symm
  have hReading := compareBridgeOnCocycle R Q W W' a b J I φ n η hη hJ hI
    ⟨t, ht⟩ ⟨s, hs⟩ hval
  change η ((extFunctorObjIsoRightDerived Q W a (n + 1)).hom.app (R.obj F)
      (J.extMk t (n + 2) rfl ht)) =
    (extFunctorObjIsoRightDerived (R ⋙ Q) W' b (n + 1)).hom.app F
      (I.extMk s (n + 2) rfl hs) at hReading
  exact hReading.trans (congrArg ((extFunctorObjIsoRightDerived (R ⋙ Q) W' b (n + 1)).hom.app F)
    hse.symm)

end Positive

section DegreeZero

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{v} A]
  [HasInjectiveResolutions A]
  (H : A ⥤ AddCommGrpCat.{v}) [H.Additive] [PreservesFiniteLimits H]
  (W : A) (a : H ≅ preadditiveCoyoneda.obj (op W)) (Y : A)

/-- The Ext-to-sections bridge carries a degree-zero morphism to its section in degree zero. -/
private theorem extBridge_zero_on_mk₀ (f : W ⟶ Y) :
    (extFunctorObjIsoRightDerived H W a 0).hom.app Y (Ext.mk₀ f) =
      H.toRightDerivedZero.app Y (a.inv.app Y f) := by
  simp only [extFunctorObjIsoRightDerived_zero, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.rightDerivedZeroIsoSelf_inv,
    NatTrans.comp_app]
  change H.toRightDerivedZero.app Y (a.inv.app Y (Ext.addEquiv₀ (Ext.mk₀ f))) = _
  have h : Ext.addEquiv₀ (Ext.mk₀ f) = f :=
    (Ext.mk₀_bijective W Y).injective (Ext.mk₀_addEquiv₀_apply _)
  rw [h]

variable {B : Type u'} [Category.{v} B] [Abelian B] [HasExt.{v} B]
  [HasInjectiveResolutions B]
  {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
  [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits (R ⋙ H)] (W' : B) (e : L.obj W ≅ W')
  (b : R ⋙ H ≅ preadditiveCoyoneda.obj (op W')) (F : B)

/-- The degree-zero bridge and adjunction map agree after applying the edge to the original
sections. The input about sections is the direct free-Yoneda identity. -/
private theorem compareBridgeZero
    (η : (H.rightDerived 0).obj (R.obj F) ⟶ ((R ⋙ H).rightDerived 0).obj F)
    (hη : H.toRightDerivedZero.app (R.obj F) ≫ η = (R ⋙ H).toRightDerivedZero.app F)
    (hSections : ∀ t : W ⟶ R.obj F,
      b.inv.app F (e.inv ≫ L.map t ≫ adj.counit.app F) = a.inv.app (R.obj F) t)
    (x : Ext.{v} W (R.obj F) 0) :
    η ((extFunctorObjIsoRightDerived H W a 0).hom.app (R.obj F) x) =
      (extFunctorObjIsoRightDerived (R ⋙ H) W' b 0).hom.app F
        ((Ext.mk₀ e.inv).comp (Stacks.ExtAdjunction.extMap adj W F 0 x) (zero_add 0)) := by
  obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective W (R.obj F)).surjective x
  have ht : (Ext.mk₀ e.inv).comp (Stacks.ExtAdjunction.extMap adj W F 0 (Ext.mk₀ t)) (zero_add 0) =
      Ext.mk₀ (e.inv ≫ L.map t ≫ adj.counit.app F) := by
    simp only [Stacks.ExtAdjunction.extMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]
  rw [extBridge_zero_on_mk₀ H W a, ht, extBridge_zero_on_mk₀ (R ⋙ H) W' b, hSections]
  exact ConcreteCategory.congr_hom hη (a.inv.app (R.obj F) t)

end DegreeZero

section OrdinaryEdge

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{v₁} A]
  {B : Type u₂} [Category.{v₁} B] [Abelian B] [HasExt.{v₁} B]
  [HasInjectiveResolutions A] [HasInjectiveResolutions B]
  {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R)
  [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [R.Additive] [R.PreservesInjectiveObjects]
  (Q : A ⥤ AddCommGrpCat.{v₁}) [Q.Additive]
  [PreservesFiniteLimits Q] [PreservesFiniteLimits (R ⋙ Q)]
  (W : A) (W' : B) (a : Q ≅ preadditiveCoyoneda.obj (op W))
  (b : R ⋙ Q ≅ preadditiveCoyoneda.obj (op W')) (i : L.obj W ≅ W')

/-- The usual sections edge agrees with exact inverse image and the counit on Ext. -/
theorem sectionsEdge_eq_refinement (F : B) [IsIso (adj.counit.app F)] (n : ℕ)
    (hSections : ∀ (G : B) (s : W ⟶ R.obj G),
      b.inv.app G (i.inv ≫ L.map s ≫ adj.counit.app G) = a.inv.app (R.obj G) s) :
    (extFunctorObjIsoRightDerived Q W a n).hom.app (R.obj F) ≫
        (RightDerivedEdge.edge R Q n).app F =
      AddCommGrpCat.ofHom (((Ext.mk₀ i.inv).precomp F (zero_add n)).comp
          (Stacks.ExtAdjunction.extMap adj W F n)) ≫
        (extFunctorObjIsoRightDerived (R ⋙ Q) W' b n).hom.app F := by
  ext x
  change (RightDerivedEdge.edge R Q n).app F
      ((extFunctorObjIsoRightDerived Q W a n).hom.app (R.obj F) x) =
    (extFunctorObjIsoRightDerived (R ⋙ Q) W' b n).hom.app F
      ((Ext.mk₀ i.inv).comp (Stacks.ExtAdjunction.extMap adj W F n x) (zero_add n))
  cases n with
  | zero =>
      exact compareBridgeZero Q W a adj W' i b F _
        (RightDerivedEdge.toRightDerivedZero_comp_edge_zero R Q F) (hSections F) x
  | succ n =>
      let I := injectiveResolution F
      let J := injectiveResolution (R.obj F)
      let φ := RightDerivedEdge.resolutionComparison R F
      have hφ := RightDerivedEdge.ι_f_zero_comp_resolutionComparison R F
      have hη := RightDerivedEdge.edge_app_eq R Q (n + 1) I J φ hφ
      have hJ : (extLeftHomologyData J W n).π ≫
          (extFunctorObjIsoRightDerived Q W a (n + 1)).hom.app (R.obj F) =
        cocycleToEvaluatedCycles J W Q a n ≫ (evaluatedComplex J Q).homologyπ (n + 1) ≫
          (J.isoRightDerivedObj Q (n + 1)).inv := by
        simpa only [cocycleToEvaluatedCycles, Category.assoc] using
          (ModuleComparison.extFunctorObjIsoRightDerived_succ_π_comp
            Q W a (R.obj F) n (by simp) (by simp))
      have hI : (extLeftHomologyData I W' n).π ≫
          (extFunctorObjIsoRightDerived (R ⋙ Q) W' b (n + 1)).hom.app F =
        cocycleToEvaluatedCycles I W' (R ⋙ Q) b n ≫
          (evaluatedComplex I (R ⋙ Q)).homologyπ (n + 1) ≫
          (I.isoRightDerivedObj (R ⋙ Q) (n + 1)).inv := by
        simpa only [cocycleToEvaluatedCycles, Category.assoc] using
          (ModuleComparison.extFunctorObjIsoRightDerived_succ_π_comp
            (R ⋙ Q) W' b F n (by simp) (by simp))
      exact comparePositiveBridge R Q W W' a b J I φ n adj i hφ hSections _ hη hJ hI x

end OrdinaryEdge

end Stacks.Cohomology.FreeYonedaUnivLE
