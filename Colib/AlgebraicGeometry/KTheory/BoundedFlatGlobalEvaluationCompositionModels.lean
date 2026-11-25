/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalEvaluationNaturality
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectNormalizedPullbackUnits
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackCoherence
public import Colib.CategoryTheory.FiberedCategory.CocartesianEvaluationNormalization
public import Colib.CategoryTheory.Functor.IsoRouteConjugation
public import Colib.KTheory.Waldhausen.AsSmall.ComparisonIso
public import Colib.KTheory.Waldhausen.Iterated.PrespectrumPastingHomotopy
public import Colib.KTheory.Waldhausen.Iterated.SmallModelEvaluationCoherence

/-!
# Chosen composition routes of normalized global evaluation

The lifted raw composition and the three edges between the chosen global evaluation
functors use the actual geometric composition constraint and the existing zero
normalizations. The equality of the full routes is a separate result.
-/
@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry.RingedSpace Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.GrothendieckSections
open CategoryTheory.StrictSections

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex

/-- The unlifted composition normalizes exactly the chosen three raw geometric pullbacks. -/
def evaluationUnliftedCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  normalizedCoefficientCompIso boundedAboveFlatPerfectPseudofunctor g.op f.op
    (evaluationRawNormalization g) (evaluationRawNormalization f)
    (evaluationRawNormalization (f ≫ g))

/-- The raw composition iso retains exactly the normalized geometric pullbacks of the evaluation. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationModelComposition.lean"
  "adaptation" "The actual chosen raw composition and the small-model lift"]
def evaluationRawCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationRawMap (f ≫ g)).hom.toFunctor ≅
      (evaluationRawMap g).hom.toFunctor ⋙ (evaluationRawMap f).hom.toFunctor :=
  asSmallCompositionIso _ _ _ (evaluationUnliftedCompIso f g)

/-- Evaluate first and then apply the actual geometric composition constraint. -/
def evaluationCompositionTargetIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationModel (op Z) ≫ evaluationRawMap (f ≫ g)).hom.toFunctor ≅
      ((evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f).hom.toFunctor :=
  isoWhiskerLeft (evaluationModel (op Z)).hom.toFunctor (evaluationRawCompIso f g) ≪≫
    (Functor.associator (evaluationModel (op Z)).hom.toFunctor
      (evaluationRawMap g).hom.toFunctor (evaluationRawMap f).hom.toFunctor).symm

theorem evaluationReindexComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op).hom.toFunctor =
      (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor ⋙
        (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor :=
  congrArg (fun h => h.hom.toFunctor)
    (boundedAboveFlatGlobalSectionModelFunctor.map_comp g.op f.op)

/-- Strict global reindexing followed by the chosen comparison for the second pullback. -/
def evaluationCompositionFirstIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op ≫
      evaluationModel (op X)).hom.toFunctor ≅
      ((boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ evaluationModel (op Y)) ≫
        evaluationRawMap f).hom.toFunctor :=
  eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op X)).hom.toFunctor)
      (evaluationReindexComp f g)) ≪≫
    Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
      (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
      (evaluationModel (op X)).hom.toFunctor ≪≫
    isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
      (evaluationComparisonIso f) ≪≫
    (Functor.associator (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
      (evaluationModel (op Y)).hom.toFunctor (evaluationRawMap f).hom.toFunctor).symm

/-- Apply the chosen comparison for the first pullback and postcompose by raw pullback. -/
def evaluationCompositionSecondIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ((boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ evaluationModel (op Y)) ≫
      evaluationRawMap f).hom.toFunctor ≅
      ((evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f).hom.toFunctor :=
  isoWhiskerRight (evaluationComparisonIso g) (evaluationRawMap f).hom.toFunctor

/-- Before the small-model lift, use the actual section comparison and its chosen-zero
normalization, for every scheme morphism. -/
def evaluationUnliftedIso {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  normalizedCoefficientIso boundedAboveFlatPerfectPseudofunctor f.op
    (evaluationRawNormalization f)

/-- The raw comparison is the native small lift of the actual chosen-zero constraint. -/
theorem evaluationRawCompIso_eq_asSmall {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    evaluationRawCompIso f g = asSmallCompositionIso _ _ _ (evaluationUnliftedCompIso f g) :=
  rfl

/-- The two original unlifted normalized routes agree at every component. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationModelComposition.lean"
  "adaptation" "Specialization of native section transition coherence to the actual pullbacks"]
theorem evaluationUnliftedIso_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationUnliftedIso (f ≫ g)).hom ≫
        whiskerLeft (boundedAboveFlatGlobalSectionEvaluation (op Z))
          (evaluationUnliftedCompIso f g).hom =
      eqToHom (congrArg (fun G => G ⋙ boundedAboveFlatGlobalSectionEvaluation (op X))
        (underCocartesianReindex_comp
          (Pseudofunctor.Grothendieck.forget boundedAboveFlatPerfectPseudofunctor) g.op f.op)) ≫
        (normalizedCoefficientRouteIso boundedAboveFlatPerfectPseudofunctor g.op f.op
          (evaluationRawNormalization g) (evaluationRawNormalization f)).hom :=
  normalizedCoefficientIso_comp_hom boundedAboveFlatPerfectPseudofunctor g.op f.op
    (evaluationRawNormalization g) (evaluationRawNormalization f)
    (evaluationRawNormalization (f ≫ g))

private theorem evaluationPullbackIso_eq_original {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatGlobalEvaluationPullbackIso f =
      (originalCoefficientIso boundedAboveFlatPerfectPseudofunctor f.op).symm := rfl

/-- Lift the existing section comparison once, before applying the two evaluation normalizations. -/
def evaluationLiftedIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatGlobalSectionsMap f.op ⋙ evaluationSmall (op X) ≅
      evaluationSmall (op Y) ⋙ (evaluationRawMap f).hom.toFunctor :=
  asSmallEvaluationWhiskerIso
    (boundedAboveFlatGlobalSectionsMap f.op)
    (boundedAboveFlatGlobalSectionEvaluation (op X))
    (boundedAboveFlatGlobalSectionEvaluation (op Y))
    (boundedAboveFlatPerfectNormalizedPullback f) (evaluationUnliftedIso f)

/-- The native middle comparison is precisely the once-lifted original comparison. -/
theorem evaluationMiddleIso_eq_lifted {X Y : Scheme.{u}} (f : X ⟶ Y) :
    evaluationMiddleIso f = evaluationLiftedIso f := by
  simp only [evaluationMiddleIso, evaluationLiftedIso, evaluationUnliftedIso,
    asSmallWhiskerIso, asSmallEvaluationWhiskerIso, normalizedCoefficientIso,
    evaluationPullbackIso_eq_original, Iso.symm_symm_eq,
    boundedAboveFlatGlobalSectionEvaluation]

attribute [local irreducible] evaluationNormalizationIso originalCoefficientIso

/-- Conjugating by the two actual normalized evaluations recovers the native comparison. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationNormalization.lean"
  "adaptation" "Preserve the actual chosen source and target evaluation zero normalizations"]
theorem evaluationComparisonIso_eq_conjugate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    evaluationComparisonIso f =
      isoSquareConjugate (evaluationLiftedIso f)
        (evaluationNormalizationIso (op Y)) (evaluationNormalizationIso (op X)) := by
  simp only [evaluationComparisonIso, evaluationMiddleIso_eq_lifted, isoSquareConjugate]
  rfl

private theorem unpack_evaluation_route
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (a : A ⥤ B) (b : B ⥤ C) (c : A ⥤ C)
    (e₀ : A ⥤ D) (e₁ : B ⥤ E) (e₂ : C ⥤ F)
    (p : D ⥤ E) (q : E ⥤ F) (r : D ⥤ F)
    (α : a ⋙ e₁ ≅ e₀ ⋙ p) (β : b ⋙ e₂ ≅ e₁ ⋙ q)
    (γ : c ⋙ e₂ ≅ e₀ ⋙ r) (μ : r ≅ p ⋙ q)
    (e : c ⋙ e₂ = (a ⋙ b) ⋙ e₂)
    (h : γ.hom ≫ whiskerLeft e₀ μ.hom = eqToHom e ≫
      (Functor.associator a b e₂ ≪≫ isoWhiskerLeft a β ≪≫
        (Functor.associator a e₁ q).symm ≪≫ isoWhiskerRight α q ≪≫
        Functor.associator e₀ p q).hom) :
    γ.hom ≫ whiskerLeft e₀ μ.hom =
      eqToHom e ≫ whiskerLeft a β.hom ≫ whiskerRight α.hom q := by
  apply NatTrans.ext
  funext x
  simpa only [Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id] using
    NatTrans.congr_app h x

/-- The native small lift preserves the actual normalized global evaluation routes. -/
theorem evaluationLiftedIso_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationLiftedIso (f ≫ g)).hom ≫
        whiskerLeft (evaluationSmall (op Z)) (evaluationRawCompIso f g).hom =
      eqToHom (congrArg (fun G => G ⋙ evaluationSmall (op X)) (evaluationReindexComp f g)) ≫
        whiskerLeft (boundedAboveFlatGlobalSectionsMap g.op) (evaluationLiftedIso f).hom ≫
        whiskerRight (evaluationLiftedIso g).hom (evaluationRawMap f).hom.toFunctor := by
  let a := boundedAboveFlatGlobalSectionsMap g.op
  let b := boundedAboveFlatGlobalSectionsMap f.op
  let c := boundedAboveFlatGlobalSectionsMap (f ≫ g).op
  let e₀ := boundedAboveFlatGlobalSectionEvaluation (op Z)
  let e₁ := boundedAboveFlatGlobalSectionEvaluation (op Y)
  let e₂ := boundedAboveFlatGlobalSectionEvaluation (op X)
  let p := boundedAboveFlatPerfectNormalizedPullback g
  let q := boundedAboveFlatPerfectNormalizedPullback f
  let r := boundedAboveFlatPerfectNormalizedPullback (f ≫ g)
  let α : a ⋙ e₁ ≅ e₀ ⋙ p := evaluationUnliftedIso g
  let β : b ⋙ e₂ ≅ e₁ ⋙ q := evaluationUnliftedIso f
  let γ : c ⋙ e₂ ≅ e₀ ⋙ r := evaluationUnliftedIso (f ≫ g)
  let μ : r ≅ p ⋙ q := evaluationUnliftedCompIso f g
  have hRaw : c ⋙ e₂ = (a ⋙ b) ⋙ e₂ :=
    congrArg (fun G => G ⋙ e₂) (underCocartesianReindex_comp
      (Pseudofunctor.Grothendieck.forget boundedAboveFlatPerfectPseudofunctor) g.op f.op)
  have hSmall : c ⋙ (e₂ ⋙ AsSmall.up) = a ⋙ (b ⋙ (e₂ ⋙ AsSmall.up)) :=
    congrArg (fun G => G ⋙ evaluationSmall (op X)) (evaluationReindexComp f g)
  have h := unpack_evaluation_route a b c e₀ e₁ e₂ p q r α β γ μ hRaw
    (evaluationUnliftedIso_comp_hom f g)
  exact asSmallEvaluationWhiskerIso_comp_hom a b c e₀ e₁ e₂ p q r
    α β γ μ hRaw hSmall h

universe u₀ v₀ u₁ v₁ u₂ v₂ w₀ z₀ w₁ z₁ w₂ z₂
section

variable {A₀ : Type u₀} [Category.{v₀} A₀]
  {A₁ : Type u₁} [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂]
  {B₀ : Type w₀} [Category.{z₀} B₀]
  {B₁ : Type w₁} [Category.{z₁} B₁] {B₂ : Type w₂} [Category.{z₂} B₂]

private theorem whiskered_route_app
    (a : A₀ ⥤ A₁) (b : A₁ ⥤ A₂) (c : A₀ ⥤ A₂) (e : c = a ⋙ b)
    (U₀ : A₀ ⥤ B₀) (U₁ : A₁ ⥤ B₁) (U₂ : A₂ ⥤ B₂)
    (p : B₀ ⥤ B₁) (q : B₁ ⥤ B₂) (r : B₀ ⥤ B₂)
    (α : a ⋙ U₁ ≅ U₀ ⋙ p) (β : b ⋙ U₂ ≅ U₁ ⋙ q)
    (γ : c ⋙ U₂ ≅ U₀ ⋙ r) (μ : r ≅ p ⋙ q)
    (h : γ.hom ≫ whiskerLeft U₀ μ.hom =
      eqToHom (congrArg (fun S ↦ S ⋙ U₂) e) ≫ whiskerLeft a β.hom ≫
        whiskerRight α.hom q) :
    ∀ x, γ.hom.app x ≫ μ.hom.app (U₀.obj x) =
      (eqToHom (congrArg (fun S ↦ S ⋙ U₂) e)).app x ≫
        β.hom.app (a.obj x) ≫ q.map (α.hom.app x) := by
  intro x
  simpa only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app] using
    NatTrans.congr_app h x

/-- Original composition pasting is preserved by all three actual evaluation normalizations. -/
private theorem isoSquareConjugate_comp_app
    (Sf : A₀ ⥤ A₁) (Sg : A₁ ⥤ A₂) (Sfg : A₀ ⥤ A₂) (hS : Sfg = Sf ⋙ Sg)
    (Pf : B₀ ⥤ B₁) (Pg : B₁ ⥤ B₂) (Pfg : B₀ ⥤ B₂)
    {U₀ E₀ : A₀ ⥤ B₀} {U₁ E₁ : A₁ ⥤ B₁} {U₂ E₂ : A₂ ⥤ B₂}
    (κf : Sf ⋙ U₁ ≅ U₀ ⋙ Pf) (κg : Sg ⋙ U₂ ≅ U₁ ⋙ Pg)
    (κfg : Sfg ⋙ U₂ ≅ U₀ ⋙ Pfg) (β : Pfg ≅ Pf ⋙ Pg)
    (z₀ : U₀ ≅ E₀) (z₁ : U₁ ≅ E₁) (z₂ : U₂ ≅ E₂)
    (h : ∀ x, κfg.hom.app x ≫ β.hom.app (U₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ U₂) hS)).app x ≫
        κg.hom.app (Sf.obj x) ≫ Pg.map (κf.hom.app x)) :
    ∀ x, (isoSquareConjugate κfg z₀ z₂).hom.app x ≫ β.hom.app (E₀.obj x) =
      (eqToHom (congrArg (fun S => S ⋙ E₂) hS)).app x ≫
        (isoSquareConjugate κg z₁ z₂).hom.app (Sf.obj x) ≫
          Pg.map ((isoSquareConjugate κf z₀ z₁).hom.app x) := by
  subst Sfg
  intro x
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp] at h ⊢
  simp only [isoSquareConjugate, Iso.trans_hom, Iso.symm_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Functor.map_comp, Category.assoc]
  rw [← Pg.map_comp_assoc, Iso.hom_inv_id_app, Pg.map_id, Category.id_comp]
  rw [β.hom.naturality, reassoc_of% h x]
  rfl

end

private theorem replace_route_components {C : Type*} [Category C] {A B D E F : C}
    {a a' : A ⟶ B} {b : B ⟶ F} {c : A ⟶ D} {d d' : D ⟶ E} {e e' : E ⟶ F}
    (ha : a = a') (hd : d = d') (he : e = e')
    (h : a' ≫ b = c ≫ d' ≫ e') : a ≫ b = c ≫ d ≫ e := by
  simpa only [ha, hd, he] using h

private theorem evaluationComparisonIso_app_eq_conjugate {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y)).obj.Obj) :
    (evaluationComparisonIso f).hom.app x =
      (isoSquareConjugate (evaluationLiftedIso f)
        (evaluationNormalizationIso (op Y)) (evaluationNormalizationIso (op X))).hom.app x :=
  NatTrans.congr_app (congrArg Iso.hom (evaluationComparisonIso_eq_conjugate f)) x

set_option maxHeartbeats 1200000 in
-- The final component composition checks exact instances on the common small fibers.
private theorem evaluationConjugateRoute_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (k : X ⟶ Z)
    (e : (boundedAboveFlatGlobalSectionModelFunctor.map k.op).hom.toFunctor =
      (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor ⋙
        (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor)
    (μ : (evaluationRawMap k).hom.toFunctor ≅
      (evaluationRawMap g).hom.toFunctor ⋙ (evaluationRawMap f).hom.toFunctor)
    (h : (evaluationLiftedIso k).hom ≫ whiskerLeft (evaluationSmall (op Z)) μ.hom =
      eqToHom (congrArg (fun G ↦ G ⋙ evaluationSmall (op X)) e) ≫
        whiskerLeft (boundedAboveFlatGlobalSectionsMap g.op) (evaluationLiftedIso f).hom ≫
        whiskerRight (evaluationLiftedIso g).hom (evaluationRawMap f).hom.toFunctor)
    (x : (boundedAboveFlatGlobalSectionModelFunctor.obj (op Z)).obj.Obj) :
    (evaluationComparisonIso k).hom.app x ≫
        μ.hom.app ((evaluationModel (op Z)).hom.toFunctor.obj x) =
      (eqToHom (congrArg (fun G ↦ G ⋙ (evaluationModel (op X)).hom.toFunctor) e)).app x ≫
        (evaluationComparisonIso f).hom.app
          ((boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor.obj x) ≫
        (evaluationRawMap f).hom.toFunctor.map ((evaluationComparisonIso g).hom.app x) := by
  let a := (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
  let b := (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
  let c := (boundedAboveFlatGlobalSectionModelFunctor.map k.op).hom.toFunctor
  let p := (evaluationRawMap g).hom.toFunctor
  let q := (evaluationRawMap f).hom.toFunctor
  let r := (evaluationRawMap k).hom.toFunctor
  let L₀ := evaluationSmall (op Z)
  let L₁ := evaluationSmall (op Y)
  let L₂ := evaluationSmall (op X)
  have hApp := whiskered_route_app a b c e L₀ L₁ L₂ p q r
    (evaluationLiftedIso g) (evaluationLiftedIso f) (evaluationLiftedIso k) μ h
  have hConjugate := isoSquareConjugate_comp_app a b c e p q r
    (evaluationLiftedIso g) (evaluationLiftedIso f) (evaluationLiftedIso k) μ
    (evaluationNormalizationIso (op Z)) (evaluationNormalizationIso (op Y))
    (evaluationNormalizationIso (op X)) hApp x
  have hk := evaluationComparisonIso_app_eq_conjugate k x
  have hf := evaluationComparisonIso_app_eq_conjugate f (a.obj x)
  have hg := congrArg q.map (evaluationComparisonIso_app_eq_conjugate g x)
  have hNative := replace_route_components hk hf hg hConjugate
  exact hNative

/-- The actual composition equation after all three original chosen-zero transports. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/GlobalBassEvaluationModelComposition.lean"
  "adaptation" "Retain the original lifted comparison and three independent chosen zeros"]
theorem evaluationComparisonIso_comp_app {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (boundedAboveFlatGlobalSectionModelFunctor.obj (op Z)).obj.Obj) :
    (evaluationComparisonIso (f ≫ g)).hom.app x ≫
        (evaluationRawCompIso f g).hom.app ((evaluationModel (op Z)).hom.toFunctor.obj x) =
      (eqToHom (congrArg (fun G => G ⋙ (evaluationModel (op X)).hom.toFunctor)
        (evaluationReindexComp f g))).app x ≫
        (evaluationComparisonIso f).hom.app
          ((boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor.obj x) ≫
        (evaluationRawMap f).hom.toFunctor.map ((evaluationComparisonIso g).hom.app x) :=
  evaluationConjugateRoute_app f g (f ≫ g) (evaluationReindexComp f g)
    (evaluationRawCompIso f g) (evaluationLiftedIso_comp_hom f g) x

private theorem evaluationCompositionTargetIso_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (boundedAboveFlatGlobalSectionModelFunctor.obj (op Z)).obj.Obj) :
    (evaluationCompositionTargetIso f g).hom.app x =
      (evaluationRawCompIso f g).hom.app ((evaluationModel (op Z)).hom.toFunctor.obj x) := by
  simp only [evaluationCompositionTargetIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Functor.associator_inv_app, Category.comp_id]

private theorem first_route_component
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    (a : A ⥤ B) (b : B ⥤ C) (c : A ⥤ C) (U : B ⥤ D) (V : C ⥤ E) (q : D ⥤ E)
    (e : c ⋙ V = (a ⋙ b) ⋙ V) (β : b ⋙ V ≅ U ⋙ q)
    (I : c ⋙ V ≅ (a ⋙ U) ⋙ q)
    (hI : I = eqToIso e ≪≫ Functor.associator a b V ≪≫ isoWhiskerLeft a β ≪≫
      (Functor.associator a U q).symm) (x : A) :
    I.hom.app x = (eqToHom e).app x ≫ β.hom.app (a.obj x) := by
  subst I
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
    Functor.associator_hom_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp]

set_option maxHeartbeats 1200000 in
-- Comparing the small-category composites checks the exact component instances.
private theorem evaluationCompositionFirstIso_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (boundedAboveFlatGlobalSectionModelFunctor.obj (op Z)).obj.Obj) :
    (evaluationCompositionFirstIso f g).hom.app x =
      (eqToHom (congrArg (fun G ↦ G ⋙ (evaluationModel (op X)).hom.toFunctor)
        (evaluationReindexComp f g))).app x ≫
        (evaluationComparisonIso f).hom.app
          ((boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor.obj x) :=
  first_route_component
    (boundedAboveFlatGlobalSectionModelFunctor.map g.op).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map f.op).hom.toFunctor
    (boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op).hom.toFunctor
    (evaluationModel (op Y)).hom.toFunctor (evaluationModel (op X)).hom.toFunctor
    (evaluationRawMap f).hom.toFunctor
    (congrArg (fun G ↦ G ⋙ (evaluationModel (op X)).hom.toFunctor) (evaluationReindexComp f g))
    (evaluationComparisonIso f) (evaluationCompositionFirstIso f g) rfl x

private theorem evaluationCompositionSecondIso_app {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : (boundedAboveFlatGlobalSectionModelFunctor.obj (op Z)).obj.Obj) :
    (evaluationCompositionSecondIso f g).hom.app x =
      (evaluationRawMap f).hom.toFunctor.map ((evaluationComparisonIso g).hom.app x) := rfl

/-- The two chosen global model transformation pastings agree as whole transformations. -/
theorem evaluationComposition_pasting {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (evaluationComparisonIso (f ≫ g)).hom ≫ (evaluationCompositionTargetIso f g).hom =
      (evaluationCompositionFirstIso f g).hom ≫ (evaluationCompositionSecondIso f g).hom := by
  apply NatTrans.ext
  funext x
  simp only [NatTrans.comp_app, evaluationCompositionTargetIso_app,
    evaluationCompositionFirstIso_app, evaluationCompositionSecondIso_app, Category.assoc]
  exact evaluationComparisonIso_comp_app f g x

/-- Realize the proved two-route equality between the actual native model arrows. -/
def evaluationModelCompositionRelHomotopy {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :=
  prespectrumTransformationPastingHomotopy
    (V := boundedAboveFlatGlobalSectionModelFunctor.obj (op Z))
    (W := asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace))
    (F := boundedAboveFlatGlobalSectionModelFunctor.map (f ≫ g).op ≫ evaluationModel (op X))
    (G := evaluationModel (op Z) ≫ evaluationRawMap (f ≫ g))
    (G' := (boundedAboveFlatGlobalSectionModelFunctor.map g.op ≫ evaluationModel (op Y)) ≫
      evaluationRawMap f)
    (H := (evaluationModel (op Z) ≫ evaluationRawMap g) ≫ evaluationRawMap f)
    (evaluationComparisonIso (f ≫ g)).hom (evaluationCompositionTargetIso f g).hom
    (evaluationCompositionFirstIso f g).hom (evaluationCompositionSecondIso f g).hom
    (fun x ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationComparisonIso (f ≫ g)).hom.app x))))
    (fun x ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationCompositionTargetIso f g).hom.app x))))
    (fun x ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationCompositionFirstIso f g).hom.app x))))
    (fun x ↦ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso _
      (inferInstanceAs (IsIso ((evaluationCompositionSecondIso f g).hom.app x))))
    (evaluationComposition_pasting f g)

end AlgebraicGeometry.Scheme.Modules.GlobalSectionChangeIndex
