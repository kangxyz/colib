/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSimplex
public import Colib.KTheory.Waldhausen.Iterated.ScalarRouteExtraction
public import Colib.KTheory.Waldhausen.Iterated.SimplexWhiskering
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumSplitTripleEvaluation

/-!
# Whole native global evaluation composition in its actual simplex

The scalar parameter follows the already selected normalization and two-triangle pasting word.
Every equality retains both comparison coordinates, the entire half-clock seam, and all
prespectrum levels. No replacement evaluation comparison is selected here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.RingedSpace
open Topology.LoopPrespectrum CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSimplex
open GlobalSectionChangeIndex

private theorem lift_cast {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {k : ℕ} (S : ModelSimplex V W k)
    {a b : StdSimplex ℝ (Fin (k + 1))} {p q : Path a b} {J : p.Homotopy q}
    {f g : prespectrum V ⟶ prespectrum W}
    {H H' K K' : Homotopy f g} {M : H.RelHomotopy K}
    (hJ : HomotopyLift S J M) (hH : H = H') (hK : K = K')
    (e : H.RelHomotopy K = H'.RelHomotopy K') : HomotopyLift S J (e.mp M) := by
  subst H'
  subst K'
  exact hJ

private theorem pasting_native
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}}
    {k : ℕ} (S : ModelSimplex V W k)
    {a b : StdSimplex ℝ (Fin (k + 1))} {p q z : Path a b}
    (J : p.Homotopy q) (K : p.Homotopy z) {F G G' H : V ⟶ W}
    (η : F.hom.toFunctor ⟶ G.hom.toFunctor) (θ : G.hom.toFunctor ⟶ H.hom.toFunctor)
    (η' : F.hom.toFunctor ⟶ G'.hom.toFunctor) (θ' : G'.hom.toFunctor ⟶ H.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A)) (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.obj.waldhausen.weq (η'.app A))
    (hθ' : ∀ A, W.obj.waldhausen.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ')
    (lJ : HomotopyLift S J (prespectrumTransformationCompositionHomotopy η θ hη hθ))
    (lK : HomotopyLift S K (prespectrumTransformationCompositionHomotopy η' θ' hη' hθ')) :
    HomotopyLift S (J.symm.trans K)
      (prespectrumTransformationPastingHomotopy η θ η' θ' hη hθ hη' hθ' he) := by
  unfold prespectrumTransformationPastingHomotopy
  apply HomotopyLift.trans S (HomotopyLift.symm S lJ)
  apply lift_cast S lK _ rfl
  congr 1
  exact he.symm

private theorem face_triangle_family
    {V W T : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {k : ℕ}
    (R : ModelSimplex V W 2) (S : ModelSimplex T W k) (J : T ⟶ V)
    (α : ⦋2⦌ ⟶ ⦋k⦌) (hface : S.face α = R.precomp J)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    prespectrumSimplexFamily S n (triangle α (r, s), x) =
      prespectrumSimplexFamily R n
        (CategoryTheory.TheoremB.compositionTriangleHomotopy (r, s), (prespectrumMap J).map n x) :=
  (prespectrumSimplexFamily_face S α n
    (CategoryTheory.TheoremB.compositionTriangleHomotopy (r, s)) x).trans
    ((congrArg (fun Q => prespectrumSimplexFamily Q n
      (CategoryTheory.TheoremB.compositionTriangleHomotopy (r, s), x)) hface).trans
      (prespectrumSimplexFamily_precomp R J n
        (CategoryTheory.TheoremB.compositionTriangleHomotopy (r, s)) x))

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The two original Model triangles use the native two-half comparison clock. -/
def modelParameter :=
  (triangle (triangleFace 0 1 4 (by decide) (by decide))).symm.trans
    (triangle (triangleFace 0 3 4 (by decide) (by decide)))

/-- The binary normalization remains under the unchanged first evaluation edge. -/
def splitParameter :=
  (Path.Homotopy.refl (edge (k := 4) 0 1)).hcomp
    (triangle (triangleFace 1 2 4 (by decide) (by decide)))

/-- The original outer comparison first reverses normalization, then follows Model pasting. -/
def compositionParameter := splitParameter.symm.trans modelParameter

/-- Every point of the first original Model triangle is preserved. -/
theorem total_native :
    HomotopyLift (simplex f g) (triangle (triangleFace 0 1 4 (by decide) (by decide)))
      (prespectrumTransformationCompositionHomotopy
        (F := sourceMap f g) (G := totalMap f g) (H := targetMap f g)
        (evaluationComparisonIso (f ≫ g)).hom (evaluationCompositionTargetIso f g).hom
        (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso
          _ inferInstance)
        (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso
          _ inferInstance)) :=
  triangle_lift _ _ _ _ _ _ (total_face f g)

/-- Every point of the original strict-cut Model triangle is preserved. -/
theorem cut_native :
    HomotopyLift (simplex f g) (triangle (triangleFace 0 3 4 (by decide) (by decide)))
      (prespectrumTransformationCompositionHomotopy
        (F := sourceMap f g) (G := cutMap f g) (H := targetMap f g)
        (evaluationCompositionFirstIso f g).hom (evaluationCompositionSecondIso f g).hom
        (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso
          _ inferInstance)
        (fun _ => (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).asSmall.weq_iso
          _ inferInstance)) :=
  triangle_lift _ _ _ _ _ _ (cut_face f g)

/-- The entire binary comparison remains the native triangle under the evaluation whisker. -/
theorem normalization_native :
    HomotopyLift (simplex f g) (triangle (triangleFace 1 2 4 (by decide) (by decide)))
      (Homotopy.RelHomotopy.precomp (prespectrumMap (evaluationModel (op Z)))
        (evaluationRawCompTotalSplit f g)) := by
  intro n r s x
  let J := evaluationModel (op Z)
  let x' := (prespectrumMap J).map n x
  exact (face_triangle_family (BoundedFlatPerfectBinarySimplex.simplex f g)
    (simplex f g) J (triangleFace 1 2 4 (by decide) (by decide))
    (normalization_face f g) n r s x).trans
      ((BoundedFlatPerfectBinarySimplex.whole_triangle f g n r s x').trans
        (((BoundedFlatPerfectBinarySimplex.native_apply f g n r s x').symm).trans
          (DFunLike.congr_fun (evaluationRawCompTotalSplit_level f g n).symm
            (r, (s, x')))))

/-- The original evaluation edge is recovered from the actual first triangle, including its seam. -/
theorem evaluation_native :
    PathLift (simplex f g) (edge (k := 4) 0 1) (evaluationComparison (f ≫ g)) := by
  have h := PathLift.trans_left _ (HomotopyLift.target _ (total_native f g))
  intro n s x
  exact h n s x

/-- Both actual Model-pasting halves retain their original equality transport. -/
theorem model_native :
    HomotopyLift (simplex f g) modelParameter (evaluationModelCompositionRelHomotopy f g) :=
  pasting_native (simplex f g) _ _ _ _ _ _ _ _ _ _
    (evaluationComposition_pasting f g) (total_native f g) (cut_native f g)

/-- The original ofLevels wrapper preserves the full Model-pasting surface. -/
theorem totalWhiskered_native :
    HomotopyLift (simplex f g) modelParameter (evaluationCompositionTotalWhiskered f g) := by
  intro n r s x
  exact model_native f g n r s x

/-- The actual binary triangle retains the unchanged outer evaluation half-clock. -/
theorem totalSplit_native :
    HomotopyLift (simplex f g) splitParameter (evaluationCompositionTotalSplit f g) := by
  have h := HomotopyLift.hcomp (simplex f g)
    (PathLift.refl _ (evaluation_native f g)) (normalization_native f g)
  intro n r s x
  exact h n r s x

/-- The entire selected global evaluation composition is the literal scalar word in one simplex. -/
theorem composition_native :
    HomotopyLift (simplex f g) compositionParameter (evaluationCompositionRelHomotopy f g) :=
  HomotopyLift.trans _ (HomotopyLift.symm _ (totalSplit_native f g))
    (totalWhiskered_native f g)

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSimplex
