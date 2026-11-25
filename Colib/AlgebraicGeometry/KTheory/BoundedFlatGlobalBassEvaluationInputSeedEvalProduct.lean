/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputSeedUnitNodes
public import
  Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputRawSquareProduct

/-!
# The original evaluation-times-unit product in the mixed seed reference

Both times remain independent. The evaluation factor is the original comparison and the unit
factor is the original normalized Laurent unit. All product vertices keep their full anchors.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry AlgebraicGeometry.RingedSpace Opposite
open Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationProduct
open GlobalSectionChangeIndex InputNormalizationPrism CommonReferenceNerve

private theorem transformation_congr
    {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} {F G : V ⟶ W}
    (η θ : F.hom.toFunctor ⟶ G.hom.toFunctor)
    (hη : ∀ A, W.obj.waldhausen.weq (η.app A))
    (hθ : ∀ A, W.obj.waldhausen.weq (θ.app A)) (e : η = θ) :
    prespectrumTransformationHomotopy η hη = prespectrumTransformationHomotopy θ hθ := by
  subst θ
  rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The unchanged raw Laurent projection is the second product factor. -/
def unitMap (X : Scheme.{u}) := evaluationRawMap (GlobalRawBass.laurentProjection.app X)

/-- The actual target action has the unchanged normalized raw-unit transformation. -/
def unitIso (X : Scheme.{u}) : (unitMap X).hom.toFunctor ≅ (unitMap X).hom.toFunctor :=
  CategoryTheory.Functor.IdentityAutomorphism.onFunctor (unitMap X).hom.toFunctor
    (evaluationSmallUnit (op (laurent.obj X)) (laurentScalar (op X)))

/-- The scalar unit retains two distinct reference nodes over the same actual Model arrow. -/
def unitVertices (X : Scheme.{u}) : Fin 2 →
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace) ⟶
      asSmallCategory (boundedAboveFlatPerfectWaldhausen (laurent.obj X).toRingedSpace)) :=
  fun _ ↦ unitMap X

/-- The unchanged lower reference and its actual forward-unit shift. -/
def unitAnchors (X : Scheme.{u}) :
    ∀ i, (unitMap X).hom.toFunctor ≅ (unitVertices X i).hom.toFunctor :=
  ![Iso.refl _, unitIso X]

/-- The original unit edge as an entire two-node Model simplex. -/
def unitSimplex (X : Scheme.{u}) :=
  ModelSimplex.ofIsos (unitMap X) (unitVertices X) (unitAnchors X)

private def unitTriangleFace : ⦋2⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 1], by decide⟩

private theorem unit_triangle (X : Scheme.{u}) :
    HomotopyLift (unitSimplex X) (triangle unitTriangleFace)
      (prespectrumTransformationCompositionHomotopy
        (F := unitMap X) (G := unitMap X) (H := unitMap X) (unitIso X).hom (𝟙 _)
        (fun _ ↦ (asSmallCategory (boundedAboveFlatPerfectWaldhausen (laurent.obj
          X).toRingedSpace)).obj.waldhausen.weq_iso
          _ inferInstance)
        (fun _ ↦ (asSmallCategory (boundedAboveFlatPerfectWaldhausen (laurent.obj
          X).toRingedSpace)).obj.waldhausen.weq_iso
          _ inferInstance)) := by
  apply triangle_lift
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact Category.comp_id _

private theorem unit_track (X : Scheme.{u}) :
    prespectrumIsoHomotopy (unitMap X) (unitIso X) = GlobalRawBass.unitHomotopy X :=
  transformation_congr (F := unitMap X) (G := unitMap X)
    (unitIso X).hom
    (evaluationRawUnit (GlobalRawBass.laurentProjection.app X)
      (laurentScalar (op X))) _ _
    (evaluationRawUnit_eq (GlobalRawBass.laurentProjection.app X)
      (laurentScalar (op X))).symm

/-- Every native unit time is the original raw forward unit, with no reparameterization. -/
theorem unit_native (X : Scheme.{u}) :
    PathLift (unitSimplex X) (edge (k := 1) 0 1) (GlobalRawBass.unitHomotopy X) := by
  have h := PathLift.trans_left _ (HomotopyLift.target _ (unit_triangle X))
  intro n s x
  exact (h n s x).trans
    (congrArg (fun H ↦ H.level n (s, x)) (unit_track X))

/-- The common reference is the complete actual second evaluation cut. -/
def anchor : (InputSeedCarrier.laurentRef g).hom.toFunctor ≅
    (firstSource g ≫ unitMap X).hom.toFunctor := (InputSeedUnitNodes.lower g 6).2

/-- Four complete original product nodes retain both independent factor references. -/
def nodes (i : Fin 4) : Node (InputSeedCarrier.laurentRef g) :=
  ⟨CommonReferenceProduct.vertices (firstVertices g) (unitVertices X) i,
    anchor g ≪≫ CommonReferenceProduct.references (firstSource g)
      (firstVertices g) (firstAnchors g) (unitMap X) (unitVertices X) (unitAnchors X) i⟩

/-- The complete two-time product parameter keeps the literal evaluation and unit clocks. -/
def scalar : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 4)) :=
  ⟨fun z ↦ Topology.SimplexGrid.parameter.{u + 1} 1 1
    ((edge (k := 1) 0 1) z.1, (edge (k := 1) 0 1) z.2), by fun_prop⟩

/-- The actual product surface takes values in the fixed original Laurent-reference nerve. -/
def parameter : C(unitInterval × unitInterval,
    |nerve (Codiscrete (Node (InputSeedCarrier.laurentRef g)))|) :=
  (CommonReferenceNerve.parameter (InputSeedCarrier.laurentRef g) (nodes g)).comp scalar.{u}

private theorem simplex_eq :
    ModelSimplex.ofIsos (InputSeedCarrier.laurentRef g)
      (fun i ↦ (nodes g i).1) (fun i ↦ (nodes g i).2) =
    CommonReferenceProduct.simplex (firstSource g) (firstVertices g) (firstAnchors g)
      (unitMap X) (unitVertices X) (unitAnchors X) :=
  ModelSimplex.ofIsos_change_reference (anchor g) _ _

/-- The complete product has precisely the prescribed original moving-input native value. -/
theorem native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (boundedAboveFlatGlobalSectionModelFunctor.obj (op Y))).space n) :
    prespectrumSimplexFamily (ModelSimplex.ofIsos (InputSeedCarrier.laurentRef g)
      (fun i => (nodes g i).1) (fun i => (nodes g i).2)) n (scalar.{u} (r, s), x) =
      (GlobalRawBass.unitHomotopy X).level n (s, (evaluationComparison g).level n (r, x)) := by
  rw [simplex_eq]
  simp only [scalar, ContinuousMap.coe_mk]
  exact (CommonReferenceProduct.prespectrum_comp
    (firstSource g) (firstVertices g) (firstAnchors g)
    (unitMap X) (unitVertices X) (unitAnchors X) n x
    ((edge (k := 1) 0 1) r) ((edge (k := 1) 0 1) s)).trans
      ((congrArg (fun y ↦ prespectrumSimplexFamily (unitSimplex X) n
        ((edge (k := 1) 0 1) s, y)) (first_native g n r x)).trans
          (unit_native X n s ((evaluationComparison g).level n (r, x))))

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputSeedEvaluationProduct
