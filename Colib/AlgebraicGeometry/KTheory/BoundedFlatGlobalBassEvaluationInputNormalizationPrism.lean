/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalBassEvaluationInputTriplePreNodes
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceProductColumns
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceWhiskering

/-!
# The original global evaluation normalization prism

The two rows are the three original precomposed normalization nodes and their actual
conversions by the final evaluation comparison. Their complete dependent nodes agree with
the canonical product of this evaluation edge and the original binary normalization simplex,
reanchored by the original total precomposition node. In particular both entire row faces
retain the original binary triangle and its actual two normalization components.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS
open AlgebraicGeometry.RingedSpace Topology
open scoped Simplicial
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputNormalizationPrism
open GlobalSectionChangeIndex SmallWaldhausenCategory
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The evaluation edge starts at the original strictly precomposed evaluation. -/
def firstSource := boundedAboveFlatGlobalSectionModelFunctor.map h.op ≫ evaluationModel (op Z)

/-- The evaluation edge ends at evaluation followed by the original raw pullback. -/
def firstTarget := evaluationModel (op T) ≫ evaluationRawMap h

/-- Both actual Model arrows of the final evaluation comparison. -/
def firstVertices : Fin 2 → (boundedAboveFlatGlobalSectionModelFunctor.obj (op T) ⟶
    asSmallCategory (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)) :=
  ![firstSource h, firstTarget h]

/-- The only nonidentity first-factor reference is the original evaluation comparison. -/
def firstAnchors : ∀ i, (firstSource h).hom.toFunctor ≅ (firstVertices h i).hom.toFunctor :=
  Fin.cases (Iso.refl _) (Fin.cases (evaluationComparisonIso h) (fun i ↦ Fin.elim0 i))

/-- The original evaluation edge as a complete model simplex. -/
def firstSimplex : ModelSimplex (boundedAboveFlatGlobalSectionModelFunctor.obj (op T))
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace)) 1 :=
  ModelSimplex.ofIsos (firstSource h) (firstVertices h) (firstAnchors h)

/-- Its carrier is exactly the original evaluation transformation. -/
theorem first_edge :
    (firstSimplex h).diagram.map (homOfLE (by decide : (0 : Fin 2) ≤ 1)) =
      (evaluationComparisonIso h).hom := by
  change 𝟙 _ ≫ (evaluationComparisonIso h).hom = _
  exact Category.id_comp _

/-- The second factor uses the original three binary normalization Model arrows. -/
def binaryVertices : Fin 3 → (asSmallCategory (boundedAboveFlatPerfectWaldhausen Z.toRingedSpace) ⟶
    asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) :=
  ![BoundedFlatPerfectBinarySimplex.sourceMap f g,
    BoundedFlatPerfectBinarySimplex.intermediateMap f g,
    BoundedFlatPerfectBinarySimplex.targetMap f g]

/-- These are exactly the original binary normalization references. -/
def binaryAnchors : ∀ i, (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor ≅
    (binaryVertices f g i).hom.toFunctor :=
  Fin.cases (Iso.refl _) (Fin.cases (BoundedFlatPerfectBinarySimplex.first f g)
    (Fin.cases (BoundedFlatPerfectBinarySimplex.total f g) (fun i ↦ Fin.elim0 i)))

/-- The second factor is the unchanged whole original binary simplex. -/
theorem binary_simplex :
    ModelSimplex.ofIsos (BoundedFlatPerfectBinarySimplex.sourceMap f g)
      (binaryVertices f g) (binaryAnchors f g) = BoundedFlatPerfectBinarySimplex.simplex f g := rfl

/-- The first row keeps the full original evaluation-chart references. -/
def preNodes : Fin 3 → InputTripleNodes.Node f g h :=
  ![InputTripleNodes.preNode f g h 1, InputTripleNodes.preNode f g h 2,
    InputTripleNodes.preNode f g h 4]

/-- The second row keeps the actual right-whiskered final evaluation comparisons. -/
def convertedNodes : Fin 3 → InputTripleNodes.Node f g h :=
  ![InputTripleNodes.preTotalNode f g h, InputTripleNodes.preIntermediateNode f g h,
    InputTripleNodes.preTargetNode f g h]

/-- Six complete original nodes in row-major product order. -/
def nodes : Fin 6 → InputTripleNodes.Node f g h :=
  ![InputTripleNodes.preNode f g h 1, InputTripleNodes.preNode f g h 2,
    InputTripleNodes.preNode f g h 4, InputTripleNodes.preTotalNode f g h,
    InputTripleNodes.preIntermediateNode f g h, InputTripleNodes.preTargetNode f g h]

/-- The original total precomposition node supplies the full product reference transport. -/
def anchor : (InputTripleNodes.sourceMap f g h).hom.toFunctor ≅
    (firstSource h ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor :=
  (InputTripleNodes.preNode f g h 1).2

/-- The canonical product references, transported by the actual original total-node anchor. -/
def productNodes (i : Fin 6) : InputTripleNodes.Node f g h :=
  ⟨CommonReferenceProduct.vertices (firstVertices h) (binaryVertices f g) i,
    anchor f g h ≪≫ CommonReferenceProduct.references (firstSource h)
      (firstVertices h) (firstAnchors h) (BoundedFlatPerfectBinarySimplex.sourceMap f g)
      (binaryVertices f g) (binaryAnchors f g) i⟩

/-- The target reference retains the two actual normalization components. -/
theorem normalization_target : evaluationCompositionTargetIso f g =
    isoWhiskerLeft (evaluationModel (op Z)).hom.toFunctor
      (BoundedFlatPerfectBinarySimplex.total f g) := by
  apply Iso.ext
  rw [← InputSimplex.normalization_composite]
  change whiskerLeft (evaluationModel (op Z)).hom.toFunctor
    (BoundedFlatPerfectBinarySimplex.first f g).hom ≫
    whiskerLeft (evaluationModel (op Z)).hom.toFunctor
      (BoundedFlatPerfectBinarySimplex.second f g).hom = _
  rw [← whiskerLeft_comp, BoundedFlatPerfectBinarySimplex.small_composite_hom]
  rfl

/-- Original precomposition references, indexed with the exact binary product targets. -/
def preReferences : ∀ i : Fin 3, (InputTripleNodes.sourceMap f g h).hom.toFunctor ≅
    (firstSource h ≫ binaryVertices f g i).hom.toFunctor :=
  Fin.cases (InputTripleNodes.preNode f g h 1).2
    (Fin.cases (InputTripleNodes.preNode f g h 2).2
      (Fin.cases (InputTripleNodes.preNode f g h 4).2 (fun i ↦ Fin.elim0 i)))

private theorem pre_anchor (i : Fin 3) : preReferences f g h i =
    anchor f g h ≪≫ isoWhiskerLeft (firstSource h).hom.toFunctor (binaryAnchors f g i) := by
  fin_cases i
  · apply Iso.ext
    apply NatTrans.ext
    funext A
    simp only [Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app]
    exact (Category.comp_id _).symm
  · apply Iso.ext
    apply NatTrans.ext
    funext A
    change ((InputTripleNodes.preSourceIso f g h).hom.app A ≫
      ((evaluationComparisonIso (f ≫ g)).hom.app _ ≫
        (BoundedFlatPerfectBinarySimplex.first f g).hom.app _)) =
      (((InputTripleNodes.preSourceIso f g h).hom.app A ≫
        (evaluationComparisonIso (f ≫ g)).hom.app _) ≫
        (BoundedFlatPerfectBinarySimplex.first f g).hom.app _)
    exact (Category.assoc _ _ _).symm
  · apply Iso.ext
    change ((InputTripleNodes.preSourceIso f g h) ≪≫
      isoWhiskerLeft (boundedAboveFlatGlobalSectionModelFunctor.map h.op).hom.toFunctor
        (evaluationComparisonIso (f ≫ g) ≪≫ evaluationCompositionTargetIso f g)).hom = _
    rw [normalization_target]
    apply NatTrans.ext
    funext A
    exact (Category.assoc _ _ _).symm

private theorem node_0_eq : nodes f g h 0 = productNodes f g h 0 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (preReferences f g h 0).hom =
    (anchor f g h ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((Iso.refl _).prod (binaryAnchors f g 0))).hom
  erw [CommonReferenceProduct.composition_pair_iso_other,
    ← Iso.trans_assoc]
  simpa only [isoWhiskerRight_refl, Iso.trans_refl] using
    congrArg Iso.hom (pre_anchor f g h 0)

private theorem node_1_eq : nodes f g h 1 = productNodes f g h 1 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (preReferences f g h 1).hom =
    (anchor f g h ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((Iso.refl _).prod (binaryAnchors f g 1))).hom
  erw [CommonReferenceProduct.composition_pair_iso_other,
    ← Iso.trans_assoc]
  simpa only [isoWhiskerRight_refl, Iso.trans_refl] using
    congrArg Iso.hom (pre_anchor f g h 1)

private theorem node_2_eq : nodes f g h 2 = productNodes f g h 2 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (preReferences f g h 2).hom =
    (anchor f g h ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((Iso.refl _).prod (binaryAnchors f g 2))).hom
  erw [CommonReferenceProduct.composition_pair_iso_other,
    ← Iso.trans_assoc]
  simpa only [isoWhiskerRight_refl, Iso.trans_refl] using
    congrArg Iso.hom (pre_anchor f g h 2)

private theorem converted_reference (i : Fin 3) :
    preReferences f g h i ≪≫ isoWhiskerRight (evaluationComparisonIso h)
      (binaryVertices f g i).hom.toFunctor =
    anchor f g h ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((evaluationComparisonIso h).prod (binaryAnchors f g i)) := by
  calc
    _ = (anchor f g h ≪≫ isoWhiskerLeft (firstSource h).hom.toFunctor (binaryAnchors f g i)) ≪≫
        isoWhiskerRight (evaluationComparisonIso h) (binaryVertices f g i).hom.toFunctor :=
      congrArg (fun e ↦ e ≪≫ isoWhiskerRight (evaluationComparisonIso h)
        (binaryVertices f g i).hom.toFunctor) (pre_anchor f g h i)
    _ = anchor f g h ≪≫
        (isoWhiskerLeft (firstSource h).hom.toFunctor (binaryAnchors f g i) ≪≫
          isoWhiskerRight (evaluationComparisonIso h) (binaryVertices f g i).hom.toFunctor) :=
      Iso.trans_assoc _ _ _
    _ = _ := congrArg (fun e ↦ anchor f g h ≪≫ e)
      (CommonReferenceProduct.composition_pair_iso_other
        (evaluationComparisonIso h) (binaryAnchors f g i)).symm

private theorem node_3_eq : nodes f g h 3 = productNodes f g h 3 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change ((preReferences f g h 0) ≪≫ isoWhiskerRight (evaluationComparisonIso h)
      (binaryVertices f g 0).hom.toFunctor).hom =
    (anchor f g h ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((evaluationComparisonIso h).prod (binaryAnchors f g 0))).hom
  exact congrArg Iso.hom (converted_reference f g h 0)

private theorem node_4_eq : nodes f g h 4 = productNodes f g h 4 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change ((preReferences f g h 1) ≪≫ isoWhiskerRight (evaluationComparisonIso h)
      (binaryVertices f g 1).hom.toFunctor).hom =
    (anchor f g h ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((evaluationComparisonIso h).prod (binaryAnchors f g 1))).hom
  exact congrArg Iso.hom (converted_reference f g h 1)

private theorem node_5_eq : nodes f g h 5 = productNodes f g h 5 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change ((preReferences f g h 2) ≪≫ isoWhiskerRight (evaluationComparisonIso h)
      (binaryVertices f g 2).hom.toFunctor).hom =
    (anchor f g h ≪≫
      (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
        ((evaluationComparisonIso h).prod (binaryAnchors f g 2))).hom
  exact congrArg Iso.hom (converted_reference f g h 2)

/-- Every complete dependent node is the canonical product node, including its full anchor. -/
theorem nodes_eq_productNodes (i : Fin 6) : nodes f g h i = productNodes f g h i := by
  fin_cases i
  · exact node_0_eq f g h
  · exact node_1_eq f g h
  · exact node_2_eq f g h
  · exact node_3_eq f g h
  · exact node_4_eq f g h
  · exact node_5_eq f g h

/-- The six-node prism retains the complete original Model diagram. -/
def simplex : ModelSimplex (boundedAboveFlatGlobalSectionModelFunctor.obj (op T))
    (asSmallCategory (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)) 5 :=
  ModelSimplex.ofIsos (InputTripleNodes.sourceMap f g h)
    (fun i ↦ (nodes f g h i).1) (fun i ↦ (nodes f g h i).2)

/-- The entire original prism is the canonical product of the evaluation edge and binary simplex. -/
theorem product_simplex : simplex f g h =
    CommonReferenceProduct.simplex (firstSource h) (firstVertices h) (firstAnchors h)
      (BoundedFlatPerfectBinarySimplex.sourceMap f g) (binaryVertices f g) (binaryAnchors f g) := by
  unfold simplex
  rw [ModelSimplex.ofIsos_nodes_congr (nodes f g h) (productNodes f g h)
    (nodes_eq_productNodes f g h)]
  exact ModelSimplex.ofIsos_change_reference (anchor f g h) _ _

/-- Both whole row faces are the unchanged original binary triangle after actual precomposition. -/
theorem row_face (i : Fin 2) :
    (simplex f g h).face (SimplexGrid.rowFace 1 2 i) =
      (BoundedFlatPerfectBinarySimplex.simplex f g).precomp (firstVertices h i) := by
  rw [product_simplex]
  change (CommonReferenceProduct.simplex (firstSource h) (firstVertices h) (firstAnchors h)
    (BoundedFlatPerfectBinarySimplex.sourceMap f g) (binaryVertices f g) (binaryAnchors f g)).face
      (CommonReferenceProduct.gridFace (SimplexGrid.constantFace i) (𝟙 ⦋2⦌)) = _
  rw [CommonReferenceProduct.grid_face, ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face,
    ModelSimplex.diagonalComposition_ofIsos]
  simp_rw [CommonReferenceProduct.composition_pair_iso]
  change ModelSimplex.ofIsos (firstSource h ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (fun j ↦ firstVertices h i ≫ binaryVertices f g j)
    (fun j ↦ isoWhiskerRight (firstAnchors h i)
      (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor ≪≫
        isoWhiskerLeft (firstVertices h i).hom.toFunctor (binaryAnchors f g j)) = _
  rw [ModelSimplex.ofIsos_change_reference
    (F₀ := firstSource h ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (F₁ := firstVertices h i ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (isoWhiskerRight (firstAnchors h i)
      (BoundedFlatPerfectBinarySimplex.sourceMap f g).hom.toFunctor)
    (fun j ↦ firstVertices h i ≫ binaryVertices f g j)
    (fun j ↦ isoWhiskerLeft (firstVertices h i).hom.toFunctor (binaryAnchors f g j)),
    ← binary_simplex]
  exact (ModelSimplex.ofIsos_precomp (BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (binaryVertices f g) (binaryAnchors f g) (firstVertices h i)).symm

/-- Each whole column is the original evaluation edge with its actual binary target suffix. -/
theorem column_face (j : Fin 3) :
    (simplex f g h).face (SimplexGrid.columnFace 1 2 j) =
      (firstSimplex h).postcomp (binaryVertices f g j) := by
  rw [product_simplex]
  change (CommonReferenceProduct.simplex (firstSource h) (firstVertices h) (firstAnchors h)
    (BoundedFlatPerfectBinarySimplex.sourceMap f g) (binaryVertices f g) (binaryAnchors f g)).face
      (CommonReferenceProduct.gridFace (𝟙 ⦋1⦌) (SimplexGrid.constantFace j)) = _
  rw [CommonReferenceProduct.grid_face, ModelSimplex.ofIsos_face, ModelSimplex.ofIsos_face,
    ModelSimplex.diagonalComposition_ofIsos]
  simp_rw [CommonReferenceProduct.composition_pair_iso_other]
  change ModelSimplex.ofIsos (firstSource h ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (fun i ↦ firstVertices h i ≫ binaryVertices f g j)
    (fun i ↦ isoWhiskerLeft (firstSource h).hom.toFunctor (binaryAnchors f g j) ≪≫
      isoWhiskerRight (firstAnchors h i) (binaryVertices f g j).hom.toFunctor) = _
  rw [ModelSimplex.ofIsos_change_reference
    (F₀ := firstSource h ≫ BoundedFlatPerfectBinarySimplex.sourceMap f g)
    (F₁ := firstSource h ≫ binaryVertices f g j)
    (isoWhiskerLeft (firstSource h).hom.toFunctor (binaryAnchors f g j))
    (fun i ↦ firstVertices h i ≫ binaryVertices f g j)
    (fun i ↦ isoWhiskerRight (firstAnchors h i) (binaryVertices f g j).hom.toFunctor)]
  exact (ModelSimplex.ofIsos_postcomp (firstSource h) (firstVertices h)
    (firstAnchors h) (binaryVertices f g j)).symm

/-- The original first row is retained as a list of complete dependent nodes. -/
theorem original_row_nodes (i : Fin 3) :
    nodes f g h (SimplexGrid.index 1 2 (0, i)) = preNodes f g h i := by
  fin_cases i <;> rfl

/-- The converted row is retained as a list of complete dependent nodes. -/
theorem converted_row_nodes (i : Fin 3) :
    nodes f g h (SimplexGrid.index 1 2 (1, i)) = convertedNodes f g h i := by
  fin_cases i <;> rfl

/-- Every vertical carrier is literally the original evaluation comparison right-whiskered. -/
theorem column_edge (j : Fin 3) :
    ((firstSimplex h).postcomp (binaryVertices f g j)).diagram.map
        (homOfLE (by decide : (0 : Fin 2) ≤ 1)) =
      whiskerRight (evaluationComparisonIso h).hom (binaryVertices f g j).hom.toFunctor := by
  change whiskerRight ((firstSimplex h).diagram.map
    (homOfLE (by decide : (0 : Fin 2) ≤ 1))) (binaryVertices f g j).hom.toFunctor = _
  rw [first_edge]

end AlgebraicGeometry.Scheme.Modules.GlobalBassEvaluation.InputNormalizationPrism
