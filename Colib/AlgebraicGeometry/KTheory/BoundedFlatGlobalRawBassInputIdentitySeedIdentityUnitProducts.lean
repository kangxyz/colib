/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedUnitSeams
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedLaurentFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityUnitBoundaryNodes
public import Colib.Topology.Realization.SimplexProductGrid
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceProductColumns

/-!
# Original identity tracks times the actual Laurent scalar edge

The three original source identity vertices and the three original Laurent identity vertices
are composed with the two full references of the original forward scalar unit. Both six-node
products live in the unchanged raw input carrier. Their lower and shifted three-node rows
retain the full references of the prescribed positive identity faces, independently of native
evaluation. Both product clocks and the actual loop level zero are retained.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open Topology.LoopPrespectrum
open CategoryTheory.Waldhausen SmallWaldhausenCategory AlgebraicGeometry.RingedSpace Topology SSet
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedIdentityUnitProducts
open CommonReferenceNerve ModelSimplex InputIdentitySeedCarrier
local notation "WC" => BoundedFlatPerfectTripleSimplex.structureOn

/-- Two references retain an automorphism as an actual scalar edge. -/
def loopReferences {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
    (α : F.hom.toFunctor ≅ F.hom.toFunctor) : Fin 2 → (F.hom.toFunctor ≅ F.hom.toFunctor) :=
  ![Iso.refl _, α]

/-- The original common-reference simplex of a specified automorphism. -/
def loopSimplex {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W)
    (α : F.hom.toFunctor ≅ F.hom.toFunctor) : ModelSimplex V W 1 :=
  ModelSimplex.ofIsos F (fun _ : Fin 2 ↦ F) (loopReferences F α)

private theorem loop_transport {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (h : F.hom.toFunctor = G.hom.toFunctor) (α : G.hom.toFunctor ≅ G.hom.toFunctor) :
    loopSimplex F (eqToIso h ≪≫ α ≪≫ (eqToIso h).symm) = loopSimplex G α := by
  have hFG : F = G := by
    apply WideSubcategory.hom_ext
    exact SmallWaldhausenCategory.Hom.ext h
  subst G
  simp only [eqToIso_refl, Iso.refl_trans, Iso.refl_symm, Iso.trans_refl]

private theorem source_shift_node {V W T : WideSubcategory preservesZero.{u}} (R : V ⟶ T)
    (H₀ H₁ : V ⟶ W) (G : W ⟶ T) (η : R.hom.toFunctor ≅ (H₀ ≫ G).hom.toFunctor)
    (ρ : H₀.hom.toFunctor ≅ H₁.hom.toFunctor) (α : G.hom.toFunctor ≅ G.hom.toFunctor)
    (τ : R.hom.toFunctor ≅ R.hom.toFunctor)
    (h : τ ≪≫ η = η ≪≫ isoWhiskerLeft H₀.hom.toFunctor α) :
    (⟨H₁ ≫ G, η ≪≫ (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      (ρ.prod α)⟩ : Node R) =
    reanchorNode τ ⟨H₁ ≫ G, η ≪≫ (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      (ρ.prod (Iso.refl _))⟩ := by
  apply congrArg (fun θ ↦ (⟨H₁ ≫ G, θ⟩ : Node R))
  rw [CommonReferenceProduct.composition_pair_iso_other,
    CommonReferenceProduct.composition_pair_iso_other]
  simp only [isoWhiskerLeft_refl, Iso.refl_trans]
  rw [← Iso.trans_assoc, ← h, Iso.trans_assoc]

private theorem target_shift_node {V W T : WideSubcategory preservesZero.{u}} (R : V ⟶ T)
    (H : V ⟶ W) (G₀ G₁ : W ⟶ T) (η : R.hom.toFunctor ≅ (H ≫ G₀).hom.toFunctor)
    (α : H.hom.toFunctor ≅ H.hom.toFunctor) (ρ : G₀.hom.toFunctor ≅ G₁.hom.toFunctor)
    (τ : R.hom.toFunctor ≅ R.hom.toFunctor)
    (h : τ ≪≫ η = η ≪≫ isoWhiskerRight α G₀.hom.toFunctor) :
    (⟨H ≫ G₁, η ≪≫ (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      (α.prod ρ)⟩ : Node R) =
    reanchorNode τ ⟨H ≫ G₁, η ≪≫ (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl _).prod ρ)⟩ := by
  apply congrArg (fun θ ↦ (⟨H ≫ G₁, θ⟩ : Node R))
  rw [CommonReferenceProduct.composition_pair_iso, CommonReferenceProduct.composition_pair_iso]
  simp only [isoWhiskerRight_refl, Iso.refl_trans]
  rw [← Iso.trans_assoc, ← h, Iso.trans_assoc]

private theorem left_unit_naturality {V W : WideSubcategory preservesZero.{u}} (H : V ⟶ V)
  (B : V ⟶ W)
    (ρ : H.hom.toFunctor ≅ 𝟭 _) (α : B.hom.toFunctor ≅ B.hom.toFunctor) :
    α ≪≫ (isoWhiskerRight ρ B.hom.toFunctor).symm =
      (isoWhiskerRight ρ B.hom.toFunctor).symm ≪≫ isoWhiskerLeft H.hom.toFunctor α := by
  apply Iso.ext
  ext A
  exact (α.hom.naturality (ρ.inv.app A)).symm

private theorem right_unit_naturality {V W : WideSubcategory preservesZero.{u}} (B : V ⟶ W)
  (H : W ⟶ W)
    (ρ : H.hom.toFunctor ≅ 𝟭 _) (α : B.hom.toFunctor ≅ B.hom.toFunctor) :
    α ≪≫ (isoWhiskerLeft B.hom.toFunctor ρ).symm =
      (isoWhiskerLeft B.hom.toFunctor ρ).symm ≪≫ isoWhiskerRight α H.hom.toFunctor := by
  apply Iso.ext
  ext A
  exact ρ.inv.naturality (α.hom.app A)

private theorem cancel_anchor {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (a : F.hom.toFunctor ≅ G.hom.toFunctor) (N : Node G) :
    reanchorNode a.symm (reanchorNode a N) = N := by
  rcases N with ⟨H, b⟩
  change (⟨H, a.symm ≪≫ (a ≪≫ b)⟩ : Node G) = ⟨H, b⟩
  simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

variable (X : Scheme.{u})

/-- The original positive projection source is the scalar product reference. -/
abbrev scalarSource := InputIdentityProjection.source X

/-- Its equality transport to the unchanged raw Laurent total. -/
def scalarSourceIso : (scalarSource X).hom.toFunctor ≅ (laurentRef (𝟙 X)).hom.toFunctor :=
  eqToIso (InputIdentityNodes.inputSourceEq X)

/-- The original common forward unit, returned through precisely that equality transport. -/
def scalarUnit : (scalarSource X).hom.toFunctor ≅ (scalarSource X).hom.toFunctor :=
  scalarSourceIso X ≪≫ commonUnit (𝟙 X) ≪≫ (scalarSourceIso X).symm

/-- The two equal underlying maps keep their different original scalar references. -/
def scalarVertices : Fin 2 →
    (asSmallCategory (WC X) ⟶
      asSmallCategory (WC (laurent.obj X))) := fun _ ↦ scalarSource X

/-- The unchanged lower and actual forward-unit shifted scalar reference. -/
def scalarReferences : ∀ i, (scalarSource X).hom.toFunctor ≅ (scalarVertices X i).hom.toFunctor :=
  loopReferences (scalarSource X) (scalarUnit X)

/-- The original two-reference scalar simplex. -/
def scalarSimplex := loopSimplex (scalarSource X) (scalarUnit X)

private def scalarFace : ⦋1⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 5], by decide⟩

private theorem scalar_face :
    (InputIdentitySeedUnitNodes.simplex (𝟙 X)).face scalarFace =
      loopSimplex (laurentRef (𝟙 X)) (commonUnit (𝟙 X)) := by
  unfold InputIdentitySeedUnitNodes.simplex
  rw [ModelSimplex.ofIsos_face]
  have h : (fun i : Fin 2 ↦ InputIdentitySeedUnitNodes.nodes (𝟙 X)
      (scalarFace.toOrderHom i)) =
      (fun i : Fin 2 ↦ (⟨laurentRef (𝟙 X),
        loopReferences (laurentRef (𝟙 X)) (commonUnit (𝟙 X)) i⟩ :
          Node (laurentRef (𝟙 X)))) := by
    funext i
    fin_cases i <;> rfl
  exact congrArg (fun N : Fin 2 → Node (laurentRef (𝟙 X)) ↦
    ModelSimplex.ofIsos (laurentRef (𝟙 X)) (fun i ↦ (N i).1) (fun i ↦ (N i).2)) h

/-- The scalar edge is the original unit homotopy at every native level and every time. -/
theorem scalar_native (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    prespectrumSimplexFamily (scalarSimplex X) n (edge (k := 1) 0 1 s, x) =
      (unitHomotopy X).level n (s, x) := by
  have hs : scalarSimplex X =
      (InputIdentitySeedUnitNodes.simplex (𝟙 X)).face scalarFace :=
    (loop_transport (InputIdentityNodes.inputSourceEq X) (commonUnit (𝟙 X))).trans
      (scalar_face X).symm
  refine (congrArg (fun S ↦ prespectrumSimplexFamily S n (edge (k := 1) 0 1 s, x)) hs).trans ?_
  refine (prespectrumSimplexFamily_face (InputIdentitySeedUnitNodes.simplex (𝟙 X))
    scalarFace n (edge (k := 1) 0 1 s) x).symm.trans ?_
  refine (congrArg (fun z ↦ prespectrumSimplexFamily
    (InputIdentitySeedUnitNodes.simplex (𝟙 X)) n (z, x))
    (show StdSimplex.map scalarFace.toOrderHom (edge (k := 1) 0 1 s) =
      InputIdentitySeedUnitNodes.U s from map_edge scalarFace 0 1 s)).trans ?_
  refine (InputIdentitySeedUnitNodes.U_native (𝟙 X) n s x).trans ?_
  have hm : laurent.map (𝟙 X) ≫ laurentProjection.app X = laurentProjection.app X :=
    (congrArg (fun f ↦ f ≫ laurentProjection.app X) (laurent.map_id X)).trans
      (Category.id_comp _)
  exact congrArg (fun f : laurent.obj X ⟶ X ↦
    (boundedAboveFlatPerfectUnitHomotopy f
      (laurentScalar (Opposite.op X))).level n (s, x)) hm

/-- Source identity times scalar unit keeps the original source product reference. -/
abbrev sourceProductSource := BoundedFlatPerfectIdentitySimplex.source X ≫ scalarSource X

/-- Scalar unit times Laurent identity keeps the original target product reference. -/
abbrev targetProductSource := scalarSource X ≫ BoundedFlatPerfectIdentitySimplex.source
  (laurent.obj X)

/-- The source product uses exactly the inverse original input reference. -/
def sourceAnchor : (laurentRef (𝟙 X)).hom.toFunctor ≅ (sourceProductSource X).hom.toFunctor :=
  (InputIdentityNodes.inputSourceIso X).symm

/-- The target product retains the original bottom face reference after returning to raw nodes. -/
def targetAnchor : (laurentRef (𝟙 X)).hom.toFunctor ≅ (targetProductSource X).hom.toFunctor :=
  (InputIdentityNodes.inputSourceIso X).symm ≪≫ InputIdentityCarrierBottom.sourceIso X

/-- Every source product pair retains both factors and their complete reference. -/
def sourcePair (i : Fin 3) (j : Fin 2) : Node (laurentRef (𝟙 X)) :=
  ⟨BoundedFlatPerfectIdentitySimplex.identityVertices X i ≫ scalarVertices X j,
    sourceAnchor X ≪≫ (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((BoundedFlatPerfectIdentitySimplex.identityReferences X i).prod (scalarReferences X j))⟩

/-- Every target product pair retains the original scalar unit and split Laurent identity. -/
def targetPair (i : Fin 2) (j : Fin 3) : Node (laurentRef (𝟙 X)) :=
  ⟨scalarVertices X i ≫ BoundedFlatPerfectIdentitySimplex.identityVertices (laurent.obj X) j,
    targetAnchor X ≪≫ (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((scalarReferences X i).prod (BoundedFlatPerfectIdentitySimplex.identityReferences
        (laurent.obj X) j))⟩

/-- All six actual source product nodes in the standard product order. -/
def sourceNodes (i : Fin 6) : Node (laurentRef (𝟙 X)) :=
  sourcePair X ((SimplexGrid.indexEquiv 2 1).symm i).1 ((SimplexGrid.indexEquiv 2 1).symm i).2

/-- All six actual target product nodes in the standard product order. -/
def targetNodes (i : Fin 6) : Node (laurentRef (𝟙 X)) :=
  targetPair X ((SimplexGrid.indexEquiv 1 2).symm i).1 ((SimplexGrid.indexEquiv 1 2).symm i).2

/-- Decoding preserves the complete source dependent node. -/
theorem source_pair (i : Fin 3) (j : Fin 2) :
    sourceNodes X (SimplexGrid.index 2 1 (i, j)) = sourcePair X i j :=
  congrArg (fun z : Fin 3 × Fin 2 ↦ sourcePair X z.1 z.2)
    (SimplexGrid.decode_index 2 1 (i, j))

/-- Decoding preserves the complete target dependent node. -/
theorem target_pair (i : Fin 2) (j : Fin 3) :
    targetNodes X (SimplexGrid.index 1 2 (i, j)) = targetPair X i j :=
  congrArg (fun z : Fin 2 × Fin 3 ↦ targetPair X z.1 z.2)
    (SimplexGrid.decode_index 1 2 (i, j))

/-- All three lower source references are those of the prescribed original positive face. -/
theorem source_lower_nodes (i : Fin 3) :
    sourcePair X i 0 = reanchorNode (InputIdentityNodes.inputSourceIso X).symm
      (InputIdentityTopNodes.middleNodes X (SimplexGrid.index 2 4 (i, 0))) := by
  rw [InputIdentityTopNodes.middle_pair]
  rfl

/-- All three lower target references are those of the prescribed original positive face. -/
theorem target_lower_nodes (i : Fin 3) :
    targetPair X 0 i = reanchorNode (InputIdentityNodes.inputSourceIso X).symm
      (InputIdentityCarrierBottom.nodes X (SimplexGrid.index 4 2 (0, i))) := by
  have h := congrArg (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)
    (InputIdentityUnitBoundaryNodes.bottom_pair X 0 i)
  refine Eq.trans ?_ h.symm
  exact congrArg (fun η ↦ (⟨scalarSource X ≫ BoundedFlatPerfectIdentitySimplex.identityVertices
    (laurent.obj X) i, η⟩ :
    Node (laurentRef (𝟙 X))))
      (Iso.trans_assoc (InputIdentityNodes.inputSourceIso X).symm
        (InputIdentityCarrierBottom.sourceIso X)
        ((Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
          ((Iso.refl (scalarSource X).hom.toFunctor).prod
            (BoundedFlatPerfectIdentitySimplex.identityReferences (laurent.obj X) i))))


private theorem source_anchor_unit :
    commonUnit (𝟙 X) ≪≫ sourceAnchor X = sourceAnchor X ≪≫
      isoWhiskerLeft (BoundedFlatPerfectIdentitySimplex.source X).hom.toFunctor (scalarUnit X) := by
  have h := left_unit_naturality (BoundedFlatPerfectIdentitySimplex.source X) (scalarSource X)
    (BoundedFlatPerfectIdentitySimplex.first X ≪≫ BoundedFlatPerfectIdentitySimplex.second X)
      (scalarUnit X)
  change scalarUnit X ≪≫ (InputIdentityNodes.sourceToProjection X).symm =
    (InputIdentityNodes.sourceToProjection X).symm ≪≫
      isoWhiskerLeft (BoundedFlatPerfectIdentitySimplex.source X).hom.toFunctor (scalarUnit X) at h
  change commonUnit (𝟙 X) ≪≫
      ((scalarSourceIso X).symm ≪≫ (InputIdentityNodes.sourceToProjection X).symm) =
    ((scalarSourceIso X).symm ≪≫ (InputIdentityNodes.sourceToProjection X).symm) ≪≫ _
  calc
    _ = (scalarSourceIso X).symm ≪≫
        (scalarUnit X ≪≫ (InputIdentityNodes.sourceToProjection X).symm) := by
      simp only [scalarUnit, Iso.trans_assoc, Iso.symm_self_id_assoc]
    _ = _ := by rw [h, ← Iso.trans_assoc]

private theorem target_anchor_eq : targetAnchor X =
    (scalarSourceIso X).symm ≪≫
      (isoWhiskerLeft (scalarSource X).hom.toFunctor
        (BoundedFlatPerfectIdentitySimplex.first (laurent.obj X) ≪≫
          BoundedFlatPerfectIdentitySimplex.second (laurent.obj X))).symm := by
  simp only [targetAnchor, InputIdentityNodes.inputSourceIso,
    InputIdentityCarrierBottom.sourceIso, Iso.trans_symm, Iso.trans_assoc,
      Iso.symm_self_id_assoc]
  rfl

private theorem target_anchor_unit :
    commonUnit (𝟙 X) ≪≫ targetAnchor X = targetAnchor X ≪≫
      isoWhiskerRight (scalarUnit X) (BoundedFlatPerfectIdentitySimplex.source
        (laurent.obj X)).hom.toFunctor := by
  rw [target_anchor_eq]
  have h := right_unit_naturality (scalarSource X) (BoundedFlatPerfectIdentitySimplex.source
    (laurent.obj X))
    (BoundedFlatPerfectIdentitySimplex.first (laurent.obj X) ≪≫
      BoundedFlatPerfectIdentitySimplex.second (laurent.obj X)) (scalarUnit X)
  calc
    _ = (scalarSourceIso X).symm ≪≫ (scalarUnit X ≪≫
        (isoWhiskerLeft (scalarSource X).hom.toFunctor
          (BoundedFlatPerfectIdentitySimplex.first (laurent.obj X) ≪≫
            BoundedFlatPerfectIdentitySimplex.second (laurent.obj X))).symm) := by
      simp only [scalarUnit, Iso.trans_assoc, Iso.symm_self_id_assoc]
    _ = _ := by rw [h, ← Iso.trans_assoc]

/-- Every upper source identity vertex is exactly the actual unit-shifted lower vertex. -/
theorem source_upper_nodes (i : Fin 3) :
    sourcePair X i 1 = reanchorNode (commonUnit (𝟙 X)) (sourcePair X i 0) :=
  source_shift_node (laurentRef (𝟙 X)) (BoundedFlatPerfectIdentitySimplex.source X)
    (BoundedFlatPerfectIdentitySimplex.identityVertices X i)
    (scalarSource X) (sourceAnchor X) (BoundedFlatPerfectIdentitySimplex.identityReferences X i)
      (scalarUnit X)
    (commonUnit (𝟙 X)) (source_anchor_unit X)

/-- Every upper Laurent identity vertex retains the distinct actual shifted reference. -/
theorem target_upper_nodes (i : Fin 3) :
    targetPair X 1 i = reanchorNode (commonUnit (𝟙 X)) (targetPair X 0 i) :=
  target_shift_node (laurentRef (𝟙 X)) (scalarSource X)
    (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
    (BoundedFlatPerfectIdentitySimplex.identityVertices (laurent.obj X) i) (targetAnchor X)
      (scalarUnit X)
    (BoundedFlatPerfectIdentitySimplex.identityReferences (laurent.obj X) i) (commonUnit (𝟙 X))
      (target_anchor_unit X)

/-- Source identity time and the original scalar-unit time are independent coordinates. -/
def sourceParameter : C(I × I, StdSimplex ℝ (Fin 6)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 2 1
    (binaryPath (k := 2) 0 1 2 z.1, edge (k := 1) 0 1 z.2), by fun_prop⟩

/-- The target product has the same clocks, in the opposite product order. -/
def targetParameter : C(I × I, StdSimplex ℝ (Fin 6)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 1 2
    (edge (k := 1) 0 1 z.2, binaryPath (k := 2) 0 1 2 z.1), by fun_prop⟩

/-- The actual source identity followed by the original Laurent unit inside the fixed carrier. -/
def source : C(I × I, Carrier (𝟙 X)) :=
  (InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)).comp
    ((parameter (laurentRef (𝟙 X)) (sourceNodes X)).comp sourceParameter.{u})

/-- The actual Laurent identity after the original forward unit inside that same carrier. -/
def target : C(I × I, Carrier (𝟙 X)) :=
  (InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)).comp
    ((parameter (laurentRef (𝟙 X)) (targetNodes X)).comp targetParameter.{u})

private theorem source_family :
    ModelSimplex.ofIsos (laurentRef (𝟙 X)) (fun i ↦ (sourceNodes X i).1)
      (fun i ↦ (sourceNodes X i).2) =
    CommonReferenceProduct.simplex (BoundedFlatPerfectIdentitySimplex.source X)
      (BoundedFlatPerfectIdentitySimplex.identityVertices X)
      (BoundedFlatPerfectIdentitySimplex.identityReferences X)
      (scalarSource X) (scalarVertices X) (scalarReferences X) :=
  ModelSimplex.ofIsos_change_reference (sourceAnchor X) _ _

private theorem target_family :
    ModelSimplex.ofIsos (laurentRef (𝟙 X)) (fun i ↦ (targetNodes X i).1)
      (fun i ↦ (targetNodes X i).2) =
    CommonReferenceProduct.simplex (scalarSource X) (scalarVertices X) (scalarReferences X)
      (BoundedFlatPerfectIdentitySimplex.source (laurent.obj X))
        (BoundedFlatPerfectIdentitySimplex.identityVertices (laurent.obj X))
      (BoundedFlatPerfectIdentitySimplex.identityReferences (laurent.obj X)) :=
  ModelSimplex.ofIsos_change_reference (targetAnchor X) _ _

/-- Every native value is the original scalar unit after the unchanged source identity track. -/
theorem source_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (source X (r, s)) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      ((unitHomotopy X).level n
        (s, (boundedAboveFlatPerfectPullbackPrespectrumIdHomotopy X).level n (r, x))) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (CutOpenCarrier.laurentInclusion _ _ _ _ _ (parameter _ _ _)) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion]
  apply congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
  rw [pointwisePrespectrumFamily_parameter, source_family]
  refine (CommonReferenceProduct.prespectrum_comp (BoundedFlatPerfectIdentitySimplex.source X)
    (BoundedFlatPerfectIdentitySimplex.identityVertices X)
      (BoundedFlatPerfectIdentitySimplex.identityReferences X) (scalarSource X)
    (scalarVertices X) (scalarReferences X) n x
    (binaryPath (k := 2) 0 1 2 r) (edge (k := 1) 0 1 s)).trans ?_
  exact (scalar_native X n s _).trans
    (congrArg (fun y ↦ (unitHomotopy X).level n (s, y))
      (BoundedFlatPerfectIdentitySimplex.identity_native X n r x))

/-- Every native value is the unchanged Laurent identity after the original scalar unit. -/
theorem target_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedAboveFlatPerfectWaldhausen X.toRingedSpace)).space n) :
    CutOpenCarrier.nativeEval (polyRef (𝟙 X)) (chart (X := X)) (laurentRef (𝟙 X))
      (ordinary (𝟙 X)) (shifted (𝟙 X)) n (target X (r, s)) x =
    (mappingConeInclusion (InputIdentityPositive.chart X)).map n
      ((InputIdentity.laurentHomotopy X).level n
        (r, (unitHomotopy X).level n (s, x))) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (CutOpenCarrier.laurentInclusion _ _ _ _ _ (parameter _ _ _)) x = _
  rw [CutOpenCarrier.nativeEval_laurentInclusion]
  apply congrArg ((mappingConeInclusion (InputIdentityPositive.chart X)).map n)
  rw [pointwisePrespectrumFamily_parameter, target_family]
  refine (CommonReferenceProduct.prespectrum_comp (scalarSource X)
    (scalarVertices X) (scalarReferences X) (BoundedFlatPerfectIdentitySimplex.source
      (laurent.obj X))
    (BoundedFlatPerfectIdentitySimplex.identityVertices (laurent.obj X))
      (BoundedFlatPerfectIdentitySimplex.identityReferences (laurent.obj X)) n x
    (edge (k := 1) 0 1 s) (binaryPath (k := 2) 0 1 2 r)).trans ?_
  exact (InputIdentityCarrierBottom.laurent_native X n r _).trans
    (congrArg (fun y ↦ (InputIdentity.laurentHomotopy X).level n (r, y))
      (scalar_native X n s x))

/-- The whole lower source edge is the prescribed positive face at its original scalar source. -/
theorem source_zero (r : I) :
    source X (r, 0) = InputIdentitySeedLaurentFaces.sourcePositive X false (r, 0) := by
  change InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (SimplexGrid.parameter.{u + 1} 2 1
        (binaryPath (k := 2) 0 1 2 r, edge (k := 1) 0 1 0))) =
    InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (mapParameter (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)
        (parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
          (binaryPath (k := 2) 0 1 2 r, binaryPath (k := 4) 0 1 2 0))))
  simp only [Path.source, SimplexGrid.parameter_column, parameter_face, mapParameter_parameter]
  apply congrArg (fun N ↦ InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
    (parameter (laurentRef (𝟙 X)) N (binaryPath (k := 2) 0 1 2 r)))
  exact funext (fun i ↦ (source_pair X i 0).trans (source_lower_nodes X i))

/-- The whole upper source edge retains the separate original forward-unit reference. -/
theorem source_one (r : I) :
    source X (r, 1) = InputIdentitySeedLaurentFaces.sourcePositive X true (r, 0) := by
  change InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (SimplexGrid.parameter.{u + 1} 2 1
        (binaryPath (k := 2) 0 1 2 r, edge (k := 1) 0 1 1))) =
    InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (mapParameter (reanchorNode (commonUnit (𝟙 X)))
        (mapParameter (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)
          (parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
            (binaryPath (k := 2) 0 1 2 r, binaryPath (k := 4) 0 1 2 0)))))
  simp only [Path.target, Path.source, SimplexGrid.parameter_column,
    parameter_face, mapParameter_parameter]
  apply congrArg (fun N ↦ InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
    (parameter (laurentRef (𝟙 X)) N (binaryPath (k := 2) 0 1 2 r)))
  exact funext (fun i ↦ (source_pair X i 1).trans ((source_upper_nodes X i).trans
    (congrArg (reanchorNode (commonUnit (𝟙 X))) (source_lower_nodes X i))))

/-- The whole lower target edge is the actual positive face at its original source vertex. -/
theorem target_zero (r : I) :
    target X (r, 0) = InputIdentitySeedLaurentFaces.targetPositive X false (r, 0) := by
  change InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (SimplexGrid.parameter.{u + 1} 1 2
        (edge (k := 1) 0 1 0, binaryPath (k := 2) 0 1 2 r))) =
    InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (mapParameter (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)
        (parameter _ _ (SimplexGrid.parameter.{u + 1} 4 2
          (binaryPath (k := 4) 0 1 2 0, binaryPath (k := 2) 0 1 2 r))))
  simp only [Path.source, SimplexGrid.parameter_row, parameter_face, mapParameter_parameter]
  apply congrArg (fun N ↦ InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
    (parameter (laurentRef (𝟙 X)) N (binaryPath (k := 2) 0 1 2 r)))
  exact funext (fun i ↦ (target_pair X 0 i).trans (target_lower_nodes X i))

/-- The entire upper target row is the full common-unit shift of the prescribed target face. -/
theorem target_one (r : I) :
    target X (r, 1) = InputIdentitySeedLaurentFaces.targetPositive X true (r, 0) := by
  change InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (SimplexGrid.parameter.{u + 1} 1 2
        (edge (k := 1) 0 1 1, binaryPath (k := 2) 0 1 2 r))) =
    InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (mapParameter (reanchorNode (commonUnit (𝟙 X)))
        (mapParameter (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)
          (parameter _ _ (SimplexGrid.parameter.{u + 1} 4 2
            (binaryPath (k := 4) 0 1 2 0, binaryPath (k := 2) 0 1 2 r)))))
  simp only [Path.target, Path.source, SimplexGrid.parameter_row,
    parameter_face, mapParameter_parameter]
  apply congrArg (fun N ↦ InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
    (parameter (laurentRef (𝟙 X)) N (binaryPath (k := 2) 0 1 2 r)))
  exact funext (fun i ↦ (target_pair X 1 i).trans ((target_upper_nodes X i).trans
    (congrArg (reanchorNode (commonUnit (𝟙 X))) (target_lower_nodes X i))))

private theorem source_initial_raw : sourcePair X 0 0 = InputDescSimplex.nodes (𝟙 X) 26 := by
  refine (source_lower_nodes X 0).trans ?_
  refine (congrArg (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)
    (InputIdentityBoundaryNodes.h0_plus_target X 0).symm).trans ?_
  exact cancel_anchor (InputIdentityNodes.inputSourceIso X) (InputDescSimplex.nodes (𝟙 X) 26)

private theorem target_initial_raw : targetPair X 0 0 = InputDescSimplex.nodes (𝟙 X) 2 := by
  refine (target_lower_nodes X 0).trans ?_
  refine (congrArg (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)
    (InputIdentityBoundaryNodes.h0_plus_source X 0).symm).trans ?_
  exact cancel_anchor (InputIdentityNodes.inputSourceIso X) (InputDescSimplex.nodes (𝟙 X) 2)

/-- The source product's original scalar edge has precisely the two full W references. -/
theorem source_initial_nodes (i : Fin 2) :
    sourcePair X 0 i = InputIdentitySeedUnitNodes.nodes (𝟙 X) (![4, 9] i) := by
  fin_cases i
  · exact (source_initial_raw X).trans (InputIdentitySeedUnitSeams.ordinary_endpoints (𝟙 X)).2
  · exact (source_upper_nodes X 0).trans
      ((congrArg (reanchorNode (commonUnit (𝟙 X))) (source_initial_raw X)).trans
        (InputIdentitySeedUnitSeams.shifted_endpoints (𝟙 X)).2)

/-- The target product's original scalar edge has precisely the two full V references. -/
theorem target_initial_nodes (i : Fin 2) :
    targetPair X i 0 = InputIdentitySeedUnitNodes.nodes (𝟙 X) (![2, 7] i) := by
  fin_cases i
  · exact (target_initial_raw X).trans (InputIdentitySeedUnitSeams.ordinary_endpoints (𝟙 X)).1
  · exact (target_upper_nodes X 0).trans
      ((congrArg (reanchorNode (commonUnit (𝟙 X))) (target_initial_raw X)).trans
        (InputIdentitySeedUnitSeams.shifted_endpoints (𝟙 X)).1)

private def sourceUnitFace : ⦋1⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![4, 9], by decide⟩
private def targetUnitFace : ⦋1⦌ ⟶ ⦋9⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 7], by decide⟩

/-- The whole initial source scalar edge is the existing W rail, with its original clock. -/
theorem source_initial (s : I) :
    source X (0, s) = InputIdentitySeedUnitSeams.newUnit (𝟙 X) s := by
  change InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (SimplexGrid.parameter.{u + 1} 2 1
        (binaryPath (k := 2) 0 1 2 0, edge (k := 1) 0 1 s))) =
    InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (InputIdentitySeedUnitNodes.W s))
  rw [Path.source, SimplexGrid.parameter_row]
  apply congrArg (InputIdentitySeedUnitSeams.includeLaurent (𝟙 X))
  let z := edge (k := 1) 0 1 s
  have hl := parameter_face (laurentRef (𝟙 X)) (sourceNodes X) (SimplexGrid.rowFace 2 1 0) z
  have hr := parameter_face (laurentRef (𝟙 X)) (InputIdentitySeedUnitNodes.nodes (𝟙 X))
    sourceUnitFace z
  have hn (i : Fin 2) :
      sourceNodes X ((SimplexGrid.rowFace 2 1 0).toOrderHom i) =
        InputIdentitySeedUnitNodes.nodes (𝟙 X) (sourceUnitFace.toOrderHom i) :=
    (source_pair X 0 i).trans (source_initial_nodes X i)
  have hh := hl.trans ((congrArg (fun N ↦ parameter (laurentRef (𝟙 X)) N z)
    (funext hn)).trans hr.symm)
  exact hh.trans (congrArg (parameter (laurentRef (𝟙 X))
    (InputIdentitySeedUnitNodes.nodes (𝟙 X)))
    (show StdSimplex.map sourceUnitFace.toOrderHom z = InputIdentitySeedUnitNodes.W s
      from map_edge sourceUnitFace 0 1 s))

/-- The whole initial target scalar edge is the original V rail, before native evaluation. -/
theorem target_initial (s : I) :
    target X (0, s) = InputIdentitySeedUnitSeams.oldUnit (𝟙 X) s := by
  change InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (SimplexGrid.parameter.{u + 1} 1 2
        (edge (k := 1) 0 1 s, binaryPath (k := 2) 0 1 2 0))) =
    InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (InputIdentitySeedUnitNodes.V s))
  rw [Path.source, SimplexGrid.parameter_column]
  apply congrArg (InputIdentitySeedUnitSeams.includeLaurent (𝟙 X))
  let z := edge (k := 1) 0 1 s
  have hl := parameter_face (laurentRef (𝟙 X)) (targetNodes X) (SimplexGrid.columnFace 1 2 0) z
  have hr := parameter_face (laurentRef (𝟙 X)) (InputIdentitySeedUnitNodes.nodes (𝟙 X))
    targetUnitFace z
  have hn (i : Fin 2) :
      targetNodes X ((SimplexGrid.columnFace 1 2 0).toOrderHom i) =
        InputIdentitySeedUnitNodes.nodes (𝟙 X) (targetUnitFace.toOrderHom i) :=
    (target_pair X i 0).trans (target_initial_nodes X i)
  have hh := hl.trans ((congrArg (fun N ↦ parameter (laurentRef (𝟙 X)) N z)
    (funext hn)).trans hr.symm)
  exact hh.trans (congrArg (parameter (laurentRef (𝟙 X))
    (InputIdentitySeedUnitNodes.nodes (𝟙 X)))
    (show StdSimplex.map targetUnitFace.toOrderHom z = InputIdentitySeedUnitNodes.V s
      from map_edge targetUnitFace 0 1 s))

/-- Both final scalar edges retain the same complete lower and shifted dependent nodes. -/
theorem terminal_nodes (i : Fin 2) : sourcePair X 2 i = targetPair X i 2 := by
  have h : sourcePair X 2 0 = targetPair X 0 2 := by
    rw [source_lower_nodes, target_lower_nodes]
    exact congrArg (reanchorNode (InputIdentityNodes.inputSourceIso X).symm)
      (InputIdentityUnitBoundaryNodes.terminal_nodes X 0).symm
  fin_cases i
  · exact h
  · change sourcePair X 2 1 = targetPair X 1 2
    rw [source_upper_nodes, target_upper_nodes, h]

/-- The two actual product surfaces share their entire terminal scalar-unit path. -/
theorem terminal (s : I) : source X (1, s) = target X (1, s) := by
  change InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (SimplexGrid.parameter.{u + 1} 2 1
        (binaryPath (k := 2) 0 1 2 1, edge (k := 1) 0 1 s))) =
    InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
      (parameter _ _ (SimplexGrid.parameter.{u + 1} 1 2
        (edge (k := 1) 0 1 s, binaryPath (k := 2) 0 1 2 1)))
  simp only [Path.target]
  rw [SimplexGrid.parameter_row, SimplexGrid.parameter_column, parameter_face, parameter_face]
  apply congrArg (fun N ↦ InputIdentitySeedUnitSeams.includeLaurent (𝟙 X)
    (parameter (laurentRef (𝟙 X)) N (edge (k := 1) 0 1 s)))
  exact funext (fun i ↦ (source_pair X 2 i).trans
    ((terminal_nodes X i).trans (target_pair X i 2).symm))

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedIdentityUnitProducts
