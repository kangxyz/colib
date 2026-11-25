/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedLaurentFaces
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentityCarrierUnitSeams

/-!
# Whole original Laurent edges of the fixed seed identity boundary

The three-node positive normalization joins the unchanged old and new rectangle rails before
native evaluation. Both terminal identity edges coincide as complete carrier paths, and the
Laurent identity surface attaches to the original positive unit square at every time.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open CategoryTheory.Waldhausen CategoryTheory.Waldhausen.IteratedS SmallWaldhausenCategory
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters Topology Topology.LoopPrespectrum SSet
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedLaurentSeams
open CommonReferenceNerve ModelSimplex InputIdentitySeedCarrier InputIdentitySeedLaurentFaces

private theorem cancel_anchor {V W : WideSubcategory preservesZero.{u}} {F G : V ⟶ W}
    (a : F.hom.toFunctor ≅ G.hom.toFunctor) (N : Node G) :
    reanchorNode a.symm (reanchorNode a N) = N := by
  rcases N with ⟨H, b⟩
  change (⟨H, a.symm ≪≫ (a ≪≫ b)⟩ : Node G) = ⟨H, b⟩
  simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]

private theorem binary_parameters {V W : WideSubcategory preservesZero.{u}} (F : V ⟶ W) {k l : ℕ}
    (N : Fin (k + 1) → Node F) (M : Fin (l + 1) → Node F)
    (a : ⦋2⦌ ⟶ ⦋k⦌) (b : ⦋2⦌ ⟶ ⦋l⦌)
    (h : ∀ i, N (a.toOrderHom i) = M (b.toOrderHom i)) (s : I) :
    parameter F N (binaryPath (a.toOrderHom 0) (a.toOrderHom 1) (a.toOrderHom 2) s) =
    parameter F M (binaryPath (b.toOrderHom 0) (b.toOrderHom 1) (b.toOrderHom 2) s) := by
  let z := binaryPath (k := 2) 0 1 2 s
  have e := (parameter_face F N a z).trans
    ((congrArg (fun ns ↦ parameter F ns z) (funext h)).trans (parameter_face F M b z).symm)
  dsimp only [z] at e
  rw [BoundedFlatCoefficientBassH0Merged.map_any_binary,
    BoundedFlatCoefficientBassH0Merged.map_any_binary] at e
  exact e

private def oldFace : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![2, 3, 11], by decide⟩
private def newFace : ⦋2⦌ ⟶ ⦋30⦌ :=
  SimplexCategory.Hom.mk ⟨![26, 27, 28], by decide⟩
private def bottomFace : ⦋2⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 3, 6], by decide⟩
private def middleFace : ⦋2⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 2], by decide⟩

variable (X : Scheme.{u})

/-- Back-transport cancels the original full reference on the entire raw simplex. -/
theorem back_raw (z : StdSimplex ℝ (Fin 31)) :
    back X (parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X) z) =
    parameter (laurentRef (𝟙 X)) (InputDescSimplex.nodes (𝟙 X)) z := by
  change mapParameter _ (parameter _ _ z) = _
  rw [mapParameter_parameter]
  apply congrArg (fun N ↦ parameter (laurentRef (𝟙 X)) N z)
  exact funext (fun i ↦ cancel_anchor (InputIdentityNodes.inputSourceIso X)
    (InputDescSimplex.nodes (𝟙 X) i))

/-- Both complete original rectangle sheets use precisely the same returned parameters. -/
theorem sheet_raw (e : Bool) (z : StdSimplex ℝ (Fin 31)) :
    sheet X e (parameter (InputIdentityNodes.source X) (InputIdentityNodes.nodes X) z) =
    InputIdentitySeedRectangle.sheetMap (𝟙 X) e z := by
  dsimp only [sheet, InputIdentitySeedRectangle.sheetMap, ContinuousMap.comp_apply]
  cases e <;> simp only [Bool.false_eq_true, ↓reduceIte,
    ContinuousMap.id_apply, ContinuousMap.comp_apply]
  all_goals rw [back_raw]

/-- The initial target-side grid is the unchanged positive normalization binary path. -/
theorem target_zero_parameter (s : I) :
    targetParameter.{u} (0, s) = binaryPath (k := 14) 0 3 6 s := by
  change SimplexGrid.parameter.{u + 1} 4 2
    (binaryPath (k := 4) 0 1 2 s, binaryPath (k := 2) 0 1 2 0) = _
  rw [Path.source, SimplexGrid.parameter_column]
  exact map_binaryPath (SimplexGrid.columnFace 4 2 0) 0 1 2 s

/-- The source-side grid initially keeps the original positive path in its first row. -/
theorem source_zero_parameter (s : I) :
    sourceParameter.{u} (0, s) = binaryPath (k := 14) 0 1 2 s := by
  change SimplexGrid.parameter.{u + 1} 2 4
    (binaryPath (k := 2) 0 1 2 0, binaryPath (k := 4) 0 1 2 s) = _
  rw [Path.source, SimplexGrid.parameter_row]
  exact map_binaryPath (SimplexGrid.rowFace 2 4 0) 0 1 2 s

/-- The entire Laurent-identity initial edge is the fixed old positive rectangle rail. -/
theorem target_initial (e : Bool) (s : I) :
    targetPositive X e (0, s) = InputIdentitySeedRectangle.oldPositive (𝟙 X) e s := by
  change sheet X e (parameter _ _ (targetParameter.{u} (0, s))) =
    InputIdentitySeedRectangle.sheetMap (𝟙 X) e
      (BoundedFlatPerfectProjectionRectangleParameters.D
        BoundedFlatCoefficientBassH0Diagram.plusFace s)
  rw [target_zero_parameter, ← sheet_raw]
  apply congrArg (sheet X e)
  symm
  apply binary_parameters _ _ _ oldFace bottomFace ?_ s
  intro i
  fin_cases i
  · exact InputIdentityBoundaryNodes.h0_plus_source X 0
  · exact InputIdentityBoundaryNodes.h0_plus_source X 1
  · exact InputIdentityBoundaryNodes.h0_plus_source X 2

/-- The entire source-identity initial edge is the fixed new positive rectangle rail. -/
theorem source_initial (e : Bool) (s : I) :
    sourcePositive X e (0, s) = InputIdentitySeedRectangle.newPositive (𝟙 X) e s := by
  change sheet X e (parameter _ _ (sourceParameter.{u} (0, s))) =
    InputIdentitySeedRectangle.sheetMap (𝟙 X) e
      (BoundedFlatPerfectProjectionRectangleParameters.K
        BoundedFlatCoefficientBassH0Diagram.plusFace s)
  rw [source_zero_parameter, ← sheet_raw]
  apply congrArg (sheet X e)
  symm
  apply binary_parameters _ _ _ newFace middleFace ?_ s
  intro i
  fin_cases i
  · exact InputIdentityBoundaryNodes.h0_plus_target X 0
  · exact InputIdentityBoundaryNodes.h0_plus_target X 1
  · exact InputIdentityBoundaryNodes.h0_plus_target X 2

/-- The two terminal faces share the full original positive path and its whole reference. -/
theorem terminal (e : Bool) (s : I) :
    targetPositive X e (1, s) = sourcePositive X e (1, s) := by
  change sheet X e (parameter _ _ (SimplexGrid.parameter.{u + 1} 4 2
      (binaryPath (k := 4) 0 1 2 s, binaryPath (k := 2) 0 1 2 1))) =
    sheet X e (parameter _ _ (SimplexGrid.parameter.{u + 1} 2 4
      (binaryPath (k := 2) 0 1 2 1, binaryPath (k := 4) 0 1 2 s)))
  rw [Path.target, SimplexGrid.parameter_column, SimplexGrid.parameter_row,
    parameter_face, parameter_face]
  apply congrArg (fun N ↦ sheet X e
    (parameter (InputIdentityNodes.source X) N (binaryPath (k := 4) 0 1 2 s)))
  exact funext (InputIdentityUnitBoundaryNodes.terminal_nodes X)

/-- The whole inner edge of the Laurent identity face meets the fixed plus identity square. -/
theorem target_chart (e : Bool) (r : I) :
    targetPositive X e (r, 1) = chartFace X e (r, 0) := by
  have hp : targetParameter.{u} (r, 1) =
      InputIdentityCarrierBottom.parameter.{u} (r, 0) := by
    change SimplexGrid.parameter.{u + 1} 4 2
      (binaryPath (k := 4) 0 1 2 1, _) =
      SimplexGrid.parameter.{u + 1} 4 2 (InputIdentityProjection.parameter 0, _)
    rw [Path.target, Path.source]
  change sheet X e (parameter _ _ (targetParameter.{u} (r, 1))) = _
  rw [hp]
  exact congrArg (sheet X e)
    (DFunLike.congr_fun (InputIdentityCarrierUnitSeams.bottom_plus X) r)

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedLaurentSeams
