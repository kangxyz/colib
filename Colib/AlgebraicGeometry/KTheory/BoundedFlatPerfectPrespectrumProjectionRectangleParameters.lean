/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH0Diagram
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectPrespectrumDoubleSquareRectangleParameter
public import Colib.KTheory.Waldhausen.Iterated.SimplexPathEmbedding

/-!
# Literal geometric rectangle parameters in the shared H0 simplex

Adapted from Quillen
`AlgebraicGeometry/PerfectComplexes/BoundedFlat/ProjectionRectangleParameters.lean:18-76`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The two chart rectangles use the same five-vertex outer path.
-/

@[expose] public noncomputable section

open CategoryTheory Convexity Topology
open CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionRectangleParameters
variable {k : ℕ} (α : ⦋17⦌ ⟶ ⦋k⦌)

/-- The source-chart binary path through rectangle vertices `2, 3, 11`, relabeled by `α`. -/
abbrev D := binaryPath (α.toOrderHom 2) (α.toOrderHom 3) (α.toOrderHom 11)
/--
The reversed source-total path followed by the target-total path, with vertex word `2, 1, 0, 14,
15` relabeled by `α`.
-/
abbrev T := (binaryPath (α.toOrderHom 0) (α.toOrderHom 1) (α.toOrderHom 2)).symm.trans
  (binaryPath (α.toOrderHom 0) (α.toOrderHom 14) (α.toOrderHom 15))
/-- The target-chart binary path through rectangle vertices `15, 16, 17`, relabeled by `α`. -/
abbrev K := binaryPath (α.toOrderHom 15) (α.toOrderHom 16) (α.toOrderHom 17)
/-- The first square comparison with vertex word `11, 10, 9, 12, 13`, relabeled by `α`. -/
abbrev L := (binaryPath (α.toOrderHom 9) (α.toOrderHom 10) (α.toOrderHom 11)).symm.trans
  (binaryPath (α.toOrderHom 9) (α.toOrderHom 12) (α.toOrderHom 13))
/-- The second square comparison with vertex word `13, 6, 5, 7, 17`, relabeled by `α`. -/
abbrev Ppath := (binaryPath (α.toOrderHom 5) (α.toOrderHom 6) (α.toOrderHom 13)).symm.trans
  (binaryPath (α.toOrderHom 5) (α.toOrderHom 7) (α.toOrderHom 17))

private theorem map_binary_symm (i j m : Fin 18) (t : unitInterval) :
    embed α ((binaryPath i j m).symm t) =
      (binaryPath (α.toOrderHom i) (α.toOrderHom j) (α.toOrderHom m)).symm t :=
  map_binaryPath α i j m (unitInterval.symm t)

/-- Whole original source word, including both native square paths and their exact speeds. -/
theorem source_mapped (t : unitInterval) :
    embed α (((BoundedFlatPerfectDoubleSquareScalarPaths.firstRestriction.symm.trans
      BoundedFlatPerfectDoubleSquareScalarPaths.secondRestriction).trans
        (BoundedFlatPerfectDoubleSquareScalarPaths.middleChart.symm.trans
          BoundedFlatPerfectDoubleSquareScalarPaths.lastRestriction)) t) =
      ((L α).trans (Ppath α)) t :=
  map_trans_values (embed α) _ _ _ _
    (map_trans_values (embed α) _ _ _ _ (map_binary_symm α 9 10 11) (map_binaryPath α 9 12 13))
    (map_trans_values (embed α) _ _ _ _ (map_binary_symm α 5 6 13) (map_binaryPath α 5 7 17)) t

/-- Whole original outer route; its central path will be shared by the two chart embeddings. -/
theorem target_mapped (t : unitInterval) :
    embed α ((BoundedFlatPerfectDoubleSquareScalarPaths.sourceChart.symm.trans
      ((BoundedFlatPerfectDoubleSquareScalarPaths.sourceTotal.symm.trans
        BoundedFlatPerfectDoubleSquareScalarPaths.targetTotal).trans
        BoundedFlatPerfectDoubleSquareScalarPaths.targetChart)) t) =
      ((D α).symm.trans ((T α).trans (K α))) t :=
  map_trans_values (embed α) _ _ _ _ (map_binary_symm α 2 3 11)
    (map_trans_values (embed α) _ _ _ _
      (map_trans_values (embed α) _ _ _ _ (map_binary_symm α 0 1 2) (map_binaryPath α 0 14 15))
      (map_binaryPath α 15 16 17)) t

/-- The original entire rectangle surface, with only its complete scalar face embedded. -/
def rectangle : ((L α).trans (Ppath α)).Homotopy ((D α).symm.trans ((T α).trans (K α))) :=
  Path.Homotopy.mapOfPaths (embed α)
    BoundedFlatPerfectDoubleSquareScalarPaths.rectangleParameter _ _
      (source_mapped α) (target_mapped α)

end AlgebraicGeometry.Scheme.Modules.BoundedFlatPerfectProjectionRectangleParameters
namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Diagram
open BoundedFlatPerfectProjectionRectangleParameters

/-- Both projection rectangles use literally the same scalar outer path. -/
theorem common_outer_path : T plusFace = T minusFace := rfl

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH0Diagram
