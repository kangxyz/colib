/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassUnitTopMiddle
public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceProductColumns

/-!
# The five actual shared terminal projection nodes of the raw Bass identity

Decoding the two original grids and cancelling their terminal unit references identifies
the whole dependent nodes. Adapted from `CoefficientBassUnitBoundaryNodes.lean`
and `CoefficientPolynomialSpanUnitNodes.lean` at Quillen
`c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CategoryTheory.Waldhausen.IteratedS
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTerminalNodes

local notation "W" => BoundedFlatPerfectTripleSimplex.structureOn
local notation "idFirst" => BoundedFlatPerfectIdentitySimplex.first
local notation "idRefs" => BoundedFlatPerfectIdentitySimplex.identityReferences
local notation "idVertices" => BoundedFlatPerfectIdentitySimplex.identityVertices
local notation "idSecond" => BoundedFlatPerfectIdentitySimplex.second
local notation "bassProjNodes" => BoundedFlatCoefficientBassProjectionPath.nodes
local notation "bassProjSource" => BoundedFlatCoefficientBassProjectionPath.source
local notation "unitBottomBottomSourceIso" => BoundedFlatCoefficientBassUnitBottom.bottomSourceIso
local notation "unitBottomNodes" => BoundedFlatCoefficientBassUnitBottom.nodes
local notation "bottomSrc" => BoundedFlatCoefficientBassUnitBottom.source
local notation "bottomToProj" => BoundedFlatCoefficientBassUnitBottom.sourceToProjection
local notation "unitMiddleNodes" => BoundedFlatCoefficientBassUnitTopMiddle.nodes

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

local notation "A" => space (op P, a)
local notation "L" => space (op P, Functor.obj (laurentUnderFunctor R) a)

/-- The whole bottom reference at the displayed projection and identity coordinates. -/
def bottomPairReference (j : Fin 5) (k : Fin 3) :
    (bottomSrc P a).hom.toFunctor ≅
    ((bassProjNodes P a j).1 ≫ idVertices L k).hom.toFunctor :=
  unitBottomBottomSourceIso P a ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((bassProjNodes P a j).2.prod (idRefs L k))

/-- The entire bottom dependent node is the actual projection-by-identity product node. -/
theorem bottom_pair (j : Fin 5) (k : Fin 3) :
    unitBottomNodes P a (Topology.SimplexGrid.index 4 2 (j, k)) =
      ⟨(bassProjNodes P a j).1 ≫ idVertices L k, bottomPairReference P a j k⟩ := by
  let node (z : Fin 5 × Fin 3) :
      Σ F : asSmallCategory (W A) ⟶ asSmallCategory (W L),
        (bottomSrc P a).hom.toFunctor ≅ F.hom.toFunctor :=
    ⟨(bassProjNodes P a z.1).1 ≫ idVertices L z.2, bottomPairReference P a z.1 z.2⟩
  change node ((Topology.SimplexGrid.indexEquiv 4 2).symm
    (Topology.SimplexGrid.index 4 2 (j, k))) = node (j, k)
  exact congrArg node (Topology.SimplexGrid.decode_index 4 2 (j, k))

/-- The whole middle reference at the displayed identity and projection coordinates. -/
def middlePairReference (k : Fin 3) (j : Fin 5) :
    (bottomSrc P a).hom.toFunctor ≅
      (idVertices A k ≫ (bassProjNodes P a j).1).hom.toFunctor :=
  (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
    ((idRefs A k).prod (bassProjNodes P a j).2)

/-- The entire middle dependent node is the actual identity-by-projection product node. -/
theorem middle_pair (k : Fin 3) (j : Fin 5) :
    unitMiddleNodes P a (Topology.SimplexGrid.index 2 4 (k, j)) =
      ⟨idVertices A k ≫ (bassProjNodes P a j).1, middlePairReference P a k j⟩ := by
  let node (z : Fin 3 × Fin 5) :
      Σ F : asSmallCategory (W A) ⟶ asSmallCategory (W L),
        (bottomSrc P a).hom.toFunctor ≅ F.hom.toFunctor :=
    ⟨idVertices A z.1 ≫ (bassProjNodes P a z.2).1, middlePairReference P a z.1 z.2⟩
  change node ((Topology.SimplexGrid.indexEquiv 2 4).symm
    (Topology.SimplexGrid.index 2 4 (k, j))) = node (k, j)
  exact congrArg node (Topology.SimplexGrid.decode_index 2 4 (k, j))

/-- The original Laurent unit cancels at the terminal row, keeping the full projection reference. -/
theorem bottom_terminal_reference (j : Fin 5) :
    bottomPairReference P a j 2 = bottomToProj P a ≪≫ (bassProjNodes P a j).2 := by
  unfold bottomPairReference
  rw [CommonReferenceProduct.composition_pair_iso_other]
  let e := isoWhiskerLeft (bassProjSource P a).hom.toFunctor (idFirst L ≪≫ idSecond L)
  change (bottomToProj P a ≪≫ e.symm) ≪≫ (e ≪≫ (bassProjNodes P a j).2) = _
  rw [Iso.trans_assoc (bottomToProj P a) e.symm, ← Iso.trans_assoc e.symm e,
    Iso.symm_self_id, Iso.refl_trans]

/-- The original base unit gives the same projection reference at the other terminal. -/
theorem middle_terminal_reference (j : Fin 5) :
    middlePairReference P a 2 j = bottomToProj P a ≪≫ (bassProjNodes P a j).2 := by
  unfold middlePairReference
  rw [CommonReferenceProduct.composition_pair_iso]
  rfl

/-- All five original terminal collisions identify the full nodes, including normalization data. -/
theorem terminal_nodes (j : Fin 5) :
    unitBottomNodes P a (Topology.SimplexGrid.index 4 2 (j, 2)) =
      unitMiddleNodes P a (Topology.SimplexGrid.index 2 4 (2, j)) := by
  rw [bottom_pair, middle_pair]
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id]
  rw [bottom_terminal_reference, middle_terminal_reference]

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassUnitTerminalNodes
