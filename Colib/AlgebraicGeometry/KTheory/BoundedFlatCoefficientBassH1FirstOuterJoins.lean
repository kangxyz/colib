/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Colib.AlgebraicGeometry.KTheory.BoundedFlatCoefficientBassH1FirstOuterRows

/-!
# The complete first half of each original H₁ outer chart word

Both signed five-node words are identified with the original old62 nodes,
including their dependent references. The word order traverses two binary
paths, with one reversed. It is not asserted to be a single monotone face.
Adapted from `H1InternalNodeJoins.lean` and `H1OuterNodeJoins.lean` at Quillen
commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.BaseChange.Coefficients CommRingCat.PolynomialLaurent
open CategoryTheory.Waldhausen.IteratedS

universe u

namespace AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join

open ModelSimplex

/-- The original five-node order of the first-component chart parameter. -/
def chartWordIndex : Fin 5 → Fin 18 := ![9, 10, 11, 12, 13]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The first half of the outer edge retains every original functor and reference node. -/
theorem first_old_chart_word_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (i : Fin 5) :
    postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
      (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (BoundedFlatCoefficientBassH1References.firstIso P u v)
        (BoundedFlatCoefficientBassH0Diagram.chartNodes P u α ha (chartWordIndex i)) =
    BoundedFlatCoefficientBassOverlap.chartOverlapNodes P u v α hc (outerFirstWordIndex i) := by
  fin_cases i
  · exact first_old_chart_center P u v α ha hc
  · exact first_old_outer_first_nodes P u v α ha hc 1
  · exact first_old_outer_first_nodes P u v α ha hc 2
  · exact first_old_outer_second_nodes P u v α ha hc 1
  · exact first_old_outer_second_nodes P u v α ha hc 2

/-- All five first-half positive nodes are the original fixed old62 nodes. -/
theorem first_old62_plus_nodes (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.plusFace.toOrderHom (chartWordIndex i)) =
    BoundedFlatCoefficientBassH0Merged.nodes P u v (BoundedFlatCoefficientBassH0Merged.oldIndex
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.plusFace.toOrderHom (outerFirstWordIndex i)))) := by
  exact (congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (BoundedFlatCoefficientBassH1References.firstIso P u v))
    (BoundedFlatCoefficientBassH0Diagram.plus_nodes P u (chartWordIndex i))).trans
    ((first_old_chart_word_nodes P u v (underToLaurent R)
      (laurentPlus_projection P a) (laurentPlus_projection P c) i).trans
      ((BoundedFlatCoefficientBassOldChartBinaryRows.old_plus_node P u v _).symm.trans
        (BoundedFlatCoefficientBassH0Merged.old_nodes P u v _).symm))

/-- All five first-half inverse nodes retain their separate inverse-coordinate references. -/
theorem first_old62_minus_nodes (i : Fin 5) :
    BoundedFlatCoefficientBassH1References.firstNodes P u v
      (BoundedFlatCoefficientBassH0Diagram.minusFace.toOrderHom (chartWordIndex i)) =
    BoundedFlatCoefficientBassH0Merged.nodes P u v (BoundedFlatCoefficientBassH0Merged.oldIndex
      (BoundedFlatCoefficientBassReferenceMerge.chartFace.toOrderHom
      (BoundedFlatCoefficientBassOverlap.minusFace.toOrderHom (outerFirstWordIndex i)))) := by
  exact (congrArg (postReferenceNode (BoundedFlatCoefficientBassOverlap.commonReference P u v)
    (BoundedFlatCoefficientBassH1Components.laurentMap P v)
      (BoundedFlatCoefficientBassH1References.firstIso P u v))
    (BoundedFlatCoefficientBassH0Diagram.minus_nodes P u (chartWordIndex i))).trans
    ((first_old_chart_word_nodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P a) (laurentMinus_projection P c) i).trans
      ((BoundedFlatCoefficientBassOldChartBinaryRows.old_minus_node P u v _).symm.trans
        (BoundedFlatCoefficientBassH0Merged.old_nodes P u v _).symm))

end AlgebraicGeometry.Scheme.Modules.BoundedFlatCoefficientBassH1Join
