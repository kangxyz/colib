/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteOriginalPairEuler

/-! Literal endpoint consumers. Source-only; no compilation or kernel check performed. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open Stacks.ModuleStalkSpecialization
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

example [IsSeparated h]
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRightRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRightRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q)
    (n : ℕ) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y))) (a : ℕ) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let F := correspondenceRightIntermediateSupportProduct f g h i z w v
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let Q := E.presheaf.stalk q
    let a₀ := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y
    let P := F.presheaf.stalk a₀
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π a₀)
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v y
    let ρ := correspondenceRightRemainingFiniteModelProjection f g h i z w v x
    let T := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x
    let sP := fun j => κ ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j))
    let eY := (pullback g g).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x y hy))
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    letI := stalkModule (T n) q
    letI := correspondenceIncidenceTorModule g h i w v (π a₀) n
    letI : Algebra P₀ P := (π.stalkMap a₀).hom.toAlgebra
    Module.length Q
      ((Koszul.seqComplexTensor (fun j => E.presheaf.germ ⊤ q trivial
        (algebraMap R B (α (eY.inv (s j))))) ((T n).presheaf.stalk q)).homology a) =
      Module.length P ((Koszul.seqComplexTensor sP
        (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π a₀) n)).homology a) := by
  exact length_correspondenceRightRemainingFiniteTorStalkKoszul_eq_originalPair
    f g h i z w v x q hq y hy hρ n s a

example [IsSeparated h]
    (x : correspondenceRightImageIncidence f g h i z w v)
    (q : correspondenceRightRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRightRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRightRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToRightImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y =
      correspondenceRightRemainingFiniteModelProjection f g h i z w v x q)
    (n : ℕ) {r : ℕ}
    (s : Fin r → (pullback g g).presheaf.stalk
      (correspondenceSixfoldFirstMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y))) :
    let E := correspondenceRightRemainingFiniteModel f g h i z w v x
    let F := correspondenceRightIntermediateSupportProduct f g h i z w v
    let R := correspondenceRightRemainingImageStalk f g h i z w v x
    let B := correspondenceRightRemainingFiniteRing f g h i z w v x
    let Q := E.presheaf.stalk q
    let a₀ := correspondenceTripleIncidenceToRightSupportProduct f g h i z w v y
    let P := F.presheaf.stalk a₀
    let π := correspondenceRightExteriorProjection f g h i z w v
    let P₀ := (correspondenceIncidence g h i w v).presheaf.stalk (π a₀)
    let α := correspondenceRightRemainingImageMiddleStalkMap f g h i z w v x
    let κ := correspondenceTripleIncidenceRightFirstStageStalkMap f g h i z w v y
    let ρ := correspondenceRightRemainingFiniteModelProjection f g h i z w v x
    let T := correspondenceRightRemainingFiniteTorSheaf f g h i z w v x
    let sP := fun j => κ ((correspondenceSixfoldFirstMiddlePair f g h i).stalkMap
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j))
    let eY := (pullback g g).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRightRemainingTriple_middle_point_eq f g h i z w v x y hy))
    letI := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
    letI := stalkModule (T n) q
    letI := correspondenceIncidenceTorModule g h i w v (π a₀) n
    letI : Algebra P₀ P := (π.stalkMap a₀).hom.toAlgebra
    Koszul.seqEuler (fun j => E.presheaf.germ ⊤ q trivial
      (algebraMap R B (α (eY.inv (s j))))) ((T n).presheaf.stalk q) =
      Koszul.seqEuler sP (P ⊗[P₀] correspondenceIncidenceAmbientTor g h i w v (π a₀) n) := by
  exact seqEuler_correspondenceRightRemainingFiniteTorStalk_eq_originalPair
    f g h i z w v x q hq y hy hρ n s

end Stacks.Chow
