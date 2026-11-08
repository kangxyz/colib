/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import
  Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingFiniteOriginalPairStalk
public import Colib.RingTheory.Koszul.RestrictionComparison

/-!
# Actual right finite-stalk Euler in the unchanged original remaining Y list

The localization projection and actual point equality identify its stalk ring with the
original right-stage stalk. Native scalar restriction preserves the raw homology length
along this actual ring isomorphism. The proved scalar triangle identifies each original
Y equation, in order, with its finite-algebra section germ. The actual G,H coefficient
comparison then computes the same remaining Euler over the original full support ring.
No finite-length or Euler comparison is assumed.
References: Stacks 0098, 0AZT and native surjective scalar-restriction length.
-/

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

/-- Raw remaining homology lengths agree for the literal original Y equations. -/
theorem length_correspondenceRightRemainingFiniteTorStalkKoszul_eq_originalPair [IsSeparated h]
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
  dsimp only
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
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let := stalkModule (T n) q
  let := correspondenceIncidenceTorModule g h i w v (π a₀) n
  let : Algebra P₀ P := (π.stalkMap a₀).hom.toAlgebra
  let := isIso_correspondenceRightRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  let ePQ : CommRingCat.of P ≅ CommRingCat.of Q :=
    F.presheaf.stalkCongr (Inseparable.of_eq hρ) ≪≫ asIso (ρ.stalkMap q)
  let : Algebra P Q := ePQ.hom.hom.toAlgebra
  let N : ModuleCat Q := ModuleCat.of Q ((T n).presheaf.stalk q)
  let N₀ := (ModuleCat.restrictScalars (algebraMap P Q)).obj N
  have hl : (fun j => algebraMap P Q (sP j)) =
      (fun j => E.presheaf.germ ⊤ q trivial (algebraMap R B (α (eY.inv (s j))))) := by
    funext j
    have hj := congrArg (fun bs => ρ.stalkMap q (bs j))
      (correspondenceRightRemainingFiniteOriginalStalkMap_originalList
        f g h i z w v x q hq y hy hρ s)
    simp only [correspondenceRightRemainingFiniteOriginalStalkMap, CommRingCat.hom_comp,
      RingHom.comp_apply, IsIso.inv_hom_id_apply] at hj
    exact hj.symm
  have hp := (Koszul.homologySeqComplexTensorRestrictScalarsIso sP N a).toLinearEquiv.length_eq
  let H := (Koszul.seqComplexTensor (fun j => algebraMap P Q (sP j)) N).homology a
  let : Module P H := Module.compHom H (algebraMap P Q)
  let : IsScalarTower P Q H := .of_algebraMap_smul fun _ _ => rfl
  have hlen : Module.length P H = Module.length Q H :=
    Module.length_eq_of_surjective (ConcreteCategory.bijective_of_isIso ePQ.hom).2
  have he := (Koszul.homologyTensorCongr sP
    (correspondenceRightRemainingFiniteOriginalPairStalkLinearEquiv
      f g h i z w v x q y hρ n) a).toLinearEquiv.length_eq
  calc
    _ = Module.length Q H := by dsimp only [H]; rw [hl]
    _ = Module.length P H := hlen.symm
    _ = Module.length P ((Koszul.seqComplexTensor sP N₀).homology a) := hp.symm
    _ = _ := he

/-- The original Y-list finite-model stalk Euler equals the actual original G,H pair Euler. -/
theorem seqEuler_correspondenceRightRemainingFiniteTorStalk_eq_originalPair [IsSeparated h]
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
  dsimp only
  let := correspondenceRightRemainingFiniteAlgebra f g h i z w v x
  let := stalkModule (correspondenceRightRemainingFiniteTorSheaf f g h i z w v x n) q
  unfold Koszul.seqEuler
  apply Finset.sum_congr rfl
  intro a _
  rw [length_correspondenceRightRemainingFiniteTorStalkKoszul_eq_originalPair
    f g h i z w v x q hq y hy hρ n s a]

end Stacks.Chow
