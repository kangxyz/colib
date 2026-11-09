/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteFirstKoszulStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstHomologyEuler
public import Colib.RingTheory.Koszul.RestrictionComparison

/-!
# Actual finite Tor-stalk Euler equals original first-Koszul remaining Euler

The actual model stalk and original first-stage stalk are isomorphic by the localization
projection and the proved equality of original exterior points. The native Koszul projection
formula therefore transports raw homology lengths between those two rings. The actual
original-list theorem identifies the finite section-germ list with the original ordered
Z-list, not merely with another generating set of the same ideal. The already constructed
P-linear coefficient comparison then identifies the Tor stalk with original Y-Koszul
homology in precisely the same degree.

This supplies an actual raw-length and Euler join. Only actual fibre and exterior point
equalities and the original regular Y-diagonal presentation are parameters. No module
comparison, alternative scalar action, remaining-Euler equality, finite length or cutoff is
assumed. The full nonreduced first-stage local ring and both ordered lists are retained.

References: the native module pullback-stalk formula (Stacks 0098), the native Tor-sheaf
stalk comparison (Stacks 0AZT), and Mathlib's surjective scalar restriction length theorem.
The implementation consumes `RemainingFiniteFirstKoszulStalk`, `RemainingFiniteOriginalList`
and the actual exterior-power Koszul projection formula; it does not rebuild those providers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits RingTheory.Sequence
open Stacks.ModuleStalkSpecialization

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)
  [Flat f] [Flat h] [Flat i] [IsSeparated g]
  [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]

/-- Raw lengths agree after the actual scalar-ring transport and original first-homology
coefficient comparison. Both list orders and the first Tor degree are unchanged. -/
theorem length_correspondenceRemainingFiniteTorStalkKoszul_eq_firstKoszul
  (x : correspondenceLeftImageIncidence f g h i z w v)
  (q : correspondenceRemainingFiniteModel f g h i z w v x)
  (hq : correspondenceRemainingFiniteModelStructure f g h i z w v x q =
    IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x))
  (y : correspondenceTripleIncidence f g h i z w v)
  (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x)
  (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
    correspondenceRemainingFiniteModelProjection f g h i z w v x q)
  {r : ℕ}
  (t : Fin r → (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
      (correspondenceIncidenceAmbientInclusion f g h z w
  (correspondenceLeftExteriorProjection f g h i z w v
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))))
  (ht : IsRegular ((pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
    (correspondenceIncidenceAmbientInclusion f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))))
    (List.ofFn t))
  (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
    (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w
  (correspondenceLeftExteriorProjection f g h i z w v
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))) = Ideal.span (Set.range
      t))
  (n : ℕ) {sLen : ℕ}
  (s : Fin sLen → (pullback h h).presheaf.stalk
    (correspondenceSixfoldSecondMiddlePair f g h i
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y)))
    (a : ℕ) :
    let E := correspondenceRemainingFiniteModel f g h i z w v x
    let F := correspondenceLeftIntermediateSupportProduct f g h i z w v
    let R := correspondenceRemainingImageStalk f g h i z w v x
    let B := correspondenceRemainingFiniteRing f g h i z w v x
    let Q := (E).presheaf.stalk q
    let a₀ := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
    let P := (F).presheaf.stalk a₀
    let p₀ := correspondenceIncidenceAmbientInclusion f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v a₀)
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
    let φ := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y
    let _ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
    let T := correspondenceRemainingFiniteTorSheaf f g h i z w v x
    let l := List.ofFn (fun j =>
      correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v y
      ((correspondenceMiddlePair f g h).stalkMap p₀ (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v y t ht hkt
    let H := correspondenceRemainingFirstKoszulModule f g h i z w v y l hreg.1 hreg.2 n
    let sP := fun j => φ
      ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j))
    let eZ := (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy))
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let := stalkModule (T n) q
    Module.length Q
      ((Koszul.seqComplexTensor (fun j => (E).presheaf.germ ⊤ q trivial
        (algebraMap R B (α (eZ.inv (s j))))) ((T n).presheaf.stalk q)).homology a) =
      Module.length P ((Koszul.seqComplexTensor sP H).homology a) := by
  dsimp only
  let E := correspondenceRemainingFiniteModel f g h i z w v x
  let F := correspondenceLeftIntermediateSupportProduct f g h i z w v
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let B := correspondenceRemainingFiniteRing f g h i z w v x
  let Q := (E).presheaf.stalk q
  let a₀ := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
  let P := (F).presheaf.stalk a₀
  let p₀ := correspondenceIncidenceAmbientInclusion f g h z w
    (correspondenceLeftExteriorProjection f g h i z w v a₀)
  let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
  let φ := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y
  let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
  let T := correspondenceRemainingFiniteTorSheaf f g h i z w v x
  let l := List.ofFn (fun j =>
    correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v y
    ((correspondenceMiddlePair f g h).stalkMap p₀ (t j)))
  let hreg := correspondenceOriginalPairList_first_regular f g h i z w v y t ht hkt
  let H := correspondenceRemainingFirstKoszulModule f g h i z w v y l hreg.1 hreg.2 n
  let sP := fun j => φ
    ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
    (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j))
  let eZ := (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
    (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy))
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let := stalkModule (T n) q
  have := isIso_correspondenceRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  let ePQ : CommRingCat.of P ≅ CommRingCat.of Q :=
    (F).presheaf.stalkCongr (Inseparable.of_eq hρ) ≪≫ asIso (ρ.stalkMap q)
  let : Algebra P Q := ePQ.hom.hom.toAlgebra
  let N : ModuleCat Q := ModuleCat.of Q ((T n).presheaf.stalk q)
  let N₀ := (ModuleCat.restrictScalars (algebraMap P Q)).obj N
  have hl : (fun j => algebraMap P Q (sP j)) =
      (fun j => (E).presheaf.germ ⊤ q trivial (algebraMap R B (α (eZ.inv (s j))))) := by
    funext j
    exact (correspondenceRemainingFiniteOriginalList_germ_eq
      f g h i z w v x q hq y hy hρ s j).symm
  have hp := (Koszul.homologySeqComplexTensorRestrictScalarsIso sP N a).toLinearEquiv.length_eq
  let H₀ := (Koszul.seqComplexTensor (fun j => algebraMap P Q (sP j)) N).homology a
  let : Module P H₀ := Module.compHom H₀ (algebraMap P Q)
  let : IsScalarTower P Q H₀ := .of_algebraMap_smul fun _ _ => rfl
  have hlen : Module.length P H₀ = Module.length Q H₀ :=
    Module.length_eq_of_surjective (ConcreteCategory.bijective_of_isIso ePQ.hom).2
  have he := ((HomologicalComplex.homologyFunctor (ModuleCat P) (.down ℕ) a).mapIso
    (correspondenceRemainingFiniteFirstKoszulStalkComplexIso
      f g h i z w v x q y hρ t ht hkt n s)).toLinearEquiv.length_eq
  calc
    _ = Module.length Q H₀ := (congrArg
      (fun l : Fin sLen → Q => Module.length Q ((Koszul.seqComplexTensor l N).homology a))
        hl).symm
    _ = Module.length P H₀ := hlen.symm
    _ = Module.length P ((Koszul.seqComplexTensor sP N₀).homology a) := hp.symm
    _ = _ := he

/-- The actual finite Tor-sheaf stalk Euler is the remaining Euler of original first
Koszul homology over the full original first-stage stalk. -/
theorem seqEuler_correspondenceRemainingFiniteTorStalk_eq_firstKoszul
  (x : correspondenceLeftImageIncidence f g h i z w v)
  (q : correspondenceRemainingFiniteModel f g h i z w v x)
  (hq : correspondenceRemainingFiniteModelStructure f g h i z w v x q =
    IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x))
  (y : correspondenceTripleIncidence f g h i z w v)
  (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x)
  (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
    correspondenceRemainingFiniteModelProjection f g h i z w v x q)
  {r : ℕ}
  (t : Fin r → (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
      (correspondenceIncidenceAmbientInclusion f g h z w
  (correspondenceLeftExteriorProjection f g h i z w v
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))))
  (ht : IsRegular ((pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
    (correspondenceIncidenceAmbientInclusion f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v
        (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))))
    (List.ofFn t))
  (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
    (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w
  (correspondenceLeftExteriorProjection f g h i z w v
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))) = Ideal.span (Set.range
      t))
  (n : ℕ) {sLen : ℕ}
  (s : Fin sLen → (pullback h h).presheaf.stalk
    (correspondenceSixfoldSecondMiddlePair f g h i
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y)))
    :
    let E := correspondenceRemainingFiniteModel f g h i z w v x
    let R := correspondenceRemainingImageStalk f g h i z w v x
    let B := correspondenceRemainingFiniteRing f g h i z w v x
    let a₀ := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
    let p₀ := correspondenceIncidenceAmbientInclusion f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v a₀)
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
    let φ := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y
    let T := correspondenceRemainingFiniteTorSheaf f g h i z w v x
    let l := List.ofFn (fun j =>
      correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v y
      ((correspondenceMiddlePair f g h).stalkMap p₀ (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v y t ht hkt
    let H := correspondenceRemainingFirstKoszulModule f g h i z w v y l hreg.1 hreg.2 n
    let sP := fun j => φ
      ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j))
    let eZ := (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy))
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let := stalkModule (T n) q
    Koszul.seqEuler (fun j => (E).presheaf.germ ⊤ q trivial
      (algebraMap R B (α (eZ.inv (s j))))) ((T n).presheaf.stalk q) =
      Koszul.seqEuler sP H := by
  dsimp only
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let := stalkModule (correspondenceRemainingFiniteTorSheaf f g h i z w v x n) q
  unfold Koszul.seqEuler
  apply Finset.sum_congr rfl
  intro a _
  rw [length_correspondenceRemainingFiniteTorStalkKoszul_eq_firstKoszul
    f g h i z w v x q hq y hy hρ t ht hkt n s a]

end Stacks.Chow
