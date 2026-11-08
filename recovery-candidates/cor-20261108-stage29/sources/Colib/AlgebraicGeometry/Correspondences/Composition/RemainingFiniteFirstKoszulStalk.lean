/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFinitePullbackStalk
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFirstTorSheaf
public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteOriginalList

/-!
# The actual finite-model Tor stalk is original first Koszul homology

The stalk of the actual degree-`n` Tor sheaf on the whole finite model is identified with
original first Koszul homology at its original triple-incidence point. Its action by the
original first-stage stalk is restriction along the actual point transport followed by the
localization-projection stalk map. The comparison composes the native pullback-stalk formula
with the already constructed, quotient-linear original first-stage Tor comparison.

Only the equality of the actual original exterior points is needed for this coefficient
comparison. In the closed fibre, `RemainingFiniteOriginalList` additionally identifies the
actual finite-algebra scalar germ of each original remaining Z equation. The coefficient
comparison therefore respects those original equations entry by entry, not just their ideal.
The final complex isomorphism uses the same ordered P-valued list on both coefficient modules.
It does not claim that a change of the base ring of a Koszul complex is definitional.

## References and scope

* Stacks Project, Tag 0098: the native module pullback-stalk formula, specialized in
  `RemainingFinitePullbackStalk` to the actual stalk-isomorphic localization projection.
* Stacks Project, Tag 0AZT: the native Tor-sheaf stalk comparison underlying `PairTorSheaf`
  and `RemainingFirstTorSheaf`.
* The original first-stage Koszul comparison and its quotient-induced scalar action are
  those of `FirstStageOriginalPairTor`, inherited through `RemainingFirstTorSheaf`.
* Mathlib's `TopCat.Presheaf.stalkCongr` transports the actual equal exterior points;
  `RemainingFiniteOriginalList` proves compatibility with the actual finite-algebra action.

No coefficient comparison, alternative scalar action, finite-map flatness, reduction,
field restriction, or connectedness hypothesis is supplied by the caller. The degree is
unchanged. The original Y list is assumed regular and to generate its original diagonal
stalk ideal, exactly as in the existing original first-stage comparison.
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

/-- The actual first-stage action on the actual finite Tor-sheaf stalk, with point transport. -/
@[instance_reducible]
def correspondenceRemainingFiniteTorStalkFirstStageModule
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) (n : ℕ) :
    Module ((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
      (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y))
        ((correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) := by
  let := stalkModule (correspondenceRemainingFiniteTorSheaf f g h i z w v x n) q
  exact Module.compHom _
    ((((correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalkCongr
      (Inseparable.of_eq hρ)).hom ≫
        (correspondenceRemainingFiniteModelProjection f g h i z w v x).stalkMap q).hom)

/-- The actual finite Tor-sheaf stalk is the original first Koszul homology in the same degree,
linearly over the original full first-stage stalk with its canonical quotient action. -/
def correspondenceRemainingFiniteFirstKoszulStalkLinearEquiv
    [Flat f] [Flat h] [Flat i] [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) {r : ℕ}
    (t : Fin r → (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
      (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))))
    (ht : IsRegular _ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))) =
        Ideal.span (Set.range t)) (n : ℕ) :
    let a := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
    let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk a
    let p₀ := correspondenceIncidenceAmbientInclusion f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v a)
    let l := List.ofFn (fun j => correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v y
      ((correspondenceMiddlePair f g h).stalkMap p₀ (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v y t ht hkt
    let := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v y l hreg.1 hreg.2 n
    let := correspondenceRemainingFiniteTorStalkFirstStageModule f g h i z w v x q y hρ n
    ((correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) ≃ₗ[P]
      (Koszul.seqComplexTensor l.get
        (correspondenceTripleIncidenceSupportStalkModule f g h i z w v y)).homology n := by
  let F := correspondenceLeftIntermediateSupportProduct f g h i z w v
  let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
  let M := correspondenceLeftExteriorTorSheaf f g h i z w v n
  let ePBAt (a : F) (ha : a = ρ q) :
      let P := F.presheaf.stalk a
      let M' := (Scheme.Modules.pullback ρ).obj M
      let := stalkModule M' q
      let := stalkModule M a
      let : Module P (M'.presheaf.stalk q) := Module.compHom _
        (((F.presheaf.stalkCongr (Inseparable.of_eq ha)).hom ≫ ρ.stalkMap q).hom)
      (M'.presheaf.stalk q) ≃ₗ[P] (M.presheaf.stalk a) := by
    subst a
    simpa only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Category.id_comp] using
        correspondenceRemainingFinitePullbackStalkLinearEquiv f g h i z w v x q M
  exact (ePBAt
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y) hρ).trans
    (correspondenceTripleIncidenceFirstKoszulIsoTorSheaf f g h i z w v y t ht hkt n).symm

/-- The same linear comparison respects every scalar from the original sixfold Z-list.
The scalar on its source is the actual finite-algebra germ, not an assumed P-action. -/
theorem correspondenceRemainingFiniteFirstKoszulStalkLinearEquiv_originalList_smul
    [Flat f] [Flat h] [Flat i] [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (hq : correspondenceRemainingFiniteModelStructure f g h i z w v x q =
      IsLocalRing.closedPoint (correspondenceRemainingImageStalk f g h i z w v x))
    (y : correspondenceTripleIncidence f g h i z w v)
    (hy : correspondenceTripleToLeftImageIncidence f g h i z w v y = x)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) {r : ℕ}
    (t : Fin r → (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
      (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))))
    (ht : IsRegular _ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))) =
        Ideal.span (Set.range t)) (n : ℕ) {sLen : ℕ}
    (s : Fin sLen → (pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y)))
    (j : Fin sLen)
    (u : (correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let := stalkModule (correspondenceRemainingFiniteTorSheaf f g h i z w v x n) q
    let a := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
    let p₀ := correspondenceIncidenceAmbientInclusion f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v a)
    let l := List.ofFn (fun j => correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v y
      ((correspondenceMiddlePair f g h).stalkMap p₀ (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v y t ht hkt
    let := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v y l hreg.1 hreg.2 n
    let eZ := (pullback h h).presheaf.stalkCongr (Inseparable.of_eq
      (correspondenceRemainingTriple_middle_point_eq f g h i z w v x y hy))
    let e := correspondenceRemainingFiniteFirstKoszulStalkLinearEquiv
      f g h i z w v x q y hρ t ht hkt n
    e ((correspondenceRemainingFiniteModel f g h i z w v x).presheaf.germ ⊤ q trivial
      (algebraMap (correspondenceRemainingImageStalk f g h i z w v x)
        (correspondenceRemainingFiniteRing f g h i z w v x)
        (correspondenceRemainingImageMiddleStalkMap f g h i z w v x (eZ.inv (s j)))) • u) =
      correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y
        ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
          (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j)) • e u := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let := stalkModule (correspondenceRemainingFiniteTorSheaf f g h i z w v x n) q
  let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk
    (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)
  let ρ := correspondenceRemainingFiniteModelProjection f g h i z w v x
  let c : P := correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y
    ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
      (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j))
  have := isIso_correspondenceRemainingFiniteModelProjection_stalkMap f g h i z w v x q
  have hs := congrArg (fun bs => ρ.stalkMap q (bs j))
    (correspondenceRemainingFiniteOriginalStalkMap_originalList
      f g h i z w v x q hq y hy hρ s)
  simp only [correspondenceRemainingFiniteOriginalStalkMap, CommRingCat.hom_comp,
    RingHom.comp_apply, IsIso.inv_hom_id_apply] at hs
  dsimp only
  rw [hs]
  exact (correspondenceRemainingFiniteFirstKoszulStalkLinearEquiv
    f g h i z w v x q y hρ t ht hkt n).map_smul c u

/-- The unchanged ordered original P-list gives isomorphic coefficient Koszul complexes.
Together with the preceding scalar theorem, this is the actual remaining-list coefficient join. -/
def correspondenceRemainingFiniteFirstKoszulStalkComplexIso
    [Flat f] [Flat h] [Flat i] [IsSeparated g]
    [Flat (((integralComponentAt v).subschemeι ≫ pullback.fst h i) ≫ h)]
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x)
    (y : correspondenceTripleIncidence f g h i z w v)
    (hρ : correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y =
      correspondenceRemainingFiniteModelProjection f g h i z w v x q) {r : ℕ}
    (t : Fin r → (pullback g g).presheaf.stalk (correspondenceMiddlePair f g h
      (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))))
    (ht : IsRegular _ (List.ofFn t))
    (hkt : IdealSheafData.stalk (pullback.diagonal g).ker
      (correspondenceMiddlePair f g h (correspondenceIncidenceAmbientInclusion f g h z w
        (correspondenceLeftExteriorProjection f g h i z w v
          (correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y)))) =
        Ideal.span (Set.range t)) (n : ℕ) {sLen : ℕ}
    (s : Fin sLen → (pullback h h).presheaf.stalk
      (correspondenceSixfoldSecondMiddlePair f g h i
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y))) :
    let a := correspondenceTripleIncidenceToLeftSupportProduct f g h i z w v y
    let P := (correspondenceLeftIntermediateSupportProduct f g h i z w v).presheaf.stalk a
    let p₀ := correspondenceIncidenceAmbientInclusion f g h z w
      (correspondenceLeftExteriorProjection f g h i z w v a)
    let l := List.ofFn (fun j => correspondenceTripleIncidencePairAmbientStalkMap f g h i z w v y
      ((correspondenceMiddlePair f g h).stalkMap p₀ (t j)))
    let hreg := correspondenceOriginalPairList_first_regular f g h i z w v y t ht hkt
    let := correspondenceTripleIncidenceFirstKoszulModule
      f g h i z w v y l hreg.1 hreg.2 n
    let := correspondenceRemainingFiniteTorStalkFirstStageModule f g h i z w v x q y hρ n
    let sP := fun j => correspondenceTripleIncidenceFirstStageStalkMap f g h i z w v y
      ((correspondenceSixfoldSecondMiddlePair f g h i).stalkMap
        (correspondenceTripleIncidenceSixfoldInclusion f g h i z w v y) (s j))
    Koszul.seqComplexTensor sP (ModuleCat.of P
      ((correspondenceRemainingFiniteTorSheaf f g h i z w v x n).presheaf.stalk q)) ≅
        Koszul.seqComplexTensor sP (ModuleCat.of P ((Koszul.seqComplexTensor l.get
          (correspondenceTripleIncidenceSupportStalkModule f g h i z w v y)).homology n)) :=
  (Koszul.seqComplexTensorFunctor _).mapIso
    (correspondenceRemainingFiniteFirstKoszulStalkLinearEquiv
      f g h i z w v x q y hρ t ht hkt n).toModuleIso

end Stacks.Chow
