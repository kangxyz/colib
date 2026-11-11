/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionBaseChange
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.PolynomialBranchCycle

import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionTower
import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.TupleFieldChange

/-!
# Scalar base change of an actual transferred polynomial point

The scalar extension of the entire transferred graph is a sum of actual
transferred graphs, one for every irreducible factor of the coefficient image.
Each factor carries the full tuple through its native polynomial quotient map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open scoped BigOperators

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionBaseChange

open _root_.AlgebraicGeometry.Scheme AlgebraicGeometry.AlgebraicCycle
open DiagonalCorestriction DiagonalFieldChange DiagonalPolynomialBranchCycle
open DiagonalCycleSymbols (rationalTuple)
open DiagonalFiniteCyclePushforward (scalarMap torusMap)
open Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

local instance pointRootIrreducible {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance pointRootFinite {F : Type u} [Field F] {d : ℕ}
    (p : MonicIrreducibleOfDegree F d) : Module.Finite F (AdjoinRoot (poly p)) :=
  (monic p).finite_adjoinRoot

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

private theorem rationalTuple_scalarSquare {E F : Type u} [Field E] [Field F]
    [Algebra k E] [Algebra L F] (ψ : E →+* F)
    (hψ : ψ.comp (algebraMap k E) = (algebraMap L F).comp (algebraMap k L))
    (n : ℕ) (a : Fin n → Eˣ) :
    Spec.map (CommRingCat.ofHom ψ) ≫
      (rationalTuple E n a).left ≫ torusMap (k := k) (E := E) n =
      (rationalTuple F n (fun i => Units.map ψ.toMonoidHom (a i))).left ≫
        torusMap (k := L) (E := F) n ≫ torusMap (k := k) (E := L) n := by
  let : Algebra E F := ψ.toAlgebra
  let : Algebra k F := ((algebraMap L F).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k E F := IsScalarTower.of_algebraMap_eq' hψ.symm
  let : IsScalarTower k L F := IsScalarTower.of_algebraMap_eq' rfl
  have hψmap : algebraMap E F = ψ := RingHom.algebraMap_toAlgebra ψ
  rw [torusMap_comp (k := k) (L := L) (E := F) n,
    ← torusMap_comp (k := k) (L := E) (E := F) n]
  simpa only [Category.assoc, scalarMap, hψmap] using
    (congrArg (fun f => f ≫ torusMap (k := k) (E := E) n)
      (rationalTuple_scalar (k := E) (E := F) n a)).symm

variable {d n : ℕ} (p : MonicIrreducibleOfDegree k d) (a : Fin n → (AdjoinRoot (poly p))ˣ)

private def polynomialPointSupportIso :
    Spec (.of (AdjoinRoot ((poly p).map (algebraMap k L)))) ≅
      changedPointSupport (k := k) (L := L) (E := AdjoinRoot (poly p)) :=
  scalarSchemeIso (algebraMap k L) (poly p) ≪≫ pullbackSymmetry _ _

private def polynomialChangedPoint :
    Spec (.of (AdjoinRoot ((poly p).map (algebraMap k L)))) ⟶ pointAmbient L n :=
  (polynomialPointSupportIso (L := L) p).hom ≫
    changedPointMap (k := k) (L := L) n (rationalTuple _ n a)

private instance : IsFinite (polynomialChangedPoint (L := L) p a) := by
  unfold polynomialChangedPoint
  infer_instance

private theorem polynomialChangedPoint_original :
    polynomialChangedPoint (L := L) p a ≫ pointAmbientMap (k := k) n =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.map (algebraMap k L) (poly p)
        ((poly p).map (algebraMap k L)) dvd_rfl)) ≫
        finitePointMap (k := k) n (rationalTuple _ n a) := by
  simp only [polynomialChangedPoint, Category.assoc, changedPointMap_original,
    polynomialPointSupportIso, Iso.trans_hom, scalarMap, AdjoinRoot.algebraMap_eq,
    pullbackSymmetry_hom_comp_fst_assoc,
    scalarSchemeIso_hom_snd_assoc]

private theorem polynomialChangedPoint_base :
    polynomialChangedPoint (L := L) p a ≫ pointAmbientStructure L n =
      NativeTorusPolynomial.projection ((poly p).map (algebraMap k L)) := by
  simp only [polynomialChangedPoint, Category.assoc, changedPointMap_base,
    polynomialPointSupportIso, Iso.trans_hom, scalarMap, AdjoinRoot.algebraMap_eq,
    pullbackSymmetry_hom_comp_snd,
    scalarSchemeIso_hom_fst]

private theorem polynomialChangedPoint_branch
    (r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap k L)}) :
    branchMap ((poly p).map (algebraMap k L)) r ≫ polynomialChangedPoint (L := L) p a =
      finitePointMap (k := L) n (rationalTuple (AdjoinRoot (poly r.1.2)) n
        (fun i => Units.map (AdjoinRoot.map (algebraMap k L) (poly p)
          (poly r.1.2) r.2).toMonoidHom (a i))) := by
  let ψ := AdjoinRoot.map (algebraMap k L) (poly p) (poly r.1.2) r.2
  have hψ : ψ.comp (algebraMap k (AdjoinRoot (poly p))) =
      (algebraMap L (AdjoinRoot (poly r.1.2))).comp (algebraMap k L) := by
    apply RingHom.ext
    exact AdjoinRoot.map_of (algebraMap k L) (poly p) (poly r.1.2) r.2
  apply (pointAmbientMap_isPullback (k := k) (L := L) n).hom_ext
  · rw [Category.assoc, polynomialChangedPoint_original, ← Category.assoc, branchMap_scalarMap]
    apply pullback.hom_ext
    · simp only [Category.assoc, finitePointMap_fst, finitePointMap_fst_assoc, pointAmbientMap_fst]
      rw [← Spec.map_comp, ← Spec.map_comp]
      exact congrArg Spec.map (congrArg CommRingCat.ofHom hψ)
    · simp only [Category.assoc, finitePointMap_snd, finitePointMap_snd_assoc, pointAmbientMap_snd]
      exact rationalTuple_scalarSquare ψ hψ n a
  · rw [Category.assoc, polynomialChangedPoint_base, branchMap_projection, finitePointMap_fst]
    simp only [NativeTorusPolynomial.projection, scalarMap, AdjoinRoot.algebraMap_eq]

/-- The native signed cycle of a transferred polynomial graph after scalar extension. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/PolynomialPointBaseChange.lean:126-174"
  "adaptation" "Full scalar branch formula for the actual transferred ordered graph"]
theorem pointPushforward_graph_fieldChange_polynomial
    [Fintype {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
      poly r.2 ∣ (poly p).map (algebraMap k L)}]
    (hsep : (poly p).Separable) :
    pointCycleFieldChange (k := k) (L := L) n
      (pointPushforward (k := k) n ((Cor.graphFunctor (AdjoinRoot (poly p))).map
        (rationalTuple _ n a))) =
      ∑ r : {r : Σ e : ℕ, MonicIrreducibleOfDegree L e //
          poly r.2 ∣ (poly p).map (algebraMap k L)},
        pointPushforward (k := L) n ((Cor.graphFunctor (AdjoinRoot (poly r.1.2))).map
          (rationalTuple (AdjoinRoot (poly r.1.2)) n
            (fun i => Units.map (AdjoinRoot.map (algebraMap k L) (poly p)
              (poly r.1.2) r.2).toMonoidHom (a i)))) := by
  classical
  let e := polynomialPointSupportIso (L := L) p
  apply Subtype.ext
  rw [pointPushforward_graph_fieldChange_val, ← finiteCyclePushforward_fundamentalCycle_iso e,
    finiteCyclePushforward_comp_apply]
  change finiteCyclePushforward (polynomialChangedPoint (L := L) p a) _ = _
  rw [fundamentalCycle_eq_sum_branches _ ((monic p).map _) hsep.map.squarefree]
  change _ = (finiteCorrespondences (SmoothSite.base (Spec (.of L))).hom
    (DiagonalCycleSymbols.target L n).toSmoothSite.hom).subtype _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [AddSubgroup.subtype_apply, finiteCyclePushforward_comp_apply]
  have hpush {P : Scheme.{u}} (f g : P ⟶ pointAmbient L n)
      [IsFinite f] [IsFinite g] (h : f = g) (c : AlgebraicCycle P ℤ) :
      finiteCyclePushforward f c = finiteCyclePushforward g c := by
    cases h
    rfl
  exact (hpush _ _ (polynomialChangedPoint_branch (L := L) p a r) _).trans
    (pointPushforward_graph_fundamental (k := L) n _).symm

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionBaseChange
