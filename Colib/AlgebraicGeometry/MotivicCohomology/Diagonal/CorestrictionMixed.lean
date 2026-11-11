/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CorestrictionPoints
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.MixedPointNorm
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.TupleFieldChange

/-!
# Corestriction of mixed diagonal graph symbols

The original finite point with one varying coordinate factors through the
unit point and the fixed-coordinate insertion. The corresponding signed
cycle retains its full residue degree. Its raw class is the symbol with the
varying coordinate replaced by the determinant norm.

Adapted from `Motivic/Cohomology/Diagonal/CorestrictionMixed.lean` at
`motivic_source_a6805c4`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionMixed

open _root_.AlgebraicGeometry.Scheme SmoothSite
open DiagonalCycleSymbols DiagonalCorestriction DiagonalFieldChange
open DiagonalFiniteCyclePushforward (scalarMap torusMap)
open DiagonalReducedPushforward (torusMap_coordinate torusPower_left_hom_ext)
open DiagonalFinitePointEvaluation (affineCoordinateUnit)
open NativeTorusPolynomial (smoothUnitPoint)

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

private theorem varyingCoordinate_coordinate (q : ℕ) (a : Fin q → kˣ) (i j : Fin q) :
    (varyingCoordinate k q a i).left ≫ (torusCoordinate (Spec (.of k)) q j).left =
      (if j = i then torusCoordinate (Spec (.of k)) 1 0 else
        torusPowerToBase (Spec (.of k)) 1 ≫ smoothUnitPoint (𝟙 (Spec (.of k))) (a j)).left := by
  let S := Spec (.of k)
  let coords (t : Fin q) : torusPower S 1 ⟶ multiplicativeGroupObject S :=
    if t = i then torusCoordinate S 1 0 else torusPowerToBase S 1 ≫ smoothUnitPoint (𝟙 S) (a t)
  exact congrArg (fun f : torusPower S 1 ⟶ multiplicativeGroupObject S => f.left)
    (torusPowerLift_coordinate S q coords j)

/-- The chosen coordinate retracts the fixed-coordinate insertion. -/
instance varyingCoordinate_closed (q : ℕ) (a : Fin q → kˣ) (i : Fin q) :
    IsClosedImmersion (varyingCoordinate k q a i).left := by
  let S := Spec (.of k)
  let d := (torusCoordinate S q i).left
  have : IsSeparated (d ≫ (multiplicativeGroupObject S).hom) := by
    rw [show d ≫ (multiplicativeGroupObject S).hom = (torusPower S q).hom from
      MorphismProperty.Over.w (torusCoordinate S q i)]
    infer_instance
  let : IsSeparated d := IsSeparated.of_comp _ (multiplicativeGroupObject S).hom
  have h : (varyingCoordinate k q a i).left ≫ d = (torusPowerOneIso S).hom.left := by
    change (varyingCoordinate k q a i).left ≫ (torusCoordinate (Spec (.of k)) q i).left =
      (torusCoordinate (Spec (.of k)) 1 0).left
    simpa only [ite_true] using varyingCoordinate_coordinate q a i i
  have : IsClosedImmersion ((varyingCoordinate k q a i).left ≫ d) := by
    rw [h]
    exact inferInstanceAs (IsClosedImmersion
      ((SmoothSite.forgetScheme S).map (torusPowerOneIso S).hom))
  exact IsClosedImmersion.of_comp _ d

/-- The tuple with one extension-field entry and all other entries from the base. -/
def mixedTuple (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : Eˣ) : Fin q → Eˣ :=
  Function.update (fun j => Units.map (algebraMap k E).toMonoidHom (a j)) i b

@[reassoc]
private theorem finitePointMap_target_structure (q : ℕ)
    (f : base (Spec (.of E)) ⟶ torusPower (Spec (.of E)) q) :
    finitePointMap (k := k) q f ≫ pullback.snd (base (Spec (.of k))).hom
        (torusPower (Spec (.of k)) q).hom ≫ (torusPower (Spec (.of k)) q).hom =
      scalarMap (k := k) (E := E) := by
  rw [← pullback.condition, finitePointMap_fst_assoc]
  exact Category.comp_id _

/-- Each coordinate of the pushed tuple is the corresponding affine unit over the base field. -/
theorem finitePointMap_rationalTuple_coordinate (q : ℕ) (a : Fin q → Eˣ) (i : Fin q) :
    finitePointMap (k := k) q (rationalTuple E q a) ≫
      pullback.snd (base (Spec (.of k))).hom (torusPower (Spec (.of k)) q).hom ≫
        (torusCoordinate (Spec (.of k)) q i).left =
      (nativeAffineTorusPoint (scalarMap (k := k) (E := E)) (a i)).left := by
  rw [finitePointMap_snd_assoc]
  refine (congrArg (fun m => (rationalTuple E q a).left ≫ m)
    (torusMap_coordinate (k := k) (E := E) q i)).trans ?_
  exact (rationalTuple_left_coordinate_assoc E q a i _).trans
    (affineUnitPoint_scalar (k := k) (E := E) (a i))

/-- The finite graph point reads its actual original units in the source field. -/
theorem affineCoordinateUnit_finitePointMap_rationalTuple
    (q : ℕ) (a : Fin q → Eˣ) (i : Fin q) :
    affineCoordinateUnit (finitePointMap (k := k) q (rationalTuple E q a)) i = a i := by
  let S := Spec (.of k)
  let readUnit (m : Spec (.of E) ⟶ (multiplicativeGroupObject S).left) : Eˣ :=
    Units.map (Scheme.ΓSpecIso (.of E)).hom.hom.toMonoidHom
      (Units.map m.appTop.hom.toMonoidHom (multiplicativeGroupBaseChangeCoordinate S))
  change readUnit (finitePointMap (k := k) q (rationalTuple E q a) ≫
    pullback.snd (base S).hom (torusPower S q).hom ≫ (torusCoordinate S q i).left) = a i
  exact (congrArg readUnit (finitePointMap_rationalTuple_coordinate q a i)).trans
    (nativeAffineTorusPoint_coordinate _ _)

private theorem rationalPoint_rationalTuple (b : Eˣ) :
    WeightOne.rationalPoint E b = rationalTuple E 1 (fun _ => b) := by
  apply torusPower_hom_ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [rationalTuple_coordinate]
  change (smoothUnitPoint (𝟙 (Spec (.of E))) b ≫ (torusPowerOneIso (Spec (.of E))).inv) ≫
    (torusPowerOneIso (Spec (.of E))).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Before taking cycles, the finite mixed point factors through the actual unit point. -/
theorem finitePointMap_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : Eˣ) :
    finitePointMap (k := k) q (rationalTuple E q (mixedTuple q a i b)) =
      finitePointMap (k := k) 1 (WeightOne.rationalPoint E b) ≫
        Cor.graphTargetMap k (base (Spec (.of k))) (varyingCoordinate k q a i) := by
  classical
  apply pullback.hom_ext
  · simp only [Category.assoc, Cor.graphTargetMap_fst, finitePointMap_fst]
  · apply torusPower_left_hom_ext q
    · simp only [Category.assoc, Cor.graphTargetMap_snd_assoc, MorphismProperty.Over.w,
        finitePointMap_target_structure]
    · intro j
      simp only [Category.assoc, finitePointMap_rationalTuple_coordinate,
        Cor.graphTargetMap_snd_assoc, varyingCoordinate_coordinate]
      by_cases hji : j = i
      · subst j
        simp only [mixedTuple, Function.update_self, ite_true, rationalPoint_rationalTuple,
          finitePointMap_rationalTuple_coordinate]
      · simp only [mixedTuple, Function.update_of_ne hji, ite_eq_right hji,
          MorphismProperty.Comma.comp_left, torusPowerToBase_left,
          finitePointMap_target_structure_assoc]
        let S := Spec (.of k)
        let s := scalarMap (k := k) (E := E)
        let c := Units.map (algebraMap k E).toMonoidHom (a j)
        let p (f : Spec (.of E) ⟶ S) : Spec (.of E) ⟶ (multiplicativeGroupObject S).left :=
          (nativeAffineTorusPoint f c).left
        change p s = s ≫ (nativeAffineTorusPoint (𝟙 S) (a j)).left
        exact (congrArg p (Category.comp_id s).symm).trans
          (nativeAffineTorusPoint_natural (𝟙 S) (algebraMap k E) (a j))

variable [Module.Finite k E]

/-- The mixed point correspondence factors with its full original cycle multiplicity. -/
theorem pointPushforward_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : Eˣ) :
    pointPushforward (k := k) q ((Cor.graphFunctor E).map
      (rationalTuple E q (mixedTuple q a i b))) =
      pointPushforward (k := k) 1 ((Cor.graphFunctor E).map (WeightOne.rationalPoint E b)) ≫
        (Cor.graphFunctor k).map (varyingCoordinate k q a i) := by
  apply Subtype.ext
  rw [pointPushforward_graph_val, Cor.comp_graph_val_of_finite, pointPushforward_graph_val,
    finiteCyclePushforward_comp_apply]
  exact finiteCyclePushforward_congr_map _ _ (finitePointMap_varying q a i b) _

/-- The actual finite transfer of a weight-one unit graph has its full determinant norm. -/
theorem pointCycleNorm_pointPushforward_rationalPoint (b : Eˣ) :
    WeightOne.pointCycleNorm k
      (pointPushforward (k := k) 1 ((Cor.graphFunctor E).map (WeightOne.rationalPoint E b))) =
      Additive.ofMul (Units.map (Algebra.norm k) b) := by
  let f := WeightOne.rationalPoint E b
  have h := DiagonalMixedPointNorm.pointCycleNorm_finitePoint
    (finitePointMap (k := k) 1 f) (finitePointMap_fst 1 f) _
    (pointPushforward_graph_fundamental (k := k) 1 f)
  have hcoord : affineCoordinateUnit (finitePointMap (k := k) 1 f) 0 = b := by
    change affineCoordinateUnit (finitePointMap (k := k) 1 (WeightOne.rationalPoint E b)) 0 = _
    rw [rationalPoint_rationalTuple, affineCoordinateUnit_finitePointMap_rationalTuple]
  exact h.trans (congrArg (fun a => Additive.ofMul (Units.map (Algebra.norm k) a)) hcoord)

/-- Actual all-weight corestriction satisfies the mixed norm formula in any position. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/CorestrictionMixed.lean:103-124"
  "adaptation" "The actual finite point and determinant norm in one varying coordinate"]
theorem corestriction_graphSymbol_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : Eˣ) :
    corestriction (k := k) q (graphSymbol E q (mixedTuple q a i b)) =
      graphSymbol k q (Function.update a i (Units.map (Algebra.norm k) b)) := by
  rw [corestriction_graphSymbol, pointPushforward_varying, DiagonalMixedPointNorm.cycle_varying]
  exact congrArg (fun z : Additive kˣ => graphSymbol k q (Function.update a i z.toMul))
    (pointCycleNorm_pointPushforward_rationalPoint (k := k) b)

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestrictionMixed
