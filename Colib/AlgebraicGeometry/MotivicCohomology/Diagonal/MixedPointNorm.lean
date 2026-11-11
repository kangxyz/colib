/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CycleSymbols
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FinitePointEvaluation
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Fixed-coordinate norms of finite point cycles

Insertion into the reduced torus carries the native weight-one norm class
to the fixed-coordinate graph symbol in every weight. The determinant norm
of a finite field point uses the degree over its actual image support.

Adapted from `Motivic/Cohomology/Diagonal/MixedPointNorm.lean` and
`Motivic/Cohomology/WeightOne/FinitePointNorm.lean:140-245` at
`motivic_source_a6805c4`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalMixedPointNorm

open _root_.AlgebraicGeometry.Scheme SmoothSite
open DiagonalTopDegree (point)
open DiagonalCycleSymbols
open DiagonalFinitePointEvaluation
open DiagonalPointNorm (Generator coordinateRing coordinateUnit targetProjection)
open NativeTorusPolynomial (PrimePoint powerOneCycleEquiv cycleNorm cycleNorm_single)

variable (k : Type u) [Field k]

/-- Inserting one varying slot in any signed point cycle gives the graph of its whole norm. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/MixedPointNorm.lean:100-124"
  "adaptation" "The native weight-one norm class under actual fixed-coordinate insertion"]
theorem cycle_varying (q : ℕ) (a : Fin q → kˣ) (i : Fin q)
    (β : point k ⟶ WeightOne.pointTarget k) :
    cycleClass k q (β ≫ (Cor.graphFunctor k).map (varyingCoordinate k q a i)) =
      graphSymbol k q (Function.update a i (WeightOne.pointCycleNorm k β).toMul) := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    have h := rawMap_cycleClass k (varyingCoordinate k (q + 1) a i) _
      (toReducedTorus_coordinateInsertion k q a i) β
    rw [cycleClass_one, WeightOne.cycleClass_eq_graphUnitClass_norm,
      rawMap_coordinateInsertion_graphUnit] at h
    exact h.symm

private theorem pointCycleNorm_single (Z : Generator k 1) (n : ℤ) :
    WeightOne.pointCycleNorm k (singleFiniteCorrespondence _ _ Z.val Z.property n) =
      n • Additive.ofMul (Units.map (Algebra.norm k) (coordinateUnit Z 0)) := by
  classical
  let S := Spec (.of k)
  let f : S ⟶ S := 𝟙 S
  let ψ := (torusPowerOneIso S).hom
  let m : DiagonalFinitePointEvaluation.ambient k 1 ⟶ NativeTorusPolynomial.ambient f :=
    Cor.graphTargetMap k (base S) ψ
  let : IsIso ψ.left := inferInstanceAs (IsIso ((SmoothSite.forgetScheme S).map ψ))
  let : IsClosedImmersion ψ.left := inferInstance
  let : IsClosedImmersion m := Cor.graphTargetMap_isClosedImmersion k (base S) ψ
  let : LocallyOfFiniteType (multiplicativeGroupBaseChange S ↘ S) :=
    inferInstanceAs (LocallyOfFiniteType (multiplicativeGroupObject S).hom)
  have hf : m ≫ pullback.fst f (multiplicativeGroupBaseChange S ↘ S) =
      pullback.fst f (torusPower S 1).hom := Cor.graphTargetMap_fst k (base S) ψ
  let Y : PrimePoint f := ⟨m Z.val, isFiniteCorrespondencePoint_finiteMap f
    (multiplicativeGroupBaseChange S ↘ S) m Z.val (by
      rw [Category.assoc, hf]
      exact Z.property.1) (by
      rw [Category.assoc, hf]
      exact Z.property.2)⟩
  let : Algebra k Y.coordinateRing := NativeTorusPolynomial.PrimePoint.coordinateAlgebra Y
  have hcycle : powerOneCycleEquiv f (singleFiniteCorrespondence _ _ Z.val Z.property n) =
      singleFiniteCorrespondence _ _ Y.val Y.property n := by
    apply Subtype.ext
    change ((singleFiniteCorrespondence _ _ Z.val Z.property n :
      point k ⟶ WeightOne.pointTarget k) ≫ (Cor.graphFunctor k).map ψ).val = single (m Z.val) n
    rw [Cor.comp_graph_val_of_finite]
    exact finiteCyclePushforward_single_of_isClosedImmersion m Z.val n
  obtain ⟨e, he⟩ := exists_iso_integralComponentAt_comp m Z.val
  have he' : e.hom ≫ Y.inclusion = (integralComponentAt Z.val).subschemeι ≫ m := he
  have hπ : e.hom ≫ Y.projection = DiagonalPointNorm.projection Z := by
    change e.hom ≫ (Y.inclusion ≫ pullback.fst f (multiplicativeGroupBaseChange S ↘ S)) =
      (integralComponentAt Z.val).subschemeι ≫ pullback.fst f (torusPower S 1).hom
    simpa only [Category.assoc, hf] using congrArg
        (fun r => r ≫ pullback.fst f (multiplicativeGroupBaseChange S ↘ S)) he'
  let ρ : Y.coordinateRing ≃ₐ[k] coordinateRing Z :=
    { (Scheme.Γ.mapIso e.op).commRingCatIsoToRingEquiv with
      commutes' := fun r => by
        have h := congrArg Scheme.Hom.appTop hπ
        rw [Scheme.Hom.comp_appTop] at h
        exact ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of k)).inv r) }
  have hcoord : ρ (Y.coordinateUnit : Y.coordinateRing) = (coordinateUnit Z 0).val := by
    have h : e.hom ≫ Y.inclusion ≫ pullback.snd f (multiplicativeGroupBaseChange S ↘ S) =
        targetProjection Z ≫ (torusCoordinate S 1 0).left := by
      have hs : m ≫ pullback.snd f (multiplicativeGroupBaseChange S ↘ S) =
          pullback.snd f (torusPower S 1).hom ≫ (torusCoordinate S 1 0).left :=
        Cor.graphTargetMap_snd k (base S) ψ
      change e.hom ≫ Y.inclusion ≫ pullback.snd f (multiplicativeGroupBaseChange S ↘ S) =
        ((integralComponentAt Z.val).subschemeι ≫ pullback.snd f (torusPower S 1).hom) ≫
          (torusCoordinate S 1 0).left
      simpa only [Category.assoc, hs] using congrArg
        (fun r => r ≫ pullback.snd f (multiplicativeGroupBaseChange S ↘ S)) he'
    have hh := congrArg Scheme.Hom.appTop h
    simp only [Scheme.Hom.comp_appTop] at hh
    rw [NativeTorusPolynomial.PrimePoint.coordinateUnit_eq_native]
    exact ConcreteCategory.congr_hom hh (multiplicativeGroupBaseChangeCoordinate S).val
  change cycleNorm f (powerOneCycleEquiv f (singleFiniteCorrespondence _ _ Z.val Z.property n)) = _
  rw [hcycle, cycleNorm_single]
  have hnorm : Y.coordinateNorm = Units.map (Algebra.norm k) (coordinateUnit Z 0) := by
    apply Units.ext
    change Algebra.norm k (Y.coordinateUnit : Y.coordinateRing) =
      Algebra.norm k (coordinateUnit Z 0).val
    exact (Algebra.norm_eq_of_algEquiv ρ _).symm.trans
      (congrArg (Algebra.norm k : coordinateRing Z →* k) hcoord)
  rw [hnorm]

variable {k} {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]

/-- The determinant of a finite point keeps its degree over the native image field. -/
theorem pointCycleNorm_finitePoint (j : Spec (.of E) ⟶ DiagonalFinitePointEvaluation.ambient k 1)
    [IsFinite j] (hj : j ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (β : point k ⟶ WeightOne.pointTarget k)
    (hβ : β.val = finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle (Spec (.of E)))) :
    WeightOne.pointCycleNorm k β = Additive.ofMul
      (Units.map (Algebra.norm k) (affineCoordinateUnit j 0)) := by
  classical
  let Z := imageGenerator j hj
  let : Algebra (coordinateRing Z) E := imageAlgebra j hj
  let : IsScalarTower k (coordinateRing Z) E := imageScalarTower j hj
  let : Module.Finite (coordinateRing Z) E := imageFinite j hj
  let x := genericPoint (Spec (.of E))
  have h : β = singleFiniteCorrespondence _ _ Z.val Z.property
      (j.residueDegree x : ℤ) := by
    apply Subtype.ext
    change β.val = single (j x) (j.residueDegree x : ℤ)
    simpa only [AlgebraicCycle.fundamentalCycle_eq_single_genericPoint,
      finiteCyclePushforward_single, one_mul] using hβ
  refine ((congrArg (WeightOne.pointCycleNorm k) h).trans
    (pointCycleNorm_single k Z (j.residueDegree x : ℤ))).trans ?_
  rw [residueDegree_eq_image_finrank j hj]
  apply Additive.toMul.injective
  simp only [toMul_zsmul, toMul_ofMul, zpow_natCast]
  rw [← imageScalarMap_coordinateUnit j hj 0]
  apply Units.ext
  change Algebra.norm k (coordinateUnit Z 0).val ^ Module.finrank (coordinateRing Z) E =
    Algebra.norm k (algebraMap (coordinateRing Z) E (coordinateUnit Z 0).val)
  symm
  rw [← Algebra.norm_norm (S := coordinateRing Z), Algebra.norm_algebraMap, map_pow]

end AlgebraicGeometry.MotivicCohomology.DiagonalMixedPointNorm
