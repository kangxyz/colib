/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CycleSymbols

/-!
# Inserting two varying coordinates in diagonal motivic cohomology

The map fixing the other coordinates carries each of the two source identity
axes into its corresponding target axis. Its map on the reduced transfer
presheaves thus carries the actual weight-two graph class to the full tuple.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCoordinateInsertion

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers DiagonalCycleSymbols NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- A map with an identity coordinate factors through the corresponding torus axis. -/
private theorem factor_axis {X : SmoothSite (Spec (.of k))} (q : ℕ)
    (f : X ⟶ SmoothSite.torusPower (Spec (.of k)) (q + 1)) (i : Fin (q + 1))
    (hi : f ≫ SmoothSite.torusCoordinate (Spec (.of k)) (q + 1) i =
      f ≫ SmoothSite.torusPowerToBase (Spec (.of k)) (q + 1) ≫
        SmoothSite.torusOne (Spec (.of k))) :
    f = (f ≫ SmoothSite.torusDeleteCoordinate (Spec (.of k)) q i) ≫
      SmoothSite.torusInsertOne (Spec (.of k)) q i := by
  apply SmoothSite.torusPower_hom_ext
  intro j
  obtain hji | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · subst j
    rw [Category.assoc, SmoothSite.torusInsertOne_coordinate_self, hi]
    have hbase : f ≫ SmoothSite.torusPowerToBase (Spec (.of k)) (q + 1) =
        (f ≫ SmoothSite.torusDeleteCoordinate (Spec (.of k)) q i) ≫
          SmoothSite.torusPowerToBase (Spec (.of k)) q :=
      SmoothSite.torusPower_hom_ext (Spec (.of k)) 0 (fun t => Fin.elim0 t)
    simpa only [Category.assoc] using
      congrArg (fun g => g ≫ SmoothSite.torusOne (Spec (.of k))) hbase
  · simp only [Category.assoc, SmoothSite.torusInsertOne_coordinate_succAbove,
      SmoothSite.torusDeleteCoordinate_coordinate]

/-- Vary two positions and fix all other entries at their prescribed units. -/
def varyingPair (q : ℕ) (a : Fin q → kˣ) (i j : Fin q) :
    SmoothSite.torusPower (Spec (.of k)) 2 ⟶ SmoothSite.torusPower (Spec (.of k)) q :=
  SmoothSite.torusPowerLift (Spec (.of k)) q (fun t => if t = i then
    SmoothSite.torusCoordinate (Spec (.of k)) 2 0 else if t = j then
      SmoothSite.torusCoordinate (Spec (.of k)) 2 1 else
        SmoothSite.torusPowerToBase (Spec (.of k)) 2 ≫
          smoothUnitPoint (𝟙 (Spec (.of k))) (a t))

/-- Evaluating the two varying coordinates at their original units recovers the whole tuple. -/
theorem rationalTuple_varyingPair (q : ℕ) (a : Fin q → kˣ) (i j : Fin q) :
    rationalTuple k 2 ![a i, a j] ≫ varyingPair k q a i j = rationalTuple k q a := by
  apply SmoothSite.torusPower_hom_ext
  intro t
  rw [Category.assoc, varyingPair, SmoothSite.torusPowerLift_coordinate,
    rationalTuple_coordinate]
  by_cases hti : t = i
  · subst t
    simp only [ite_true, rationalTuple_coordinate]
    rfl
  · by_cases htj : t = j
    · subst t
      simp only [hti, ite_false, ite_true, rationalTuple_coordinate]
      rfl
    · simp only [hti, htj, ite_false, ← Category.assoc, rationalTuple_toBase,
        Category.id_comp]

/-- Each source identity axis maps through its corresponding target axis. -/
private theorem varyingPair_axis (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i j : Fin (q + 1)) (hij : i ≠ j) (s : Fin 2) :
    ∃ (t : Fin (q + 1))
      (f : SmoothSite.torusPower (Spec (.of k)) 1 ⟶ SmoothSite.torusPower (Spec (.of k)) q),
      SmoothSite.torusInsertOne (Spec (.of k)) 1 s ≫ varyingPair k (q + 1) a i j =
        f ≫ SmoothSite.torusInsertOne (Spec (.of k)) q t := by
  let f := SmoothSite.torusInsertOne (Spec (.of k)) 1 s ≫ varyingPair k (q + 1) a i j
  let t := if s = 0 then i else j
  refine ⟨t, f ≫ SmoothSite.torusDeleteCoordinate (Spec (.of k)) q t,
    factor_axis k q f t ?_⟩
  have hbase : f ≫ SmoothSite.torusPowerToBase (Spec (.of k)) (q + 1) =
      SmoothSite.torusPowerToBase (Spec (.of k)) 1 :=
    SmoothSite.torusPower_hom_ext (Spec (.of k)) 0 (fun r => Fin.elim0 r)
  rw [← Category.assoc, hbase]
  fin_cases s
  · change (SmoothSite.torusInsertOne (Spec (.of k)) 1 0 ≫ varyingPair k (q + 1) a i j) ≫
      SmoothSite.torusCoordinate (Spec (.of k)) (q + 1) i = _
    simp only [Category.assoc, varyingPair, SmoothSite.torusPowerLift_coordinate,
      ite_true, SmoothSite.torusInsertOne_coordinate_self]
  · change (SmoothSite.torusInsertOne (Spec (.of k)) 1 1 ≫ varyingPair k (q + 1) a i j) ≫
      SmoothSite.torusCoordinate (Spec (.of k)) (q + 1) j = _
    simp only [Category.assoc, varyingPair, SmoothSite.torusPowerLift_coordinate,
      Ne.symm hij, ite_false, ite_true, SmoothSite.torusInsertOne_coordinate_self]

/-- Insertion in distinct positions gives a morphism of the reduced transfer presheaves. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/CoordinateInsertion.lean:79-179"
  "adaptation" "Fixed-coordinate insertion descends through the actual identity axes"]
def pairInsertion (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i j : Fin (q + 1)) (hij : i ≠ j) : reducedTorus k 2 ⟶ reducedTorus k (q + 1) :=
  reducedTorusDesc k 2
    ((representableLarge k).map ((Cor.graphFunctor k).map (varyingPair k (q + 1) a i j)) ≫
      toReducedTorus k (q + 1)) (by
        intro s
        obtain ⟨t, f, hf⟩ := varyingPair_axis k q a i j hij s
        change (representableLarge k).map
          ((Cor.graphFunctor k).map (SmoothSite.torusInsertOne (Spec (.of k)) 1 s)) ≫
            (representableLarge k).map
              ((Cor.graphFunctor k).map (varyingPair k (q + 1) a i j)) ≫ _ = 0
        rw [← Functor.map_comp_assoc, ← Functor.map_comp, hf, Functor.map_comp,
          Functor.map_comp, Category.assoc]
        change (representableLarge k).map ((Cor.graphFunctor k).map f) ≫
          (torusIdentityAxis k (q + 1) t ≫ toReducedTorus k (q + 1)) = 0
        rw [torusIdentityAxis_toReducedTorus, comp_zero])

/-- On signed correspondences the descended insertion is postcomposition with the graph. -/
theorem toReducedTorus_pairInsertion (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i j : Fin (q + 1)) (hij : i ≠ j) :
    toReducedTorus k 2 ≫ pairInsertion k q a i j hij =
      (representableLarge k).map ((Cor.graphFunctor k).map (varyingPair k (q + 1) a i j)) ≫
        toReducedTorus k (q + 1) :=
  toReducedTorus_desc k 2 _ _

/-- The induced raw map sends the weight-two graph to the original whole-tuple graph. -/
theorem rawMap_pairSymbol (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i j : Fin (q + 1)) (hij : i ≠ j) :
    rawMap k (pairInsertion k q a i j hij) (graphSymbol k 2 ![a i, a j]) =
      graphSymbol k (q + 1) a := by
  unfold graphSymbol
  rw [rawMap_cycleClass k (varyingPair k (q + 1) a i j) _
    (toReducedTorus_pairInsertion k q a i j hij), ← Functor.map_comp,
    rationalTuple_varyingPair]

/-- The weight-two Steinberg relation propagates to any distinct pair of coordinates. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/CoordinateInsertion.lean:195-220"
  "adaptation" "The pair insertion sends the vanishing weight-two graph to the full tuple"]
theorem graphSymbol_steinberg_of_two
    (h₂ : ∀ a b : kˣ, (b : k) = 1 - (a : k) → graphSymbol k 2 ![a, b] = 0)
    (q : ℕ) (a : Fin q → kˣ) (i j : Fin q) (hij : i ≠ j)
    (hab : (a i : k) + (a j : k) = 1) : graphSymbol k q a = 0 := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    have h := h₂ (a i) (a j) (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using hab))
    rw [← rawMap_pairSymbol k q a i j hij, h, map_zero]

end AlgebraicGeometry.MotivicCohomology.DiagonalCoordinateInsertion
