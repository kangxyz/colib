/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.TopDegree
public import Colib.AlgebraicGeometry.MotivicCohomology.WeightOne.FieldEquivalence

/-!
# Rational tuple graphs in diagonal motivic cohomology

A tuple of units gives the class of its actual graph in the reduced singular
zero-cycle quotient. The identity axes give the zero-coordinate relations.
Inserting one varying coordinate descends to the reduced transfer presheaves,
so the weight-one graph relation gives multiplicativity in each position.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCycleSymbols

open _root_.AlgebraicGeometry.Scheme
open PresheafWithTransfers DiagonalTopDegree NativeTorusPolynomial

variable (k : Type u) [Field k]

/-- The correspondence target of the native ordered torus power. -/
abbrev target (q : ℕ) : Cor k := Cor.mk (SmoothSite.torusPower (Spec (.of k)) q)

/-- The class of a signed point cycle, via the actual zero-simplex projection. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/CycleSymbols.lean:39-50"
  "adaptation" "Class map for actual signed point correspondences"]
def cycleClass (q : ℕ) : (point k ⟶ target k q) →+
    (motivicRawBaseComplex k q).homology q :=
  (singularClass k q).comp
    (((toReducedTorus k q).hom.app (op (Cor.simplexProduct (point k) 0))).hom.comp
      ((AddEquiv.ulift : ULift.{u + 1}
        (Cor.simplexProduct (point k) 0 ⟶ target k q) ≃+
          (Cor.simplexProduct (point k) 0 ⟶ target k q)).symm.toAddMonoidHom.comp
        (Preadditive.leftComp (target k q) (WeightOne.zeroSimplexProjection k))))

/-- A point cycle retains its literal representative in the reduced zero-chains. -/
theorem cycleClass_apply (q : ℕ) (z : point k ⟶ target k q) :
    cycleClass k q z = singularClass k q
      ((toReducedTorus k q).hom.app (op (Cor.simplexProduct (point k) 0))
        (ULift.up (WeightOne.zeroSimplexProjection k ≫ z))) := rfl

/-- The all-weight construction specializes to the existing weight-one class map. -/
theorem cycleClass_one (z : point k ⟶ target k 1) :
    cycleClass k 1 z = WeightOne.cycleClass k z := rfl

/-- A signed cycle through an identity axis already vanishes in reduced zero-chains. -/
theorem cycleClass_axis (q : ℕ) (i : Fin (q + 1)) (z : point k ⟶ target k q) :
    cycleClass k (q + 1) (z ≫ (Cor.graphFunctor k).map
      (SmoothSite.torusInsertOne (Spec (.of k)) q i)) = 0 := by
  have h := congrArg (fun η => η.hom.app (op (Cor.simplexProduct (point k) 0)))
    (torusIdentityAxis_toReducedTorus k (q + 1) i)
  have hz := ConcreteCategory.congr_hom h
    (ULift.up (WeightOne.zeroSimplexProjection k ≫ z))
  change (toReducedTorus k (q + 1)).hom.app (op (Cor.simplexProduct (point k) 0))
    ((torusIdentityAxis k (q + 1) i).hom.app (op (Cor.simplexProduct (point k) 0))
      (ULift.up (WeightOne.zeroSimplexProjection k ≫ z))) = 0 at hz
  rw [torusIdentityAxis_app_apply, Category.assoc] at hz
  rw [cycleClass_apply, hz, map_zero]

/-- The rational point with its specified ordered unit coordinates. -/
def rationalTuple (q : ℕ) (a : Fin q → kˣ) :
    SmoothSite.base (Spec (.of k)) ⟶ SmoothSite.torusPower (Spec (.of k)) q :=
  SmoothSite.torusPowerLift (Spec (.of k)) q
    (fun i => smoothUnitPoint (𝟙 (Spec (.of k))) (a i))

/-- Every coordinate of the tuple is the native Laurent evaluation at that unit. -/
@[reassoc (attr := simp)]
theorem rationalTuple_coordinate (q : ℕ) (a : Fin q → kˣ) (i : Fin q) :
    rationalTuple k q a ≫ SmoothSite.torusCoordinate (Spec (.of k)) q i =
      smoothUnitPoint (𝟙 (Spec (.of k))) (a i) :=
  SmoothSite.torusPowerLift_coordinate (Spec (.of k)) q _ i

/-- The tuple's composite to the base is the identity of the original field point. -/
@[reassoc (attr := simp)]
theorem rationalTuple_toBase (q : ℕ) (a : Fin q → kˣ) :
    rationalTuple k q a ≫ SmoothSite.torusPowerToBase (Spec (.of k)) q = 𝟙 _ := by
  apply SmoothSite.torusPower_hom_ext (Spec (.of k)) 0
  intro i
  exact Fin.elim0 i

private theorem smoothUnitPoint_base_one :
    smoothUnitPoint (𝟙 (Spec (.of k))) (1 : kˣ) = SmoothSite.torusOne (Spec (.of k)) := by
  apply MorphismProperty.Over.Hom.ext
  change (nativeAffineTorusPoint (𝟙 (Spec (.of k))) (1 : kˣ)).left =
    (SmoothSite.torusOne (Spec (.of k))).left
  rw [affineUnitPoint_one, Category.id_comp]

/-- An identity entry factors the rational point through its literal identity axis. -/
theorem rationalTuple_axis (q : ℕ) (a : Fin (q + 1) → kˣ) (i : Fin (q + 1)) (hi : a i = 1) :
    rationalTuple k (q + 1) a =
      rationalTuple k q (fun j => a (i.succAbove j)) ≫
        SmoothSite.torusInsertOne (Spec (.of k)) q i := by
  apply SmoothSite.torusPower_hom_ext
  intro j
  obtain rfl | ⟨j, rfl⟩ := Fin.eq_self_or_eq_succAbove i j
  · simp only [rationalTuple_coordinate, hi, smoothUnitPoint_base_one, Category.assoc,
      SmoothSite.torusInsertOne_coordinate_self, rationalTuple_toBase_assoc]
  · simp only [rationalTuple_coordinate, Category.assoc,
      SmoothSite.torusInsertOne_coordinate_succAbove]

/-- The raw diagonal class of the literal graph of the ordered tuple. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/CycleSymbols.lean:109-139"
  "adaptation" "Rational ordered tuple and its graph class"]
def graphSymbol (q : ℕ) (a : Fin q → kˣ) : (motivicRawBaseComplex k q).homology q :=
  cycleClass k q ((Cor.graphFunctor k).map (rationalTuple k q a))

/-- Any identity entry gives a zero diagonal graph class. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/CycleSymbols.lean:91-148"
  "adaptation" "Vanishing via the literal identity axis"]
theorem graphSymbol_one (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (hi : a i = 1) :
    graphSymbol k q a = 0 := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    rw [graphSymbol, rationalTuple_axis k q a i hi, Functor.map_comp]
    exact cycleClass_axis k q i _

private theorem coefficientMap_boundary {m n : ℕ} (η : reducedTorus k m ⟶ reducedTorus k n)
    (x : chains k m 1) :
    η.hom.app (op (Cor.simplexProduct (point k) 0)) (boundary k m x) =
      boundary k n (η.hom.app (op (Cor.simplexProduct (point k) 1)) x) := by
  have h := congrArg (fun f => f.hom.app (op (point k))) ((singularComplexMap η).comm 1 0)
  exact (ConcreteCategory.congr_hom h x).symm

/-- A coefficient morphism sends each singular boundary to a singular boundary. -/
def quotientMap {m n : ℕ} (η : reducedTorus k m ⟶ reducedTorus k n) :
    zeroHomology k m →+ zeroHomology k n :=
  QuotientAddGroup.map (boundary k m).range (boundary k n).range
    (η.hom.app (op (Cor.simplexProduct (point k) 0))).hom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨η.hom.app (op (Cor.simplexProduct (point k) 1)) x,
        (coefficientMap_boundary k η x).symm⟩)

/-- The induced map between the raw diagonal groups, in their respective top degrees. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/Diagonal/CoordinateInsertion.lean:42-76"
  "adaptation" "Descent of actual coefficient morphisms through the singular boundary"]
def rawMap {m n : ℕ} (η : reducedTorus k m ⟶ reducedTorus k n) :
    (motivicRawBaseComplex k m).homology m →+ (motivicRawBaseComplex k n).homology n :=
  (quotientToRawEquiv k n).toAddMonoidHom.comp
    ((quotientMap k η).comp (quotientToRawEquiv k m).symm.toAddMonoidHom)

/-- The induced map acts by the original coefficient morphism on a zero-chain. -/
theorem rawMap_singularClass {m n : ℕ} (η : reducedTorus k m ⟶ reducedTorus k n)
    (x : chains k m 0) :
    rawMap k η (singularClass k m x) =
      singularClass k n (η.hom.app (op (Cor.simplexProduct (point k) 0)) x) := by
  rw [← quotientToRawEquiv_mk k m]
  change quotientToRawEquiv k n (quotientMap k η
    ((quotientToRawEquiv k m).symm (quotientToRawEquiv k m _))) = _
  rw [AddEquiv.symm_apply_apply]
  exact quotientToRawEquiv_mk k n _

/-- An induced map from graph postcomposition retains the original signed cycles. -/
theorem rawMap_cycleClass {m n : ℕ}
    (f : SmoothSite.torusPower (Spec (.of k)) m ⟶ SmoothSite.torusPower (Spec (.of k)) n)
    (η : reducedTorus k m ⟶ reducedTorus k n)
    (hη : toReducedTorus k m ≫ η =
      (representableLarge k).map ((Cor.graphFunctor k).map f) ≫ toReducedTorus k n)
    (z : point k ⟶ target k m) :
    rawMap k η (cycleClass k m z) = cycleClass k n (z ≫ (Cor.graphFunctor k).map f) := by
  rw [cycleClass_apply, cycleClass_apply, rawMap_singularClass, ← Category.assoc]
  exact congrArg (singularClass k n) (congrArg
    (fun T => T.hom.app (op (Cor.simplexProduct (point k) 0))
      (ULift.up (WeightOne.zeroSimplexProjection k ≫ z))) hη)

/-- Vary one torus coordinate and fix every other coordinate at the given unit. -/
def varyingCoordinate (q : ℕ) (a : Fin q → kˣ) (i : Fin q) :
    SmoothSite.torusPower (Spec (.of k)) 1 ⟶ SmoothSite.torusPower (Spec (.of k)) q :=
  SmoothSite.torusPowerLift (Spec (.of k)) q (fun j => if j = i then
    SmoothSite.torusCoordinate (Spec (.of k)) 1 0 else
      SmoothSite.torusPowerToBase (Spec (.of k)) 1 ≫
        smoothUnitPoint (𝟙 (Spec (.of k))) (a j))

private theorem rationalPoint_coordinate (b : kˣ) :
    WeightOne.rationalPoint k b ≫ SmoothSite.torusCoordinate (Spec (.of k)) 1 0 =
      smoothUnitPoint (𝟙 (Spec (.of k))) b := by
  change (smoothUnitPoint (𝟙 (Spec (.of k))) b ≫
    (SmoothSite.torusPowerOneIso (Spec (.of k))).inv) ≫
      (SmoothSite.torusPowerOneIso (Spec (.of k))).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem rationalPoint_toBase (b : kˣ) :
    WeightOne.rationalPoint k b ≫ SmoothSite.torusPowerToBase (Spec (.of k)) 1 = 𝟙 _ := by
  apply SmoothSite.torusPower_hom_ext (Spec (.of k)) 0
  intro i
  exact Fin.elim0 i

/-- Evaluation at a unit in the varying coordinate gives the specified updated tuple. -/
@[reassoc]
theorem rationalPoint_varyingCoordinate (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b : kˣ) :
    WeightOne.rationalPoint k b ≫ varyingCoordinate k q a i =
      rationalTuple k q (Function.update a i b) := by
  apply SmoothSite.torusPower_hom_ext
  intro j
  rw [Category.assoc, varyingCoordinate, SmoothSite.torusPowerLift_coordinate,
    rationalTuple_coordinate]
  by_cases h : j = i
  · subst j
    simp only [ite_true, Function.update_self, rationalPoint_coordinate]
  · simp only [h, ite_false, Function.update_of_ne h, ← Category.assoc, rationalPoint_toBase,
      Category.id_comp]

private theorem rationalPoint_one :
    WeightOne.rationalPoint k 1 = SmoothSite.torusInsertOne (Spec (.of k)) 0 0 := by
  apply (cancel_mono (SmoothSite.torusPowerOneIso (Spec (.of k))).hom).1
  rw [SmoothSite.torusInsertOne_zero_powerOneIso]
  exact (rationalPoint_coordinate k 1).trans (smoothUnitPoint_base_one k)

/-- The source identity axis lands on the target identity axis at the varying position. -/
theorem varyingCoordinate_axis (q : ℕ) (a : Fin (q + 1) → kˣ) (i : Fin (q + 1)) :
    SmoothSite.torusInsertOne (Spec (.of k)) 0 0 ≫ varyingCoordinate k (q + 1) a i =
      rationalTuple k q (fun j => a (i.succAbove j)) ≫
        SmoothSite.torusInsertOne (Spec (.of k)) q i := by
  have h : (fun j => Function.update a i (1 : kˣ) (i.succAbove j)) =
      fun j => a (i.succAbove j) := by
    funext j
    exact Function.update_of_ne (Fin.succAbove_ne i j) _ _
  rw [← rationalPoint_one, rationalPoint_varyingCoordinate,
    rationalTuple_axis k q _ i (Function.update_self i 1 a), h]

/-- Varying one coordinate gives a morphism of the actual reduced transfer presheaves. -/
def coordinateInsertion (q : ℕ) (a : Fin (q + 1) → kˣ) (i : Fin (q + 1)) :
    reducedTorus k 1 ⟶ reducedTorus k (q + 1) :=
  reducedTorusDesc k 1
    ((representableLarge k).map ((Cor.graphFunctor k).map (varyingCoordinate k (q + 1) a i)) ≫
      toReducedTorus k (q + 1)) (by
        intro s
        have hs : s = 0 := Subsingleton.elim _ _
        subst s
        change (representableLarge k).map
          ((Cor.graphFunctor k).map (SmoothSite.torusInsertOne (Spec (.of k)) 0 0)) ≫
            (representableLarge k).map
              ((Cor.graphFunctor k).map (varyingCoordinate k (q + 1) a i)) ≫ _ = 0
        rw [← Functor.map_comp_assoc, ← Functor.map_comp, varyingCoordinate_axis,
          Functor.map_comp, Functor.map_comp, Category.assoc]
        change (representableLarge k).map
          ((Cor.graphFunctor k).map (rationalTuple k q (fun j => a (i.succAbove j)))) ≫
            (torusIdentityAxis k (q + 1) i ≫ toReducedTorus k (q + 1)) = 0
        rw [torusIdentityAxis_toReducedTorus, comp_zero])

/-- On representatives the descended coefficient map is literal graph postcomposition. -/
theorem toReducedTorus_coordinateInsertion (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i : Fin (q + 1)) :
    toReducedTorus k 1 ≫ coordinateInsertion k q a i =
      (representableLarge k).map ((Cor.graphFunctor k).map (varyingCoordinate k (q + 1) a i)) ≫
        toReducedTorus k (q + 1) :=
  toReducedTorus_desc k 1 _ _

/-- The descended insertion sends the genuine weight-one graph to the updated tuple graph. -/
theorem rawMap_coordinateInsertion_graphUnit (q : ℕ) (a : Fin (q + 1) → kˣ)
    (i : Fin (q + 1)) (b : kˣ) :
    rawMap k (coordinateInsertion k q a i) (WeightOne.graphUnitClass k b) =
      graphSymbol k (q + 1) (Function.update a i b) := by
  unfold WeightOne.graphUnitClass graphSymbol
  rw [← cycleClass_one, rawMap_cycleClass k (varyingCoordinate k (q + 1) a i) _
    (toReducedTorus_coordinateInsertion k q a i), ← Functor.map_comp,
    rationalPoint_varyingCoordinate]

/-- Multiplying units in one coordinate adds their actual diagonal graph classes. -/
@[colib_ref "motivic_source_a6805c4" "Motivic/Cohomology/Diagonal/CycleSymbols.lean:150-172,205-214"
  "adaptation" "Coordinate multiplicativity via the genuine weight-one graph relation"]
theorem graphSymbol_mul (q : ℕ) (a : Fin q → kˣ) (i : Fin q) (b c : kˣ) :
    graphSymbol k q (Function.update a i (b * c)) =
      graphSymbol k q (Function.update a i b) + graphSymbol k q (Function.update a i c) := by
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    have h := congrArg (rawMap k (coordinateInsertion k q a i)) (WeightOne.graphUnitClass_mul k b c)
    simpa only [map_add, rawMap_coordinateInsertion_graphUnit] using h

end AlgebraicGeometry.MotivicCohomology.DiagonalCycleSymbols
