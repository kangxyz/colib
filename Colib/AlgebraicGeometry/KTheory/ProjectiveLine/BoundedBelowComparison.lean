/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectOppositeJoint
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJointInclusion
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.BaseFactorization
public import Colib.KTheory.Waldhausen.Approximation.GeneralKEquivalence
public import Colib.CategoryTheory.Waldhausen.Duality.SConstruction
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.QuasiCompactBounded
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Bounded below representatives for perfect K-theory

On a quasi-compact scheme, the inclusion of perfect complexes whose terms vanish below
some bound induces the actual K-group isomorphisms. Good lower truncation gives
approximation in the opposite categories, and Waldhausen duality identifies the maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry HomologicalComplex Topology
open scoped ZeroObject

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

/-- The actual original locally perfect complexes with lower-bounded terms. -/
def objects (X : Scheme.{u}) : ObjectProperty (CochainComplex X.Modules ℤ) := fun K =>
  RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K ∧ ∃ a : ℤ, K.IsStrictlyGE a

/-- The full subcategory of locally perfect complexes whose terms vanish below some degree. -/
abbrev Obj (X : Scheme.{u}) := (objects X).FullSubcategory

variable {X : Scheme.{u}}

lemma objects_of_isZero {K : CochainComplex X.Modules ℤ} (hK : IsZero K) : objects X K := by
  refine ⟨RingedSpace.isPerfectComplex_of_forall_isZero (fun n =>
    (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero hK), 0, ?_⟩
  exact (CochainComplex.isStrictlyGE_iff _ _).mpr
    (fun n _ => (HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) n).map_isZero hK)

instance containsZero : (objects X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, objects_of_isZero (isZero_zero _)⟩

lemma objects_of_iso {K L : CochainComplex X.Modules ℤ} (e : K ≅ L) (hK : objects X K) :
    objects X L := by
  obtain ⟨hp, a, ha⟩ := hK
  let := ha
  exact ⟨hp.of_iso e, a, CochainComplex.isStrictlyGE_of_iso e a⟩

instance closedUnderIsomorphisms : (objects X).IsClosedUnderIsomorphisms where
  of_iso e hK := objects_of_iso e hK

lemma objects_of_shortExact {S : ShortComplex (CochainComplex X.Modules ℤ)} (hS : S.ShortExact)
    (h₁ : objects X S.X₁) (h₃ : objects X S.X₃) : objects X S.X₂ := by
  obtain ⟨hp₁, a, ha⟩ := h₁
  obtain ⟨hp₃, b, hb⟩ := h₃
  let := ha
  let := hb
  refine ⟨RingedSpace.isPerfectComplex_X₂_of_shortExact X.toRingedSpace hS hp₁ hp₃, min a b,
    (CochainComplex.isStrictlyGE_iff _ _).mpr ?_⟩
  intro n hn
  have hs := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n
  exact hs.exact.isZero_X₂
    ((S.X₁.isZero_of_isStrictlyGE a n (by omega)).eq_of_src _ _)
    ((S.X₃.isZero_of_isStrictlyGE b n (by omega)).eq_of_tgt _ _)

instance extensionClosed :
    (abelianExactStructure (CochainComplex X.Modules ℤ)).IsExtensionClosed (objects X) where
  prop_middle := objects_of_shortExact

instance closedUnderFiniteProducts : (objects X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure (CochainComplex X.Modules ℤ)).extensionClosed_finiteProducts (objects X)

lemma objects_shift {K : CochainComplex X.Modules ℤ} (hK : objects X K) (n : ℤ) : objects X
    (K⟦n⟧) := by
  obtain ⟨hp, a, ha⟩ := hK
  let := ha
  refine ⟨RingedSpace.isPerfectComplex_shift X.toRingedSpace hp n, a - n,
    (CochainComplex.isStrictlyGE_iff _ _).mpr ?_⟩
  intro i hi
  change IsZero (K.X (i + n))
  exact K.isZero_of_isStrictlyGE a (i + n) (by omega)

/-- The inclusion that forgets the lower bound on the terms of a locally perfect complex. -/
def inclusion (X : Scheme.{u}) :
    Obj X ⥤ ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

instance inclusion_additive (X : Scheme.{u}) : (inclusion X).Additive where
  map_add := by intros; rfl

local instance (X : Scheme.{u}) : ObjectProperty.ContainsZero
    (show ObjectProperty (CochainComplex X.Modules ℤ) from
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_containsZero X.toRingedSpace

local instance (X : Scheme.{u}) : ObjectProperty.IsClosedUnderIsomorphisms
    (show ObjectProperty (CochainComplex X.Modules ℤ) from
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_closedUnderIsomorphisms X.toRingedSpace

local instance (X : Scheme.{u}) : (abelianExactStructure
    (CochainComplex X.Modules ℤ)).IsExtensionClosed
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_extensionClosed X.toRingedSpace

local instance (X : Scheme.{u}) : ObjectProperty.IsClosedUnderFiniteProducts
    (show ObjectProperty (CochainComplex X.Modules ℤ) from
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  RingedSpace.isPerfectComplex_closedUnderFiniteProducts X.toRingedSpace

/-- The complex-subcategory Waldhausen structure on lower-bounded locally perfect complexes. -/
def waldhausen (X : Scheme.{u}) : Waldhausen.Structure (Obj X) :=
  Waldhausen.complexSubcategory (objects X)

lemma inclusion_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (waldhausen X).cof (waldhausen X).weq
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq (inclusion X) :=
  { zero := fun h => (inclusion X).map_isZero h
    cofibration := fun f hf =>
      (Waldhausen.complexSubcategory_inclusion_exact (objects X)).cofibration f hf
    weak := fun _ h => h
    pushout := by
      intro A B D P i f g j hi hp
      apply IsPushout.of_map_of_faithful
        (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)))
      exact (Waldhausen.complexSubcategory_inclusion_exact (objects X)).pushout hi hp }

/-- The opposite complex-subcategory Waldhausen structure for lower-bounded perfect complexes. -/
def oppositeWaldhausen (X : Scheme.{u}) : Waldhausen.Structure (Obj X)ᵒᵖ :=
  Waldhausen.oppositeComplexSubcategory (objects X)

lemma opposite_compatible (X : Scheme.{u}) :
    Waldhausen.IsCompatibleDual (waldhausen X) (oppositeWaldhausen X) :=
  Waldhausen.oppositeComplexSubcategory_compatible (objects X)

lemma inclusion_op_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (oppositeWaldhausen X).cof (oppositeWaldhausen X).weq
    (RingedSpace.perfectComplexesOppositeWaldhausen X.toRingedSpace).cof
    (RingedSpace.perfectComplexesOppositeWaldhausen X.toRingedSpace).weq
    (inclusion X).op :=
  Waldhausen.oppositeSubcategoryInclusion_exact (objects X)
    (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) (fun _ h => h.1)

/-- Joint row-factorization data for the opposite structure, using closure under shift by `-1`. -/
def oppositeJointData (X : Scheme.{u}) :
    Waldhausen.Fibration.RowFactorization.JointData
      (Waldhausen.Fibration.NestedWeakEquivalences.refl (oppositeWaldhausen X)) :=
  Waldhausen.oppositeComplexJointData (objects X) (fun _ h => objects_shift h (-1))

/-- Actual App2 in the literal opposite categories; the original arrow is retained. -/
theorem inclusion_op_approximation (X : Scheme.{u}) [CompactSpace X] :
    Waldhausen.HasApproximationProperty (oppositeWaldhausen X)
      (RingedSpace.perfectComplexesOppositeWaldhausen X.toRingedSpace) (inclusion X).op where
  reflects _ h := h
  lift {K L} f := by
    let : HasDerivedCategory.{u + 1} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) :=
      HasDerivedCategory.standard _
    obtain ⟨b, _, hb, _⟩ :=
      Stacks.AlgebraicGeometry.PerfectCohomology.exists_isGE_isLE_of_isPerfect
        X (DerivedCategory.Q.obj L.unop.obj) L.unop.property.isPerfect
    have hLb := (DerivedCategory.isGE_Q_obj_iff L.unop.obj b).mp hb
    let := hLb
    obtain ⟨d, hd⟩ := K.unop.property.2
    let := hd
    let a := min b d
    have hKa : K.unop.obj.IsStrictlyGE a :=
      K.unop.obj.isStrictlyGE_of_ge a d (min_le_right _ _)
    let := hKa
    have hLa : L.unop.obj.IsGE a :=
      L.unop.obj.isGE_of_ge a b (min_le_left _ _)
    let := hLa
    let T : Obj X := ⟨L.unop.obj.truncGE a,
      L.unop.property.of_quasiIso (L.unop.obj.πTruncGE a) inferInstance,
      a, inferInstance⟩
    let s : L.unop.obj ⟶ K.unop.obj := f.unop.hom
    let g : T ⟶ K.unop := ObjectProperty.homMk
      (CochainComplex.truncGEMap s a ≫ inv (K.unop.obj.πTruncGE a))
    let η : L.unop ⟶ (inclusion X).obj T :=
      ObjectProperty.homMk (L.unop.obj.πTruncGE a)
    have hη : (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq η := by
      change QuasiIso (L.unop.obj.πTruncGE a)
      infer_instance
    have hfac : η ≫ (inclusion X).map g = f.unop := by
      apply ObjectProperty.hom_ext
      change L.unop.obj.πTruncGE a ≫
        (CochainComplex.truncGEMap s a ≫ inv (K.unop.obj.πTruncGE a)) = s
      rw [← Category.assoc, CochainComplex.πTruncGE_naturality,
        Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    let D := (oppositeJointData X).sourceFactorization
    let A := Arrow.mk g.op
    let i := D.inclusion.app A
    let q := D.projection.app A
    refine ⟨D.middle.obj A, i, (inclusion X).op.map q ≫ η.op, D.cofibration A, ?_, ?_⟩
    · exact (RingedSpace.perfectComplexesOppositeWaldhausen X.toRingedSpace).weq.comp_mem _ _
        ((inclusion_op_exact X).weak q (D.weak A)) hη
    · rw [← Category.assoc, ← Functor.map_comp, D.factorization A]
      exact congrArg Quiver.Hom.op hfac

/-- The unchanged original S-map is weak by actual opposite approximation and S-duality. -/
theorem inclusion_delooping_weak (X : Scheme.{u}) [CompactSpace X] :
    IsWeakHomotopyEquivalence (Waldhausen.deloopingMap (inclusion_exact X)).hom := by
  let V := RingedSpace.perfectComplexesWaldhausen X.toRingedSpace
  let Vd := RingedSpace.perfectComplexesOppositeWaldhausen X.toRingedSpace
  let hV : V.weq.HasTwoOutOfThreeProperty :=
    Waldhausen.complexSubcategory_saturated (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))
  let : Vd.weq.HasTwoOutOfThreeProperty :=
    inferInstanceAs (V.weq.op.HasTwoOutOfThreeProperty)
  have hd := (inclusion_op_approximation X).deloopingMap_isWeakHomotopyEquivalence_general
    (inclusion_op_exact X) (oppositeJointData X)
  exact Waldhausen.DualSConstruction.sSetMap_weak_of_dual
    (opposite_compatible X)
    (RingedSpace.perfectComplexesOppositeWaldhausen_compatible X.toRingedSpace)
    (inclusion_exact X) (inclusion_op_exact X) hd

/-- The literal original inclusion K-map is bijective in every degree, including zero. -/
theorem inclusion_KMap_bijective (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (inclusion_exact X) n) :=
  Waldhausen.KMap_bijective_of_isWeakHomotopyEquivalence
    (inclusion_exact X) (inclusion_delooping_weak X) n

end AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedBelowComparison.lean:35-108"
  "adaptation" "Actual bounded below inclusion via good truncation and opposite approximation"]
  AlgebraicGeometry.Scheme.Modules.BoundedBelowPerfect.inclusion_KMap_bijective
