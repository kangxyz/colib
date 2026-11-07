/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Waldhausen.Additivity.PushoutTransformation
public import Colib.CategoryTheory.Waldhausen.SConstruction.WeakGridHomotopy
public import Colib.CategoryTheory.Waldhausen.SConstruction.NerveCylinderZero

/-!
# Actual mixed-grid transformations of the original additivity deformation

The literal normalized pushout transformation is evaluated on the original mixed interval arrows.
Independent interval and nerve restrictions, both actual cut endpoints, and every chosen-zero
input are retained. The resulting weak-grid cylinder is a prerequisite for a later two-parameter
based-additivity square; no such square or scalar boundary comparison is asserted here.
-/
/- Implementation provenance: Quillen/Waldhausen/Additivity/MixedTransformation.lean
   at c561118b7795eb9780be9ed391c3251d6a4d0afd. Source-only native adaptation;
   no compilation or independent-review claim is made. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open SSet.MixedOrdinalCylinder
open scoped Simplicial
universe u v
namespace CategoryTheory.Waldhausen.Additivity
variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/-- Outer restriction preserves the exact cut-dependent Arrow diagram before any pushout. -/
theorem mixedIntervalArrows_outer {n n' m : SimplexCategory} (μ : n' ⟶ n)
    (φ : Cut n) (A : Grid₂ (mixedOrdinal φ) m ⥤ C) :
    gridMap₂ μ (𝟙 m) ⋙
        intervalArrows (firstIndex φ) (switchedIndex φ) (firstIndex_le_switchedIndex φ) A =
      intervalArrows (firstIndex (μ ≫ φ)) (switchedIndex (μ ≫ φ))
        (firstIndex_le_switchedIndex (μ ≫ φ))
        (gridMap₂ (mixedMap μ (fun _ ↦ le_rfl)) (𝟙 m) ⋙ A) := by
  rw [intervalArrows_outer, intervalArrows_input]
  exact intervalArrows_congr (firstIndex_naturality μ (fun _ ↦ le_rfl)).symm
    (switchedIndex_naturality μ φ).symm A

/-- Both independent restrictions preserve the actual Arrow diagram. -/
theorem mixedIntervalArrows_reindex {n n' m m' : SimplexCategory}
    (μ : n' ⟶ n) (ν : m' ⟶ m) (φ : Cut n) (A : Grid₂ (mixedOrdinal φ) m ⥤ C) :
    gridMap₂ μ ν ⋙
        intervalArrows (firstIndex φ) (switchedIndex φ) (firstIndex_le_switchedIndex φ) A =
      intervalArrows (firstIndex (μ ≫ φ)) (switchedIndex (μ ≫ φ))
        (firstIndex_le_switchedIndex (μ ≫ φ))
        (gridMap₂ (mixedMap μ (fun _ ↦ le_rfl)) ν ⋙ A) := by
  change gridMap₂ μ (𝟙 m') ⋙ (gridMap₂ (𝟙 n) ν ⋙
    intervalArrows (firstIndex φ) (switchedIndex φ) (firstIndex_le_switchedIndex φ) A) = _
  rw [intervalArrows_inner, mixedIntervalArrows_outer]
  rfl

/-- The actual zero cut is the original identity-arrow family. -/
theorem mixedIntervalArrows_zero {n m : SimplexCategory} (A : Grid₂ n m ⥤ C) :
    intervalArrows (firstIndex (zeroCut n)) (switchedIndex (zeroCut n))
        (firstIndex_le_switchedIndex (zeroCut n)) (gridMap₂ (zeroCollapse n) (𝟙 m) ⋙ A) =
      intervalArrows (𝟙 n) (𝟙 n) (fun _ ↦ le_rfl) A := by
  rw [intervalArrows_input]
  exact intervalArrows_congr (firstIndex_zeroCollapse n)
    (by rw [switchedIndex_zero, firstIndex_zeroCollapse]) A

/-- The actual one cut is the unchanged separated-half interval family. -/
theorem mixedIntervalArrows_one {n m : SimplexCategory}
    (A : Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m ⥤ C) :
    intervalArrows (firstIndex (oneCut n)) (switchedIndex (oneCut n))
        (firstIndex_le_switchedIndex (oneCut n))
        (gridMap₂ (inclusion (oneCut n)) (𝟙 m) ⋙ A) =
      intervalArrows (SSet.OrdinalJoin.left n n) (SSet.OrdinalJoin.right n n) (left_le_right n) A := by
  rw [intervalArrows_input]
  exact intervalArrows_congr (firstIndex_inclusion (oneCut n))
    (switchedIndex_one_inclusion n) A

variable (V : Structure C) (W : Structure D) {F G H F' G' H' : C ⥤ D}
  (a : F ⟶ G) (a' : F' ⟶ G') (b : G ⟶ H) (b' : G' ⟶ H')
  (hs : IsCofibrationSequence V W a b) (hs' : IsCofibrationSequence V W a' b')
  (ηF : F ⟶ F') (ηG : G ⟶ G') (haη : a ≫ ηG = ηF ≫ a')

/-- The actual normalized pushout transformation on the unchanged mixed interval arrows. -/
def normalizedMixedTransformation {n m : SimplexCategory} (φ : Cut n)
    (A : Grid₂ (mixedOrdinal φ) m ⥤ C) :
    normalizedMixedGrid V W a hs.exactF hs.exactG hs.cofibration φ A ⟶
      normalizedMixedGrid V W a' hs'.exactF hs'.exactG hs'.cofibration φ A :=
  Functor.whiskerLeft
    (intervalArrows (firstIndex φ) (switchedIndex φ) (firstIndex_le_switchedIndex φ) A)
    (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')

/-- Every component is literally the previously fixed normalized pushout arrow. -/
theorem normalizedMixedTransformation_app {n m : SimplexCategory} (φ : Cut n)
    (A : Grid₂ (mixedOrdinal φ) m ⥤ C) (x : Grid₂ n m) :
    (normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ A).app x =
      (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app
        ((intervalArrows (firstIndex φ) (switchedIndex φ)
          (firstIndex_le_switchedIndex φ) A).obj x) := rfl

/-- Weakness is the original gluing theorem on precisely this actual interval arrow. -/
theorem normalizedMixedTransformation_weak (hηF : ∀ X, W.weq (ηF.app X))
    (hηG : ∀ X, W.weq (ηG.app X)) {n m : SimplexCategory} (φ : Cut n)
    (A : Grid₂ (mixedOrdinal φ) m ⥤ C) (x : Grid₂ n m) :
    W.weq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ A).app x) :=
  normalizedPushoutTransformation_weak W a a' ηF ηG haη b b' V hs hs' hηF hηG _

private theorem normalizedPushoutTransformation_app_heq {f g : Arrow C} (h : f = g) :
    HEq ((normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app f)
      ((normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs').app g) := by
  subst g
  rfl

/-- Independent nerve restriction retains every component of the actual transformation. -/
theorem normalizedMixedTransformation_inner {n m m' : SimplexCategory} (ν : m' ⟶ m)
    (φ : Cut n) (A : Grid₂ (mixedOrdinal φ) m ⥤ C) (x : Grid₂ n m') :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ A).app
        ((gridMap₂ (𝟙 n) ν).obj x))
      ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ
        (gridMap₂ (𝟙 (mixedOrdinal φ)) ν ⋙ A)).app x) :=
  normalizedPushoutTransformation_app_heq V W a a' b b' hs hs' ηF ηG haη
    (congrArg (fun T ↦ T.obj x) (intervalArrows_inner
      (firstIndex φ) (switchedIndex φ) (firstIndex_le_switchedIndex φ) ν A))

/-- Independent outer restriction keeps each original mixed Arrow object. -/
theorem normalizedMixedTransformation_outer {n n' m : SimplexCategory} (μ : n' ⟶ n)
    (φ : Cut n) (A : Grid₂ (mixedOrdinal φ) m ⥤ C) (x : Grid₂ n' m) :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ A).app
        ((gridMap₂ μ (𝟙 m)).obj x))
      ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη (μ ≫ φ)
        (gridMap₂ (mixedMap μ (fun _ ↦ le_rfl)) (𝟙 m) ⋙ A)).app x) :=
  normalizedPushoutTransformation_app_heq V W a a' b b' hs hs' ηF ηG haη
    (congrArg (fun T ↦ T.obj x) (mixedIntervalArrows_outer μ φ A))

/-- Simultaneous restriction is derived from the two independent actual Arrow restrictions. -/
theorem normalizedMixedTransformation_reindex {n n' m m' : SimplexCategory}
    (μ : n' ⟶ n) (ν : m' ⟶ m) (φ : Cut n) (A : Grid₂ (mixedOrdinal φ) m ⥤ C)
    (x : Grid₂ n' m') :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ A).app
        ((gridMap₂ μ ν).obj x))
      ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη (μ ≫ φ)
        (gridMap₂ (mixedMap μ (fun _ ↦ le_rfl)) ν ⋙ A)).app x) :=
  normalizedPushoutTransformation_app_heq V W a a' b b' hs hs' ηF ηG haη
    (congrArg (fun T ↦ T.obj x) (mixedIntervalArrows_reindex μ ν φ A))

/-- Zero-cut recovery keeps the same transformation used by the original identity endpoint. -/
theorem normalizedMixedTransformation_zero {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ C) (x : Grid₂ n m) :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη (zeroCut n)
        (gridMap₂ (zeroCollapse n) (𝟙 m) ⋙ A)).app x)
      ((Functor.whiskerLeft (intervalArrows (𝟙 n) (𝟙 n) (fun _ ↦ le_rfl) A)
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')).app x) :=
  normalizedPushoutTransformation_app_heq V W a a' b b' hs hs' ηF ηG haη
    (congrArg (fun T ↦ T.obj x) (mixedIntervalArrows_zero A))

/-- One-cut recovery keeps the separated endpoint's actual quotient-first comparison input. -/
theorem normalizedMixedTransformation_one {n m : SimplexCategory}
    (A : Grid₂ (SSet.OrdinalSubdivision.δ.obj n) m ⥤ C) (x : Grid₂ n m) :
    HEq ((normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη (oneCut n)
        (gridMap₂ (inclusion (oneCut n)) (𝟙 m) ⋙ A)).app x)
      ((Functor.whiskerLeft
        (intervalArrows (SSet.OrdinalJoin.left n n) (SSet.OrdinalJoin.right n n) (left_le_right n) A)
        (normalizedPushoutTransformation W a a' ηF ηG haη b b' V hs hs')).app x) :=
  normalizedPushoutTransformation_app_heq V W a a' b b' hs hs' ηF ηG haη
    (congrArg (fun T ↦ T.obj x) (mixedIntervalArrows_one A))

/-- Every cut and every independent nerve time keeps the entire chosen-zero diagram. -/
theorem normalizedMixedTransformation_nerveCylinder_zero {n m : SimplexCategory}
    (φ : Cut n) (τ : m ⟶ ⦋1⦌) :
    nerveCylinderDiagram
        (normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη φ
          ((Functor.const (Grid₂ (mixedOrdinal φ) m)).obj V.zero)) τ =
      (Functor.const (Grid₂ n m)).obj W.zero := by
  apply nerveCylinderDiagram_eq_const_of_zero _ W.zero W.isZero
  · intro x
    exact normalizedPushoutFunctor_obj_zero V W a hs.exactF hs.exactG hs.cofibration
  · intro x
    exact normalizedPushoutFunctor_obj_zero V W a' hs'.exactF hs'.exactG hs'.cofibration

/-- The literal family on the original outer mixed cylinder. -/
def normalizedMixedTransformationFamily (n m : SimplexCategoryᵒᵖ)
    (z : ((outerCylinder (bisimplicialSSet V)).obj n).obj m) :
    (((normalizedMixedMap V W a hs.exactF hs.exactG hs.cofibration).app n).app m z).1 ⟶
      (((normalizedMixedMap V W a' hs'.exactF hs'.exactG hs'.cofibration).app n).app m z).1 :=
  normalizedMixedTransformation V W a a' b b' hs hs' ηF ηG haη z.1 z.2.1

/-- The family has the exact diagonal compatibility required by the original nerve cylinder. -/
theorem normalizedMixedTransformationFamily_reindex {n n' : SimplexCategoryᵒᵖ}
    (α : n ⟶ n') (z : (SSet.diagonalSSet (outerCylinder (bisimplicialSSet V))).obj n)
    (x : Grid₂ n'.unop n'.unop) :
    HEq ((normalizedMixedTransformationFamily V W a a' b b' hs hs' ηF ηG haη n' n'
        ((SSet.diagonalSSet (outerCylinder (bisimplicialSSet V))).map α z)).app x)
      ((normalizedMixedTransformationFamily V W a a' b b' hs hs' ηF ηG haη n n z).app
        ((gridMap₂ α.unop α.unop).obj x)) := by
  dsimp only [normalizedMixedTransformationFamily, normalizedMixedTransformation,
    Functor.whiskerLeft_app]
  apply normalizedPushoutTransformation_app_heq V W a a' b b' hs hs' ηF ηG haη
  exact (congrArg (fun T ↦ T.obj x)
    (mixedIntervalArrows_reindex α.unop α.unop z.1 z.2.1)).symm

/-- The actual weak-grid homotopy between the two original mixed deformation maps. -/
def normalizedMixedTransformationHomotopy (hηF : ∀ X, W.weq (ηF.app X))
    (hηG : ∀ X, W.weq (ηG.app X)) :
    SSet.Homotopy
      (SSet.diagonalMap (normalizedMixedMap V W a hs.exactF hs.exactG hs.cofibration))
      (SSet.diagonalMap (normalizedMixedMap V W a' hs'.exactF hs'.exactG hs'.cofibration)) :=
  diagonalWeakGridHomotopy W _ _
    (normalizedMixedTransformationFamily V W a a' b b' hs hs' ηF ηG haη)
    (fun _n _m z x ↦ normalizedMixedTransformation_weak V W a a' b b' hs hs' ηF ηG haη
      hηF hηG z.1 z.2.1 x)
    (normalizedMixedTransformationFamily_reindex V W a a' b b' hs hs' ηF ηG haη)

end CategoryTheory.Waldhausen.Additivity
