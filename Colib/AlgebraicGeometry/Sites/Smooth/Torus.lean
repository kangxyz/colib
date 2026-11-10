/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.GroupSchemes
public import Colib.AlgebraicGeometry.Sites.Smooth.Products
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Native torus powers and identity-coordinate inclusions

Adapted from motivic_source_a6805c4, Smooth/Torus/Basic.lean, to Stacks'
native multiplicative group base change over an arbitrary scheme. The identity
is the point representing the actual unit 1, and powers are literal relative
products, starting at the base. No categorical product in Cor is asserted.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The native multiplicative-group point representing the global unit one. -/
def torusOneOver (S : Scheme.{u}) :
    Over.mk (𝟙 S) ⟶ Scheme.asOver (multiplicativeGroupBaseChange S) S :=
  (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv.symm 1

/-- The identity section of the native multiplicative group on the smooth site. -/
def torusOne (S : Scheme.{u}) : base S ⟶ multiplicativeGroupObject S :=
  homMk (torusOneOver S).left (Over.w (torusOneOver S))

/-- This point represents one under the native global-units representation. -/
theorem torusOneOver_represents_one (S : Scheme.{u}) :
    (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv (torusOneOver S) = 1 :=
  (multiplicativeGroupBaseChangeRepresentsGlobalUnits S).homEquiv.apply_symm_apply 1

/-- Finite torus powers, starting with the actual base scheme. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Torus/Basic.lean:50-58"
  "adaptation" "Literal relative powers of the native Stacks torus over any base"]
def torusPower (S : Scheme.{u}) : ℕ → SmoothSite S
  | 0 => base S
  | q + 1 => product (multiplicativeGroupObject S) (torusPower S q)

@[simp] theorem torusPower_zero (S : Scheme.{u}) :
    torusPower S 0 = base S := rfl

@[simp] theorem torusPower_succ (S : Scheme.{u}) (q : ℕ) :
    torusPower S (q + 1) = product (multiplicativeGroupObject S) (torusPower S q) := rfl

/-- The structure morphism to the zeroth power. -/
def torusPowerToBase (S : Scheme.{u}) (q : ℕ) :
    torusPower S q ⟶ base S :=
  homMk (torusPower S q).hom (Category.comp_id _)

@[simp] theorem torusPowerToBase_left (S : Scheme.{u}) (q : ℕ) :
    (torusPowerToBase S q).left = (torusPower S q).hom := rfl

@[simp] theorem torusPowerToBase_zero (S : Scheme.{u}) :
    torusPowerToBase S 0 = 𝟙 (base S) :=
  MorphismProperty.Over.Hom.ext rfl

/-- The coordinate projections of the actual recursive relative product. -/
def torusCoordinate (S : Scheme.{u}) :
    (q : ℕ) → Fin q → (torusPower S q ⟶ multiplicativeGroupObject S)
  | 0, i => Fin.elim0 i
  | q + 1, i => Fin.cases (productFst (multiplicativeGroupObject S) (torusPower S q))
      (fun j => productSnd (multiplicativeGroupObject S) (torusPower S q) ≫ torusCoordinate S q j) i

@[simp] theorem torusCoordinate_zero (S : Scheme.{u}) (q : ℕ) :
    torusCoordinate S (q + 1) 0 = productFst (multiplicativeGroupObject S) (torusPower S q) := rfl

@[simp] theorem torusCoordinate_succ (S : Scheme.{u}) (q : ℕ) (i : Fin q) :
    torusCoordinate S (q + 1) i.succ =
      productSnd (multiplicativeGroupObject S) (torusPower S q) ≫ torusCoordinate S q i := rfl

/-- Lift any tuple of actual maps into the relative torus power. -/
def torusPowerLift (S : Scheme.{u}) {X : SmoothSite S} :
    (q : ℕ) → (Fin q → (X ⟶ multiplicativeGroupObject S)) → (X ⟶ torusPower S q)
  | 0, _ => homMk X.hom (Category.comp_id _)
  | q + 1, f => productLift (f 0) (torusPowerLift S q (fun i => f i.succ))

@[reassoc (attr := simp)]
theorem torusPowerLift_coordinate (S : Scheme.{u}) {X : SmoothSite S}
    (q : ℕ) (f : Fin q → (X ⟶ multiplicativeGroupObject S)) (i : Fin q) :
    torusPowerLift S q f ≫ torusCoordinate S q i = f i := by
  induction q with
  | zero => exact Fin.elim0 i
  | succ q ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact productLift_fst _ _
    · simp only [torusCoordinate_succ, torusPowerLift, ← Category.assoc,
        productLift_snd, ih]

/-- Maps into a torus power are determined by their coordinate maps. -/
theorem torusPower_hom_ext (S : Scheme.{u}) {X : SmoothSite S}
    (q : ℕ) {f g : X ⟶ torusPower S q}
    (h : ∀ i, f ≫ torusCoordinate S q i = g ≫ torusCoordinate S q i) : f = g := by
  induction q with
  | zero =>
    apply MorphismProperty.Over.Hom.ext
    have hf := MorphismProperty.Over.w f
    have hg := MorphismProperty.Over.w g
    change f.left ≫ 𝟙 S = X.hom at hf
    change g.left ≫ 𝟙 S = X.hom at hg
    exact (Category.comp_id f.left).symm.trans
      ((hf.trans hg.symm).trans (Category.comp_id g.left))
  | succ q ih =>
    apply product_hom_ext
    · exact h 0
    · apply ih
      intro i
      simpa only [torusCoordinate_succ, Category.assoc] using h i.succ

@[simp] theorem torusPowerLift_coordinates (S : Scheme.{u}) (q : ℕ) :
    torusPowerLift S q (torusCoordinate S q) = 𝟙 (torusPower S q) := by
  apply torusPower_hom_ext
  intro i
  simp

/-- Insert the literal identity section in the chosen coordinate. -/
def torusInsertOne (S : Scheme.{u}) (q : ℕ) (i : Fin (q + 1)) :
    torusPower S q ⟶ torusPower S (q + 1) :=
  torusPowerLift S (q + 1)
    (Fin.insertNth i (torusPowerToBase S q ≫ torusOne S) (torusCoordinate S q))

@[reassoc (attr := simp)]
theorem torusInsertOne_coordinate_self (S : Scheme.{u}) (q : ℕ)
    (i : Fin (q + 1)) :
    torusInsertOne S q i ≫ torusCoordinate S (q + 1) i =
      torusPowerToBase S q ≫ torusOne S := by
  simp [torusInsertOne]

@[reassoc (attr := simp)]
theorem torusInsertOne_coordinate_succAbove (S : Scheme.{u}) (q : ℕ)
    (i : Fin (q + 1)) (j : Fin q) :
    torusInsertOne S q i ≫ torusCoordinate S (q + 1) (i.succAbove j) =
      torusCoordinate S q j := by
  simp [torusInsertOne]

/-- On the underlying schemes, the inserted coordinate is the actual unit section. -/
@[reassoc]
theorem torusInsertOne_left_coordinate_self (S : Scheme.{u}) (q : ℕ)
    (i : Fin (q + 1)) :
    (torusInsertOne S q i).left ≫ (torusCoordinate S (q + 1) i).left =
      (torusPower S q).hom ≫ (torusOne S).left :=
  congrArg (fun f => f.left) (torusInsertOne_coordinate_self S q i)

/-- On the underlying schemes, every other coordinate is retained literally. -/
@[reassoc]
theorem torusInsertOne_left_coordinate_succAbove (S : Scheme.{u}) (q : ℕ)
    (i : Fin (q + 1)) (j : Fin q) :
    (torusInsertOne S q i).left ≫
      (torusCoordinate S (q + 1) (i.succAbove j)).left =
        (torusCoordinate S q j).left :=
  congrArg (fun f => f.left) (torusInsertOne_coordinate_succAbove S q i j)

/-- Forget one coordinate of a torus power. -/
def torusDeleteCoordinate (S : Scheme.{u}) (q : ℕ) (i : Fin (q + 1)) :
    torusPower S (q + 1) ⟶ torusPower S q :=
  torusPowerLift S q (fun j => torusCoordinate S (q + 1) (i.succAbove j))

@[reassoc (attr := simp)]
theorem torusDeleteCoordinate_coordinate (S : Scheme.{u}) (q : ℕ)
    (i : Fin (q + 1)) (j : Fin q) :
    torusDeleteCoordinate S q i ≫ torusCoordinate S q j =
      torusCoordinate S (q + 1) (i.succAbove j) := by
  simp [torusDeleteCoordinate]

@[reassoc (attr := simp)]
theorem torusInsertOne_deleteCoordinate (S : Scheme.{u}) (q : ℕ)
    (i : Fin (q + 1)) :
    torusInsertOne S q i ≫ torusDeleteCoordinate S q i = 𝟙 (torusPower S q) := by
  apply torusPower_hom_ext
  intro j
  simp

/-- Each identity-coordinate inclusion is a closed immersion of the actual schemes. -/
instance instIsClosedImmersionTorusInsertOne (S : Scheme.{u}) (q : ℕ)
    (i : Fin (q + 1)) : IsClosedImmersion (torusInsertOne S q i).left := by
  have : IsSeparated ((torusDeleteCoordinate S q i).left ≫ (torusPower S q).hom) := by
    rw [MorphismProperty.Over.w]
    infer_instance
  have : IsSeparated (torusDeleteCoordinate S q i).left :=
    IsSeparated.of_comp _ (torusPower S q).hom
  have h : (torusInsertOne S q i).left ≫ (torusDeleteCoordinate S q i).left =
      𝟙 (torusPower S q).left :=
    congrArg (fun f => f.left) (torusInsertOne_deleteCoordinate S q i)
  have : IsClosedImmersion
      ((torusInsertOne S q i).left ≫ (torusDeleteCoordinate S q i).left) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ (torusDeleteCoordinate S q i).left

/-- The first recursive power is canonically the actual Laurent torus. -/
def torusPowerOneIso (S : Scheme.{u}) : torusPower S 1 ≅ multiplicativeGroupObject S where
  hom := torusCoordinate S 1 0
  inv := torusPowerLift S 1 (fun _ => 𝟙 (multiplicativeGroupObject S))
  hom_inv_id := by
    apply torusPower_hom_ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Category.assoc, torusPowerLift_coordinate, Category.comp_id, Category.id_comp]
  inv_hom_id := torusPowerLift_coordinate S 1 _ 0

@[reassoc (attr := simp)]
theorem torusInsertOne_zero_powerOneIso (S : Scheme.{u}) :
    torusInsertOne S 0 0 ≫ (torusPowerOneIso S).hom = torusOne S := by
  change torusInsertOne S 0 0 ≫ torusCoordinate S 1 0 = _
  rw [torusInsertOne_coordinate_self, torusPowerToBase_zero]
  exact Category.id_comp _

attribute [colib_tag "COL-0384"]
  torusPower
  torusOneOver_represents_one
  torusInsertOne
  torusInsertOne_coordinate_self
  torusInsertOne_coordinate_succAbove
  instIsClosedImmersionTorusInsertOne

end AlgebraicGeometry.Scheme.SmoothSite
