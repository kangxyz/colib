/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.Prespectrum.Homotopy
public import Colib.Util.References

/-! The actual reduced sequential mapping telescope of loop prespectra.
The topology and all structure maps are constructed on the original quotient.
No claim that this prespectrum is already Omega, or that it computes stable
homotopy groups, is included in this construction. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/Telescope.lean` at
Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual reduced quotient,
continuous structure maps, full cylinder homotopies and strict diagram maps are retained.
Stable homotopy colimits and cone or fiber excision are not asserted. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
open unitInterval
universe u
namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- Identify consecutive stage cylinders and all their basepoint lines. -/
inductive Relation (k : ℕ) : (Σ i, I × (E i).space k) → (Σ i, I × (E i).space k) → Prop
  | step (i : ℕ) (x : (E i).space k) : Relation k ⟨i, (1, x)⟩ ⟨i + 1, (0, (f i).map k x)⟩
  | base (i : ℕ) (s : I) : Relation k ⟨i, (s, (E i).point k)⟩ ⟨0, (0, (E 0).point k)⟩

/-- The quotient space of the reduced prespectrum telescope at each level. -/
abbrev Space (k : ℕ) := Quot (Relation E f k)

/-- The stage cylinder map into the levelwise telescope. -/
def cylinder (k i : ℕ) : C(I × (E i).space k, Space E f k) :=
  ⟨fun z ↦ Quot.mk _ ⟨i, z⟩, continuous_quot_mk.comp (continuous_sigmaMk (i := i))⟩

/-- The common basepoint of the levelwise telescope. -/
def point (k : ℕ) : Space E f k := cylinder E f k 0 (0, (E 0).point k)

@[simp] theorem cylinder_one (k i : ℕ) (x : (E i).space k) :
    cylinder E f k i (1, x) = cylinder E f k (i + 1) (0, (f i).map k x) := Quot.sound (Relation.step
      i x)
@[simp] theorem cylinder_point (k i : ℕ) (s : I) :
    cylinder E f k i (s, (E i).point k) = point E f k := Quot.sound (Relation.base i s)

/-- Actual adjoint structure map before descending the stage identifications. -/
def structurePiece (k i : ℕ) :
    C(I × (E i).space k, Path (point E f (k + 1)) (point E f (k + 1))) where
  toFun z :=
    { toFun t := cylinder E f (k + 1) i (z.1, (E i).structureMap k z.2 t)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (I × (E i).space k) × I ↦
      cylinder E f (k + 1) i (z.1.1, (E i).structureMap k z.1.2 z.2))
    fun_prop

/-- The original structure maps respect both telescope gluing and the collapsed base ray. -/
theorem structurePiece_respects (k : ℕ) (a b : Σ i, I × (E i).space k) (h : Relation E f k a b) :
    structurePiece E f k a.1 a.2 = structurePiece E f k b.1 b.2 := by
  cases h with
  | step i x =>
    ext t
    change cylinder E f (k + 1) i (1, (E i).structureMap k x t) =
      cylinder E f (k + 1) (i + 1) (0, (E (i + 1)).structureMap k ((f i).map k x) t)
    rw [cylinder_one]
    exact congrArg (fun y ↦ cylinder E f (k + 1) (i + 1) (0, y))
      (congrArg (fun p ↦ p t) ((f i).comm k x))
  | base i s =>
    ext t
    change cylinder E f (k + 1) i (s, (E i).structureMap k ((E i).point k) t) =
      cylinder E f (k + 1) 0 (0, (E 0).structureMap k ((E 0).point k) t)
    rw [(E i).map_point, (E 0).map_point]
    exact (cylinder_point E f (k + 1) i s).trans (cylinder_point E f (k + 1) 0 0).symm

/-- Continuous descent to the actual loop space of the next quotient. -/
def structureMap (k : ℕ) : C(Space E f k, Path (point E f (k + 1)) (point E f (k + 1))) where
  toFun := Quot.lift (fun z ↦ structurePiece E f k z.1 z.2) (structurePiece_respects E f k)
  continuous_toFun := continuous_quot_lift _ (continuous_sigma (fun i ↦ (structurePiece E f k
    i).continuous))

@[simp] theorem structureMap_cylinder (k i : ℕ) (s : I) (x : (E i).space k) (t : I) :
    structureMap E f k (cylinder E f k i (s, x)) t =
      cylinder E f (k + 1) i (s, (E i).structureMap k x t) := rfl

@[simp] theorem structureMap_point (k : ℕ) :
    structureMap E f k (point E f k) = Path.refl (point E f (k + 1)) := by
  ext t
  change cylinder E f (k + 1) 0 (0, (E 0).structureMap k ((E 0).point k) t) = point E f (k + 1)
  rw [(E 0).map_point]
  exact cylinder_point E f (k + 1) 0 0

/-- The constructed sequential reduced mapping telescope as an actual prespectrum. -/
@[colib_tag "COL-0339",
  colib_ref "quillen" "Quillen/Topology/Prespectrum/Telescope.lean:96" "adaptation"
    "The actual reduced quotient telescope and its loop-prespectrum structure."]
def prespectrum : LoopPrespectrum.{u} where
  space k := TopCat.of (Space E f k)
  point := point E f
  structureMap := structureMap E f
  map_point := structureMap_point E f

/-- The actual initial face of each stage cylinder. -/
def inclusion (i : ℕ) : E i ⟶ prespectrum E f where
  map k := ⟨fun x ↦ cylinder E f k i (0, x),
    (cylinder E f k i).continuous.comp (continuous_const.prodMk continuous_id)⟩
  map_point k := cylinder_point E f k i 0
  comm _k _x := by ext t; rfl

/-- The original telescope cylinders give coherent homotopies of consecutive stage maps. -/
def inclusionHomotopy (i : ℕ) : Homotopy (inclusion E f i) (f i ≫ inclusion E f (i + 1)) where
  level k := cylinder E f k i
  at_zero _k _x := rfl
  at_one k x := cylinder_one E f k i x
  at_point k s := cylinder_point E f k i s
  comm _k _s _x _t := rfl

end Topology.LoopPrespectrum.Telescope

namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  {G : LoopPrespectrum.{u}} (g : ∀ i, E i ⟶ G)
  (H : ∀ i, Homotopy (g i) (f i ≫ g (i + 1)))

/-- A coherent sequence of original maps and original homotopies descends continuously. -/
def desc : prespectrum E f ⟶ G where
  map k :=
    { toFun := Quot.lift (fun z ↦ (H z.1).level k z.2) (by
        intro a b h
        cases h with
        | step i x => exact ((H i).at_one k x).trans ((H (i + 1)).at_zero k ((f i).map k x)).symm
        | base i s => exact ((H i).at_point k s).trans ((H 0).at_point k 0).symm)
      continuous_toFun := continuous_quot_lift _ (continuous_sigma (fun i ↦ ((H i).level
        k).continuous)) }
  map_point k := (H 0).at_point k 0
  comm k q := by
    apply Path.ext
    funext t
    induction q using Quot.inductionOn with
    | h z => exact (H z.1).comm k z.2.1 z.2.2 t

@[simp] theorem inclusion_desc (i : ℕ) : inclusion E f i ≫ desc E f g H = g i := by
  apply Hom.ext
  funext k
  ext x
  exact (H i).at_zero k x

@[simp] theorem desc_cylinder (k i : ℕ) (s : I) (x : (E i).space k) :
    (desc E f g H).map k (cylinder E f k i (s, x)) = (H i).level k (s, x) := rfl

/-- The maps on every whole stage cylinder determine the original telescope map. -/
theorem hom_ext {a b : prespectrum E f ⟶ G}
    (h : ∀ k i s x, a.map k (cylinder E f k i (s, x)) = b.map k (cylinder E f k i (s, x))) : a = b
      := by
  apply Hom.ext
  funext k
  ext q
  induction q using Quot.inductionOn with
  | h z => exact h k z.1 z.2.1 z.2.2

end Topology.LoopPrespectrum.Telescope

namespace Topology.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))
  (E' : ℕ → LoopPrespectrum.{u}) (f' : ∀ i, E' i ⟶ E' (i + 1))
  (a : ∀ i, E i ⟶ E' i) (ha : ∀ i, a i ≫ f' i = f i ≫ a (i + 1))

/-- A strict original map of sequential diagrams acts on each whole telescope cylinder. -/
def map : prespectrum E f ⟶ prespectrum E' f' where
  map k :=
    { toFun := Quot.lift (fun z ↦ cylinder E' f' k z.1 (z.2.1, (a z.1).map k z.2.2)) (by
        intro x y h
        cases h with
        | step i x =>
          rw [cylinder_one]
          exact congrArg (fun y ↦ cylinder E' f' k (i + 1) (0, y)) (congrArg (fun h ↦ h.map k x)
            (ha i))
        | base i s =>
          rw [(a i).map_point, (a 0).map_point]
          exact (cylinder_point E' f' k i s).trans (cylinder_point E' f' k 0 0).symm)
      continuous_toFun := continuous_quot_lift _ (continuous_sigma (fun i ↦ by
        change Continuous (fun z : I × (E i).space k ↦ cylinder E' f' k i (z.1, (a i).map k z.2))
        fun_prop)) }
  map_point k := by
    change cylinder E' f' k 0 (0, (a 0).map k ((E 0).point k)) = point E' f' k
    rw [(a 0).map_point]
    exact cylinder_point E' f' k 0 0
  comm k q := by
    apply Path.ext
    funext t
    induction q using Quot.inductionOn with
    | h z =>
      exact congrArg (fun y ↦ cylinder E' f' (k + 1) z.1 (z.2.1, y))
        (congrArg (fun p ↦ p t) ((a z.1).comm k z.2.2))

@[simp] theorem map_cylinder (k i : ℕ) (s : I) (x : (E i).space k) :
    (map E f E' f' a ha).map k (cylinder E f k i (s, x)) = cylinder E' f' k i (s, (a i).map k x)
      := rfl

@[simp] theorem inclusion_map (i : ℕ) : inclusion E f i ≫ map E f E' f' a ha = a i ≫ inclusion
    E' f' i := by
  apply Hom.ext
  funext k
  ext x
  rfl

@[simp] theorem map_id : map E f E f (fun i ↦ 𝟙 (E i)) (by intro i; simp) = 𝟙 (prespectrum E f)
    := by
  apply hom_ext
  intro k i s x
  rfl

@[simp] theorem map_comp (E'' : ℕ → LoopPrespectrum.{u}) (f'' : ∀ i, E'' i ⟶ E'' (i + 1))
    (b : ∀ i, E' i ⟶ E'' i) (hb : ∀ i, b i ≫ f'' i = f' i ≫ b (i + 1)) :
    map E f E' f' a ha ≫ map E' f' E'' f'' b hb =
      map E f E'' f'' (fun i ↦ a i ≫ b i)
        (by intro i; rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc]) := by
  apply hom_ext
  intro k i s x
  rfl

end Topology.LoopPrespectrum.Telescope
