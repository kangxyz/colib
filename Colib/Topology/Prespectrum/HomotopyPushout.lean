/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.Prespectrum.Homotopy

/-! The original reduced double mapping cylinder, with actual prespectrum structure.
The quotient identifies exactly the two ends and the base cylinder. -/
/-! Implementation provenance: `Quillen/Topology/Prespectrum/HomotopyPushout.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Topology unitInterval
open unitInterval
universe u
namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- Identify the cylinder ends with the two targets and collapse its basepoint line. -/
inductive Relation (k : ℕ) :
    ((B.space k ⊕ C.space k) ⊕ (I × A.space k)) → ((B.space k ⊕ C.space k) ⊕ (I × A.space k)) → Prop
  | left (x : A.space k) : Relation k (.inr (0,x)) (.inl (.inl (f.map k x)))
  | right (x : A.space k) : Relation k (.inr (1,x)) (.inl (.inr (g.map k x)))
  | base (s : I) : Relation k (.inr (s,A.point k)) (.inl (.inl (B.point k)))

/-- The quotient space of the reduced homotopy pushout at each prespectrum level. -/
abbrev Space (k : ℕ) := Quot (Relation f g k)

/-- The left target map into the levelwise homotopy pushout. -/
def left (k : ℕ) : C(B.space k, Space f g k) :=
  ⟨fun y ↦ Quot.mk _ (.inl (.inl y)), continuous_quot_mk.comp (continuous_inl.comp continuous_inl)⟩
/-- The right target map into the levelwise homotopy pushout. -/
def right (k : ℕ) : C(C.space k, Space f g k) :=
  ⟨fun z ↦ Quot.mk _ (.inl (.inr z)), continuous_quot_mk.comp (continuous_inl.comp continuous_inr)⟩
/-- The original cylinder map into the levelwise homotopy pushout. -/
def cylinder (k : ℕ) : C(I × A.space k, Space f g k) :=
  ⟨fun z ↦ Quot.mk _ (.inr z), continuous_quot_mk.comp continuous_inr⟩
/-- The common target basepoint of the levelwise homotopy pushout. -/
def point (k : ℕ) : Space f g k := left f g k (B.point k)

@[simp] theorem cylinder_zero (k : ℕ) (x : A.space k) :
    cylinder f g k (0,x) = left f g k (f.map k x) := Quot.sound (Relation.left x)
@[simp] theorem cylinder_one (k : ℕ) (x : A.space k) :
    cylinder f g k (1,x) = right f g k (g.map k x) := Quot.sound (Relation.right x)
@[simp] theorem cylinder_point (k : ℕ) (s : I) :
    cylinder f g k (s,A.point k) = point f g k := Quot.sound (Relation.base s)
@[simp] theorem right_point (k : ℕ) : right f g k (C.point k) = point f g k := by
  rw [← g.map_point k, ← cylinder_one]
  exact cylinder_point f g k 1

/-- The actual target loops on the left part. -/
def leftLoop (k : ℕ) : C(B.space k, Path (point f g (k+1)) (point f g (k+1))) :=
  (basedLoopMap (left f g (k+1)) rfl).comp (B.structureMap k)
/-- The actual target loops on the right part. -/
def rightLoop (k : ℕ) : C(C.space k, Path (point f g (k+1)) (point f g (k+1))) :=
  (basedLoopMap (right f g (k+1)) (right_point f g (k+1))).comp (C.structureMap k)
/-- The whole cylinder, with independent actual loop parameter. -/
def cylinderLoop (k : ℕ) : C(I × A.space k, Path (point f g (k+1)) (point f g (k+1))) where
  toFun z :=
    { toFun t := cylinder f g (k+1) (z.1,A.structureMap k z.2 t)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  continuous_toFun := by
    apply Path.continuous_uncurry_iff.mp
    change Continuous (fun z : (I × A.space k) × I ↦ cylinder f g (k+1) (z.1.1,A.structureMap k
      z.1.2 z.2))
    fun_prop

/-- The loop-valued pieces respect the original quotient relation. -/
theorem respects (k : ℕ) (a b : ((B.space k ⊕ C.space k) ⊕ (I × A.space k))) (h : Relation f g k
    a b) :
    Sum.elim (Sum.elim (leftLoop f g k) (rightLoop f g k)) (cylinderLoop f g k) a =
      Sum.elim (Sum.elim (leftLoop f g k) (rightLoop f g k)) (cylinderLoop f g k) b := by
  cases h with
  | left x =>
    ext t
    change cylinder f g (k+1) (0,A.structureMap k x t) = left f g (k+1) (B.structureMap k (f.map
      k x) t)
    rw [cylinder_zero]
    exact congrArg (left f g (k+1)) (congrArg (fun p ↦ p t) (f.comm k x))
  | right x =>
    ext t
    change cylinder f g (k+1) (1,A.structureMap k x t) = right f g (k+1) (C.structureMap k
      (g.map k x) t)
    rw [cylinder_one]
    exact congrArg (right f g (k+1)) (congrArg (fun p ↦ p t) (g.comm k x))
  | base s =>
    ext t
    change cylinder f g (k+1) (s,A.structureMap k (A.point k) t) = left f g (k+1)
      (B.structureMap k (B.point k) t)
    rw [A.map_point, B.map_point]
    exact cylinder_point f g (k+1) s

/-- The loop structure map descended from the two targets and the cylinder. -/
def structureMap (k : ℕ) : C(Space f g k, Path (point f g (k+1)) (point f g (k+1))) where
  toFun := Quot.lift (Sum.elim (Sum.elim (leftLoop f g k) (rightLoop f g k)) (cylinderLoop f g
    k)) (respects f g k)
  continuous_toFun := continuous_quot_lift _
    (((leftLoop f g k).continuous.sumElim (rightLoop f g k).continuous).sumElim (cylinderLoop f
      g k).continuous)

@[simp] theorem structureMap_point (k : ℕ) :
    structureMap f g k (point f g k) = Path.refl (point f g (k+1)) := by
  ext t
  change left f g (k+1) (B.structureMap k (B.point k) t) = point f g (k+1)
  rw [B.map_point]
  rfl

/-- The actual reduced double mapping cylinder as a prespectrum. -/
def prespectrum : LoopPrespectrum.{u} where
  space k := TopCat.of (Space f g k)
  point := point f g
  structureMap := structureMap f g
  map_point := structureMap_point f g

/-- The left inclusion into the homotopy-pushout prespectrum. -/
def inl : B ⟶ prespectrum f g where
  map := left f g
  map_point _k := rfl
  comm _k _x := by ext t; rfl

/-- The right inclusion into the homotopy-pushout prespectrum. -/
def inr : C ⟶ prespectrum f g where
  map := right f g
  map_point := right_point f g
  comm _k _x := by ext t; rfl

/-- The original overlap maps agree by the actual coherent cylinder homotopy. -/
def glue : Homotopy (f ≫ inl f g) (g ≫ inr f g) where
  level := cylinder f g
  at_zero := cylinder_zero f g
  at_one := cylinder_one f g
  at_point := cylinder_point f g
  comm _k _s _x _t := rfl

variable {D : LoopPrespectrum.{u}} (b : B ⟶ D) (c : C ⟶ D) (H : Homotopy (f ≫ b) (g ≫ c))

/-- Descend actual prespectrum arrows with the specified original overlap homotopy. -/
def desc : prespectrum f g ⟶ D where
  map k :=
    { toFun := Quot.lift (Sum.elim (Sum.elim (b.map k) (c.map k)) (H.level k)) (by
        intro a b' h
        cases h with
        | left x => exact H.at_zero k x
        | right x => exact H.at_one k x
        | base s => exact (H.at_point k s).trans (b.map_point k).symm)
      continuous_toFun := continuous_quot_lift _
        (((b.map k).continuous.sumElim (c.map k).continuous).sumElim (H.level k).continuous) }
  map_point k := b.map_point k
  comm k q := by
    apply Path.ext
    funext t
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl x => exact congrArg (fun p ↦ p t) (b.comm k x)
        | inr x => exact congrArg (fun p ↦ p t) (c.comm k x)
      | inr z => exact H.comm k z.1 z.2 t

@[simp] theorem inl_desc : inl f g ≫ desc f g b c H = b := by apply Hom.ext; funext k; ext x; rfl
@[simp] theorem inr_desc : inr f g ≫ desc f g b c H = c := by apply Hom.ext; funext k; ext x; rfl
@[simp] theorem desc_cylinder (k : ℕ) (s : I) (x : A.space k) :
    (desc f g b c H).map k (cylinder f g k (s,x)) = H.level k (s,x) := rfl

end Topology.LoopPrespectrum.HomotopyPushout

namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C A' B' C' D : LoopPrespectrum.{u}}
  (f : A ⟶ B) (g : A ⟶ C) (f' : A' ⟶ B') (g' : A' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (hf : f ≫ b = a ≫ f') (hg : g ≫ c = a ≫ g')

/-- Original maps on the three legs induce an actual map on the entire quotient cylinder. -/
def map : prespectrum f g ⟶ prespectrum f' g' where
  map k :=
    { toFun := Quot.lift (Sum.elim
        (Sum.elim (fun y ↦ left f' g' k (b.map k y)) (fun z ↦ right f' g' k (c.map k z)))
        (fun z ↦ cylinder f' g' k (z.1,a.map k z.2))) (by
        intro x y h
        cases h with
        | left x =>
          exact (cylinder_zero f' g' k (a.map k x)).trans
            (congrArg (left f' g' k) (congrArg (fun h ↦ h.map k x) hf.symm))
        | right x =>
          exact (cylinder_one f' g' k (a.map k x)).trans
            (congrArg (right f' g' k) (congrArg (fun h ↦ h.map k x) hg.symm))
        | base s =>
            change cylinder f' g' k (s,a.map k (A.point k)) = left f' g' k (b.map k (B.point k))
            rw [a.map_point, b.map_point]
            exact cylinder_point f' g' k s)
      continuous_toFun := continuous_quot_lift _
        (((left f' g' k).continuous.comp (b.map k).continuous).sumElim
          ((right f' g' k).continuous.comp (c.map k).continuous) |>.sumElim (by fun_prop)) }
  map_point k := congrArg (left f' g' k) (b.map_point k)
  comm k q := by
    apply Path.ext
    funext t
    induction q using Quot.inductionOn with
    | h z => cases z with
      | inl z => cases z with
        | inl x => exact congrArg (left f' g' (k+1)) (congrArg (fun p ↦ p t) (b.comm k x))
        | inr x => exact congrArg (right f' g' (k+1)) (congrArg (fun p ↦ p t) (c.comm k x))
      | inr z =>
        exact congrArg (fun y ↦ cylinder f' g' (k+1) (z.1,y))
          (congrArg (fun p ↦ p t) (a.comm k z.2))

@[simp] theorem inl_map : inl f g ≫ map f g f' g' a b c hf hg = b ≫ inl f' g' := by
  apply Hom.ext; funext k; ext x; rfl
@[simp] theorem inr_map : inr f g ≫ map f g f' g' a b c hf hg = c ≫ inr f' g' := by
  apply Hom.ext; funext k; ext x; rfl
@[simp] theorem map_cylinder (k : ℕ) (s : I) (x : A.space k) :
    (map f g f' g' a b c hf hg).map k (cylinder f g k (s,x)) = cylinder f' g' k (s,a.map k x) := rfl

/-- Both original inclusions and the whole coherent overlap cylinder determine a map. -/
theorem hom_ext {a b : prespectrum f g ⟶ D}
    (hl : inl f g ≫ a = inl f g ≫ b) (hr : inr f g ≫ a = inr f g ≫ b)
    (hc : ∀ k s x, a.map k (cylinder f g k (s, x)) = b.map k (cylinder f g k (s, x))) : a = b := by
  apply Hom.ext
  funext k
  ext q
  induction q using Quot.inductionOn with
  | h z => cases z with
    | inl z => cases z with
      | inl x => exact congrArg (fun h ↦ h.map k x) hl
      | inr x => exact congrArg (fun h ↦ h.map k x) hr
    | inr z => exact hc k z.1 z.2

end Topology.LoopPrespectrum.HomotopyPushout

namespace Topology.LoopPrespectrum.HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

@[simp] theorem map_id : map f g f g (𝟙 A) (𝟙 B) (𝟙 C) (by simp) (by simp) = 𝟙 (prespectrum f g)
    := by
  apply hom_ext
  · apply Hom.ext; funext k; ext x; rfl
  · apply Hom.ext; funext k; ext x; rfl
  · intro k s x; rfl

variable {A' B' C' A'' B'' C'' : LoopPrespectrum.{u}}
  (f' : A' ⟶ B') (g' : A' ⟶ C') (f'' : A'' ⟶ B'') (g'' : A'' ⟶ C'')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
  (hf : f ≫ b = a ≫ f') (hg : g ≫ c = a ≫ g')
  (a' : A' ⟶ A'') (b' : B' ⟶ B'') (c' : C' ⟶ C'')
  (hf' : f' ≫ b' = a' ≫ f'') (hg' : g' ≫ c' = a' ≫ g'')

@[simp] theorem map_comp :
    map f g f' g' a b c hf hg ≫ map f' g' f'' g'' a' b' c' hf' hg' =
      map f g f'' g'' (a ≫ a') (b ≫ b') (c ≫ c')
      (by rw [← Category.assoc, hf, Category.assoc, hf', Category.assoc])
      (by rw [← Category.assoc, hg, Category.assoc, hg', Category.assoc]) := by
  apply hom_ext
  · apply Hom.ext; funext k; ext x; rfl
  · apply Hom.ext; funext k; ext x; rfl
  · intro k s x; rfl

end Topology.LoopPrespectrum.HomotopyPushout

attribute [colib_tag "COL-0338",
  colib_ref "quillen" "Quillen/Topology/Prespectrum/HomotopyPushout.lean" "adaptation"
    "Actual strict-square cylinder, cone-loop maps and supplied-seed finite iteration"]
  Topology.LoopPrespectrum.HomotopyPushout.prespectrum
  Topology.LoopPrespectrum.HomotopyPushout.glue
  Topology.LoopPrespectrum.HomotopyPushout.desc
  Topology.LoopPrespectrum.HomotopyPushout.map
  Topology.LoopPrespectrum.HomotopyPushout.map_id
  Topology.LoopPrespectrum.HomotopyPushout.map_comp
