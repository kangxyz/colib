/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant

/-! # Fixed-exponent subpresheaves with transfers

The subgroup of sections killed by a natural number is stable under every
transfer. Homotopy invariance restricts to this subgroup using the original
projection and zero section.
-/
@[expose] public noncomputable section
open CategoryTheory Opposite
open AlgebraicGeometry.Scheme
universe u v
namespace AlgebraicGeometry.PresheafWithTransfers
variable {k : Type u} [Field k]

/-- Sections killed by `n`, as an actual subgroup of the original sections. -/
def torsionSections (P : PresheafWithTransfers.{v} k) (n : ℕ) (X : Cor k) :
    AddSubgroup (sections P X) where
  carrier := {x | n • x = 0}
  zero_mem' := nsmul_zero n
  add_mem' hx hy := by
    change n • (_ + _) = 0
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' hx := by
    change n • (-_) = 0
    rw [smul_neg, hx, neg_zero]

/-- Restriction of the actual transfer functor to its `n`-torsion subgroup. -/
def torsionFunctor (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj X := AddCommGrpCat.of (torsionSections P n X.unop)
  map f := AddCommGrpCat.ofHom
    { toFun := fun x => ⟨P.obj.map f x, by
        change n • P.obj.map f x.val = 0
        rw [← map_nsmul, x.property, map_zero]⟩
      map_zero' := by apply Subtype.ext; exact map_zero _
      map_add' := fun x y => by apply Subtype.ext; exact map_add _ _ _ }
  map_id X := by ext x; exact congrArg (fun f => f x.val) (P.obj.map_id X)
  map_comp f g := by ext x; exact congrArg (fun f => f x.val) (P.obj.map_comp f g)

instance (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    (torsionFunctor P n).Additive where
  map_add := by
    intro X Y f g
    ext x
    apply Subtype.ext
    exact congrArg (fun h => h x.val) (P.obj.map_add (f := f) (g := g))

/-- The actual subpresheaf with transfers consisting of sections killed by `n`. -/
def torsionSubpresheaf (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    PresheafWithTransfers.{v} k := AdditiveFunctor.of (torsionFunctor P n)

/-- Inclusion into the original transfer presheaf. -/
def torsionInclusion (P : PresheafWithTransfers.{v} k) (n : ℕ) :
    torsionSubpresheaf P n ⟶ P :=
  ⟨{ app X := AddCommGrpCat.ofHom (torsionSections P n X.unop).subtype
     naturality := by intros; ext; rfl }⟩

/-- The torsion subpresheaf has the asserted uniform exponent. -/
theorem torsionSubpresheaf_nsmul (P : PresheafWithTransfers.{v} k) (n : ℕ)
    (X : Cor k) (x : sections (torsionSubpresheaf P n) X) : n • x = 0 := by
  apply Subtype.ext
  exact x.property

/-- Homotopy invariance restricts to the actual torsion subpresheaf. -/
theorem isA1Invariant_torsionSubpresheaf (P : PresheafWithTransfers.{v} k)
    (hP : IsA1Invariant P) (n : ℕ) : IsA1Invariant (torsionSubpresheaf P n) := by
  intro X
  let Q := (toPresheaf k).obj (torsionSubpresheaf P n)
  let R := (toPresheaf k).obj P
  refine ⟨⟨A1.sectionPullback (.of k) Q X 0, ?_, ?_⟩⟩
  · exact A1.projectionPullback_sectionPullback (.of k) Q X 0
  · ext x
    apply Subtype.ext
    exact congrArg (fun f => f x.val)
      (A1.sectionPullback_projectionPullback (.of k) R hP X 0)

end AlgebraicGeometry.PresheafWithTransfers
