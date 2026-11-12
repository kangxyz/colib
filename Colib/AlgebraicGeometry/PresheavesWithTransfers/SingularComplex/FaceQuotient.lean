/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.Presheaf
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.YonedaLarge
public import Colib.AlgebraicTopology.DoldKan.NormalizedRepresentatives
import Mathlib.Algebra.Category.Grp.Colimits

/-!
# Representable quotients by algebraic simplex faces

Take the cokernel of the sum of the genuine coface maps of transfer
representables. Its morphisms into a coefficient presheaf are the normalized
cycles of the evaluated singular simplicial abelian group.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open AlgebraicTopology.NormalizedMooreComplex

variable (k : Type u) [Field k] (U : Cor k)

local notation "R(" n ")" => Functor.obj (representableLarge k) (Cor.simplexProduct U n)
set_option quotPrecheck false in
local notation "δ(" n "," i ")" =>
  (show Cor.simplexProduct U n ⟶ Cor.simplexProduct U (n + 1) from
    (Cor.simplexProductCosimplicial U).δ i)
set_option quotPrecheck false in
local notation "S(" P₁ ")" => (Cor.simplexProductCosimplicial U).op ⋙ (P₁).obj

/-- The representables indexed by the actual faces of the next simplex. -/
abbrev singularFaceRepresentables (n : ℕ) : Fin (n + 2) → PresheafWithTransfers.{u + 1} k :=
  fun _ => R(n)

local instance (n : ℕ) : HasCoproduct (singularFaceRepresentables k U n) := by
  let : HasColimitsOfShape (Discrete (Fin (n + 2))) AddCommGrpCat.{u + 1} :=
    AddCommGrpCat.hasColimitsOfShape
  exact (hasColimitsOfShape_of_closedUnderColimits (Discrete (Fin (n + 2)))
    (additiveFunctor (Cor k)ᵒᵖ AddCommGrpCat.{u + 1})).has_colimit _

/-- The coproduct map whose components are the actual finite correspondence cofaces. -/
def singularFaceBoundaryMap (n : ℕ) :
    (∐ singularFaceRepresentables k U n) ⟶ R(n + 1) :=
  Sigma.desc (fun i => (representableLarge k).map (δ(n,i)))

/-- The component of the boundary map is the original corresponding coface. -/
theorem singularFaceBoundaryMap_ι (n : ℕ) (i : Fin (n + 2)) :
    Sigma.ι (singularFaceRepresentables k U n) i ≫ singularFaceBoundaryMap k U n =
      (representableLarge k).map (δ(n,i)) :=
  Sigma.ι_comp_desc (C := (PresheafWithTransfers.{u + 1} k)) (f := singularFaceRepresentables k U n)
    (fun j => (representableLarge k).map (δ(n,j))) i

/-- Quotient the representing simplex by the images of all its actual faces. -/
def singularFaceQuotient (n : ℕ) : PresheafWithTransfers.{u + 1} k :=
  match n with
  | .zero => R(0)
  | .succ m => cokernel (singularFaceBoundaryMap k U m)

/-- Each actual coface vanishes in the quotient. -/
theorem singularFaceBoundaryMap_component_comp_π (n : ℕ) (i : Fin (n + 2)) :
    (representableLarge k).map (δ(n,i)) ≫
      cokernel.π (C := (PresheafWithTransfers.{u + 1} k)) (singularFaceBoundaryMap k U n) = 0 := by
  rw [← singularFaceBoundaryMap_ι k U, Category.assoc, cokernel.condition, comp_zero]

/-- A map from the quotient is the section at the lifted full diagonal, and
its cycle condition is vanishing on every original coface. -/
@[colib_ref "Voevodsky2010Cancellation" "Corollary 4.9, p. 684"
  "ingredient" "Maps from the actual transfer quotient by simplex faces"]
def singularFaceQuotientHomEquiv (P : PresheafWithTransfers.{u + 1} k) (n : ℕ) :
    (singularFaceQuotient k U n ⟶ P) ≃
      {s : sections P (Cor.simplexProduct U n) // IsCycle (S(P)) n s} := by
  rcases n with _ | n
  · change (R(0) ⟶ P) ≃ _
    exact
      { toFun := fun f => ⟨yonedaLargeAddEquiv P _ f, trivial⟩
        invFun := fun s => (yonedaLargeAddEquiv P _).symm s.val
        left_inv := fun f => (yonedaLargeAddEquiv P _).symm_apply_apply f
        right_inv := fun s => Subtype.ext ((yonedaLargeAddEquiv P _).apply_symm_apply s.val) }
  let d := singularFaceBoundaryMap k U n
  let e := yonedaLargeAddEquiv P (Cor.simplexProduct U (n + 1))
  change (cokernel d ⟶ P) ≃ _
  refine
    { toFun := fun f => ⟨e (cokernel.π d ≫ f), ?_⟩
      invFun := fun s => cokernel.desc d (e.symm s.val) ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro i
    change transfer P (δ(n,i)) (e (cokernel.π d ≫ f)) = 0
    calc
      transfer P (δ(n,i)) (e (cokernel.π d ≫ f)) =
          yonedaLargeAddEquiv P (Cor.simplexProduct U n)
            ((representableLarge k).map (δ(n,i)) ≫ cokernel.π d ≫ f) :=
        (yonedaLargeAddEquiv_naturality_left P (δ(n,i)) (cokernel.π d ≫ f)).symm
      _ = 0 := by
        have h := singularFaceBoundaryMap_component_comp_π k U n i
        change (representableLarge k).map (δ(n,i)) ≫ cokernel.π d = 0 at h
        rw [← Category.assoc, h, zero_comp, map_zero]
  · apply Sigma.hom_ext
    intro i
    have hi : Sigma.ι (singularFaceRepresentables k U n) i ≫ d =
        (representableLarge k).map (δ(n,i)) := singularFaceBoundaryMap_ι k U n i
    rw [← Category.assoc, hi, comp_zero]
    let e' := yonedaLargeAddEquiv P (Cor.simplexProduct U n)
    apply e'.injective
    calc
      _ = transfer P (δ(n,i)) (e (e.symm s.val)) :=
        yonedaLargeAddEquiv_naturality_left P (δ(n,i)) (e.symm s.val)
      _ = transfer P (δ(n,i)) s.val := congrArg (transfer P (δ(n,i))) (e.apply_symm_apply s.val)
      _ = 0 := s.property i
      _ = e' 0 := (map_zero e').symm
  · intro f
    apply (cancel_epi (cokernel.π d)).mp
    simp only [cokernel.π_desc, e.symm_apply_apply]
  · intro s
    apply Subtype.ext
    simp only [cokernel.π_desc, e.apply_symm_apply]

end AlgebraicGeometry.PresheafWithTransfers
