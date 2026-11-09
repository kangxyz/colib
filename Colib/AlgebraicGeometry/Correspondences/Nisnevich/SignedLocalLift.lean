/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Nisnevich.LocalGeneratorLift
public import Mathlib.Data.Fintype.EquivFin

/-!
# Pointed Nisnevich lifting of native signed finite correspondences

The native finite-support decomposition expresses the original correspondence
as the sum of its actual point cycles with their integer coefficients. Lift each
signed prime on a pointed smooth Nisnevich neighborhood, take one common pointed
refinement of this finite family, and add their actual graph restrictions there.
The genuine graph functor and the existing preadditive category give the desired
factorization. No new presentation of cycles or caller-supplied factorization law
is used. Negative coefficients and cancellation are preserved.

For the zero correspondence the actual support index is empty. The existing
common-refinement theorem allows the empty family, so no artificial nonempty
support or nonzero coefficient premise is introduced.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Nisnevich/SignedLocalLift.lean`,
blob `f9457d0f0d7a9a0902f4ad6797394f5d83d63a32`. The original `Finsupp` induction
is replaced by the existing native signed-single decomposition and one finite
common refinement. Actual Tor coefficients and residue degrees are inherited
unchanged from the native prime-lifting theorem.

Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Chow
open Function.locallyFinsuppWithin
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]
  {X Y V : Scheme.SmoothSite (Spec (.of k))}

/-- Every native signed finite correspondence lifts through a single Nisnevich
covering arrow after a genuine pointed smooth-site Nisnevich neighborhood. -/
@[colib_ref "motivic_source_a6805c4"
  "Correspondences/Nisnevich/SignedLocalLift.lean: exists_nisnevich_graph_factorization"
  "adaptation" "native signed finite-support decomposition and actual finite common refinement"]
theorem exists_nisnevich_graph_factorization
    (α : Cor.mk X ⟶ Cor.mk Y) (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v)) (x : X.left) :
    ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (graphFunctor k).map q = (graphFunctor k).map g ≫ α := by
  classical
  let I : Type u := ↥(α.property.1.toFinset)
  have hadm (i : I) : IsFiniteCorrespondencePoint X.hom Y.hom i.val :=
    α.property.2 i.val (by
      simpa only [Set.Finite.mem_toFinset, support, Function.mem_support] using i.property)
  let c (i : I) : Cor.mk X ⟶ Cor.mk Y :=
    singleFiniteCorrespondence X.hom Y.hom i.val (hadm i) (α.val i.val)
  have hsum : ∑ i : I, c i = α :=
    (finiteCorrespondence_eq_sum_signedSingles X.hom Y.hom α).symm
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hα : ∑ i : Fin (Fintype.card I), c (e i) = α :=
    (Equiv.sum_comp e c).trans hsum
  have hlocal (i : Fin (Fintype.card I)) :
      ∃ (U : Scheme.SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
      ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      ∃ β : Cor.mk U ⟶ Cor.mk V,
        β ≫ (graphFunctor k).map q = (graphFunctor k).map g ≫ c (e i) :=
    exists_nisnevich_graph_factorization_single_signed k (e i).val (hadm (e i))
      q hq x (α.val (e i).val)
  choose U g hg u hu hr β hβ using hlocal
  obtain ⟨W, h, hh, w, hw, hwr, a, ha, _⟩ :=
    Scheme.SmoothSite.exists_common_nisnevich_refinement X x (Fintype.card I)
      U g hg u hu hr
  let δ : Cor.mk V ⟶ Cor.mk Y := (graphFunctor k).map q
  let γ : Cor.mk W ⟶ Cor.mk X := (graphFunctor k).map h
  let ρ (i : Fin (Fintype.card I)) : Cor.mk W ⟶ Cor.mk (U i) :=
    (graphFunctor k).map (a i)
  let σ (i : Fin (Fintype.card I)) : Cor.mk (U i) ⟶ Cor.mk X :=
    (graphFunctor k).map (g i)
  have hβ' (i : Fin (Fintype.card I)) : β i ≫ δ = σ i ≫ c (e i) := hβ i
  have hmap (i : Fin (Fintype.card I)) : ρ i ≫ σ i = γ :=
    ((graphFunctor k).map_comp (a i) (g i)).symm.trans
      (congrArg (fun f : W ⟶ X => (graphFunctor k).map f) (ha i))
  refine ⟨W, h, hh, w, hw, hwr, ∑ i : Fin (Fintype.card I), ρ i ≫ β i, ?_⟩
  change (∑ i : Fin (Fintype.card I), ρ i ≫ β i) ≫ δ = γ ≫ α
  calc
    (∑ i : Fin (Fintype.card I), ρ i ≫ β i) ≫ δ =
      ∑ i : Fin (Fintype.card I), γ ≫ c (e i) := by
        rw [Preadditive.sum_comp]
        apply Finset.sum_congr rfl
        intro i _
        rw [Category.assoc, hβ' i, ← Category.assoc, hmap i]
    _ = γ ≫ ∑ i : Fin (Fintype.card I), c (e i) := by
      rw [Preadditive.comp_sum]
    _ = γ ≫ α := by rw [hα]

end AlgebraicGeometry.Cor
