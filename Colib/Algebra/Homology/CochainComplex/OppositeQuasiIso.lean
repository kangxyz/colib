/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # Quasi-isomorphisms under the native opposite cochain equivalence

Degree reversal preserves the actual short complexes computing homology. Together
with Mathlib's opposite homology comparison this proves preservation and reflection
of quasi-isomorphisms by `CochainComplex.opEquivalence`, on its literal chain maps.

Implementation provenance: the compatibility statements replace
`Quillen/Aglib/Algebra/Homology/CochainComplex/OppositeQuasiIsoCompatibility.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite HomologicalComplex
universe u v

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {K L : HomologicalComplex C c'} (f : K ⟶ L)
  (e : c.Embedding c') [e.IsRelIff]

/-- Restriction preserves homology equivalences at every degree whose neighbors
are retained by the embedding. The short-complex map is unchanged. -/
lemma quasiIsoAt_restrictionMap_iff (j : ι)
    (hp : c'.prev (e.f j) = e.f (c.prev j))
    (hn : c'.next (e.f j) = e.f (c.next j)) :
    QuasiIsoAt (restrictionMap f e) j ↔ QuasiIsoAt f (e.f j) := by
  rw [quasiIsoAt_iff,
    quasiIsoAt_iff' f (e.f (c.prev j)) (e.f j) (e.f (c.next j)) hp hn]
  rfl

end HomologicalComplex

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The native opposite cochain equivalence preserves quasi-isomorphisms. -/
lemma quasiIso_cochain_opEquivalence_functor_map {K L : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((opEquivalence C).functor.map f.op) := by
  change QuasiIso (restrictionMap ((HomologicalComplex.opFunctor C (.up ℤ)).map f.op)
    ComplexShape.embeddingUpIntDownInt)
  constructor
  intro j
  apply (quasiIsoAt_restrictionMap_iff (c' := .down ℤ) _ _ j
    (by simp; omega) (by simp; omega)).2
  infer_instance

/-- The inverse native opposite equivalence preserves quasi-isomorphisms. -/
lemma quasiIso_cochain_opEquivalence_inverse_map {K L : CochainComplex Cᵒᵖ ℤ}
    (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((opEquivalence C).inverse.map f).unop := by
  have h : QuasiIso (restrictionMap f ComplexShape.embeddingDownIntUpInt) := by
    constructor
    intro j
    apply (quasiIsoAt_restrictionMap_iff _ _ j (by simp; omega) (by simp; omega)).2
    infer_instance
  exact (quasiIso_unopFunctor_map_iff
    (restrictionMap f ComplexShape.embeddingDownIntUpInt)).2 h

/-- Reflection uses the actual unit of the native degree-reversing equivalence. -/
lemma quasiIso_cochain_opEquivalence_functor_map_iff {K L : CochainComplex C ℤ}
    (f : K ⟶ L) : QuasiIso ((opEquivalence C).functor.map f.op) ↔ QuasiIso f := by
  constructor
  · intro h
    let := h
    have := quasiIso_cochain_opEquivalence_inverse_map ((opEquivalence C).functor.map f.op)
    let e := opEquivalence C
    have he : f = (e.unitIso.app (op K)).inv.unop ≫
        (e.inverse.map (e.functor.map f.op)).unop ≫ (e.unitIso.app (op L)).hom.unop := by
      apply Quiver.Hom.op_inj
      simp only [op_comp, Quiver.Hom.op_unop, Category.assoc]
      change f.op = e.unitIso.hom.app (op L) ≫
        (e.functor ⋙ e.inverse).map f.op ≫ e.unitIso.inv.app (op K)
      rw [← e.unitIso.hom.naturality_assoc]
      simp
    rw [he]
    infer_instance
  · intro h
    let := h
    exact quasiIso_cochain_opEquivalence_functor_map f

end CochainComplex
