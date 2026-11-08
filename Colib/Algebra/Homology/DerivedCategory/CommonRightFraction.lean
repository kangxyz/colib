/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-!
# A common complex representative for two outgoing derived morphisms

Two morphisms from the same represented derived object can be represented by actual chain maps
from a common quasi-isomorphic replacement. This only changes the common source; the two target
complexes remain fixed.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace DerivedCategory

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- Two outgoing derived morphisms admit chain-map representatives with a common
quasi-isomorphic source. -/
theorem exists_common_right_fraction {R K E : CochainComplex C ℤ}
    (s : Q.obj R ⟶ Q.obj K) (t : Q.obj R ⟶ Q.obj E) :
    ∃ (R' : CochainComplex C ℤ) (r : R' ⟶ R) (q : R' ⟶ K) (a : R' ⟶ E),
      QuasiIso r ∧ Q.map r ≫ s = Q.map q ∧ Q.map r ≫ t = Q.map a := by
  obtain ⟨R₁, r₁, hr₁, q₁, hs⟩ := right_fac s
  obtain ⟨R₂, r₂, hr₂, a, ht⟩ := right_fac (Q.map r₁ ≫ t)
  have hr₁' : QuasiIso r₁ := (isIso_Q_map_iff_quasiIso C r₁).1 hr₁
  have hr₂' : QuasiIso r₂ := (isIso_Q_map_iff_quasiIso C r₂).1 hr₂
  refine ⟨R₂, r₂ ≫ r₁, r₂ ≫ q₁, a, inferInstance, ?_, ?_⟩
  · simp [Functor.map_comp, hs]
  · rw [Functor.map_comp, Category.assoc, ht, IsIso.hom_inv_id_assoc]

end DerivedCategory
