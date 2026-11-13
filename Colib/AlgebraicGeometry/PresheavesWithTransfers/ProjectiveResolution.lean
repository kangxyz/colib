/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution.BoundedAbove

/-!
# Projective representatives of bounded-above transfer complexes

The original derived category of transfer presheaves has bounded-above
projective representatives by the Stacks projective resolution theorem.
The same representative is K-projective in the native homotopy category.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]
variable [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

/-- The actual bounded-above derived object has a native projective representative. -/
theorem exists_projectiveRepresentative
    (K : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) :
    ∃ (P : CochainComplex (PresheafWithTransfers.{u + 1} k) ℤ) (n : ℤ),
      P.IsStrictlyLE n ∧ (∀ i : ℤ, Projective (P.X i)) ∧ P.IsKProjective ∧
        Nonempty (DerivedCategory.Q.obj P ≅ K.obj) := by
  obtain ⟨n, hn⟩ := K.property
  let : K.obj.IsLE n := hn
  obtain ⟨L, hL, ⟨e⟩⟩ := K.obj.exists_iso_Q_obj_of_isLE n
  obtain ⟨P, _⟩ := ProjectiveResolutionLemma.statement3 n L hL
  let : P.complex.IsStrictlyLE n := P.boundedAbove
  let : ∀ i : ℤ, Projective (P.complex.X i) := P.projective
  let : QuasiIso P.α := P.quasiIso
  exact ⟨P.complex, n, P.boundedAbove, P.projective,
    CochainComplex.isKProjective_of_projective P.complex n,
    ⟨asIso (DerivedCategory.Q.map P.α) ≪≫ e.symm⟩⟩

end AlgebraicGeometry.PresheafWithTransfers
