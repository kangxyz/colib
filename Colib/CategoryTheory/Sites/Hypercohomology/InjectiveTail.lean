/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import Mathlib.Algebra.Homology.ShortComplex.Ab
import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplex

/-!
# Ext vanishing on an exact injective tail

If a cochain complex is exact above degree `a` and its terms from `a` onward
are injective, applying additive Hom out of an object of projective dimension
at most `d` produces an exact complex above `a + d`. Dimension shifting uses
the short exact sequence of consecutive cycles induced by the actual differential.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open Stacks.Cohomology.RightDerivedCoEdge

universe w v u

namespace CochainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

private abbrev cyclesShortComplex (I : CochainComplex A ℤ) (j : ℤ) : ShortComplex A :=
  ShortComplex.mk (I.iCycles (j - 1)) (I.toCycles (j - 1) j)
    (iCycles_comp_toCycles I (j - 1) j)

private theorem shortExact_cyclesShortComplex (I : CochainComplex A ℤ) (j : ℤ)
    (hj : I.ExactAt j) : (cyclesShortComplex I j).ShortExact := by
  have hrel : (ComplexShape.up ℤ).Rel (j - 1) j := by simp
  have hg : Epi (I.toCycles (j - 1) j) :=
    Preadditive.epi_of_isZero_cokernel' _
      (I.homologyIsCokernel (j - 1) j (CochainComplex.prev ℤ j)) hj.isZero_homology
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel _ (cyclesIsKernelToCycles I (j - 1) j hrel))
    inferInstance hg

private theorem subsingleton_ext_cycles_of_exact_tail [HasExt.{w} A]
    (P : A) (I : CochainComplex A ℤ) (d : ℕ) [HasProjectiveDimensionLE P d]
    (a : ℤ) (hinj : ∀ j : ℤ, a ≤ j → Injective (I.X j))
    (hex : ∀ j : ℤ, a < j → I.ExactAt j)
    (m : ℕ) (j : ℤ) (s : ℕ) (hj : a + (m : ℤ) ≤ j) (hs : d < s + m + 1) :
    Subsingleton (Ext.{w} P (I.cycles j) (s + 1)) := by
  induction m generalizing j s with
  | zero =>
      exact HasProjectiveDimensionLT.subsingleton P (d + 1) (s + 1) (by omega) _
  | succ m ih =>
      let S := cyclesShortComplex I j
      have hS : S.ShortExact := shortExact_cyclesShortComplex I j (hex j (by omega))
      have hLeft : Subsingleton (Ext.{w} P S.X₁ (s + 1 + 1)) :=
        ih (j - 1) (s + 1) (by omega) (by omega)
      let : Injective S.X₂ := hinj (j - 1) (by omega)
      have hMid : Subsingleton (Ext.{w} P S.X₂ (s + 1)) :=
        Ext.subsingleton_of_injective P S.X₂ s
      refine subsingleton_of_forall_eq 0 fun z ↦ ?_
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ P hS z rfl (hLeft.elim _ _)
      rw [← hy, hMid.elim y 0, Ext.zero_comp]

/-- A cocycle out of an object of projective dimension at most `d` is a
boundary above `a + d` on a complex with an exact injective tail at `a`. -/
theorem exists_comp_d_eq_of_hasProjectiveDimensionLE
    (P : A) (I : CochainComplex A ℤ) (d : ℕ) [HasProjectiveDimensionLE P d]
    (a : ℤ) (hinj : ∀ j : ℤ, a ≤ j → Injective (I.X j))
    (hex : ∀ j : ℤ, a < j → I.ExactAt j)
    (i : ℤ) (hi : a + (d : ℤ) < i)
    (f : P ⟶ I.X i) (hf : f ≫ I.d i (i + 1) = 0) :
    ∃ g : P ⟶ I.X (i - 1), g ≫ I.d (i - 1) i = f := by
  let := HasExt.standard A
  let S := cyclesShortComplex I i
  have hS : S.ShortExact := shortExact_cyclesShortComplex I i (hex i (by omega))
  have hExt : Subsingleton (Ext.{max u v} P (I.cycles (i - 1)) 1) :=
    subsingleton_ext_cycles_of_exact_tail P I d a hinj hex d (i - 1) 0 (by omega) (by omega)
  let z := I.liftCycles f (i + 1) (CochainComplex.next ℤ i) hf
  obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ P hS (Ext.mk₀ z) (zero_add 1)
    (hExt.elim _ _)
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective P S.X₂).2 x
  have hg : g ≫ I.toCycles (i - 1) i = z :=
    (Ext.mk₀_bijective P (I.cycles i)).1 (by simpa only [Ext.mk₀_comp_mk₀] using hx)
  refine ⟨g, ?_⟩
  rw [← I.toCycles_i (i - 1) i, ← Category.assoc, hg]
  exact I.liftCycles_i f _ _ hf

/-- Additive Hom out of an object of finite projective dimension has zero
cohomology above the corresponding bound on an exact injective tail. -/
theorem isZero_homology_preadditiveCoyoneda_of_exact_tail
    (P : A) (I : CochainComplex A ℤ) (d : ℕ) [HasProjectiveDimensionLE P d]
    (a : ℤ) (hinj : ∀ j : ℤ, a ≤ j → Injective (I.X j))
    (hex : ∀ j : ℤ, a < j → I.ExactAt j) (i : ℤ) (hi : a + (d : ℤ) < i) :
    IsZero ((((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex
      (.up ℤ)).obj I).homology i) := by
  let L := ((preadditiveCoyoneda.obj (op P)).mapHomologicalComplex (.up ℤ)).obj I
  apply (L.exactAt_iff_isZero_homology i).mp
  rw [HomologicalComplex.exactAt_iff, ShortComplex.ab_exact_iff]
  intro f hf
  change f ≫ I.d i ((ComplexShape.up ℤ).next i) = 0 at hf
  rw [CochainComplex.next ℤ i] at hf
  change ∃ g : P ⟶ I.X ((ComplexShape.up ℤ).prev i),
    g ≫ I.d ((ComplexShape.up ℤ).prev i) i = f
  rw [CochainComplex.prev ℤ i]
  exact exists_comp_d_eq_of_hasProjectiveDimensionLE P I d a hinj hex i hi f hf

end CochainComplex
