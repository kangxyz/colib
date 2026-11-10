/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.HomologicalComplex.AcyclicKernel

/-! Consumers of the acyclic-kernel quotient theorem, including degree zero. -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

variable {C : Type*} [Category* C] [Abelian C]

-- The nonnegative chain specialization retains its endpoint degree.
example (S : ShortComplex (ChainComplex C ℕ)) (hS : S.ShortExact)
    (hA : ∀ i, IsZero (S.X₁.homology i)) :
    QuasiIsoAt S.g 0 := by
  have h := HomologicalComplex.quasiIso_of_shortExact_isZero_homology S hS hA
  exact (quasiIso_iff S.g).1 h 0

-- Construct the actual quotient by zero, rather than assume the desired result.
example {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex C c) :
    QuasiIso (𝟙 K) := by
  let S : ShortComplex (HomologicalComplex C c) :=
    ShortComplex.mk (0 : (0 : HomologicalComplex C c) ⟶ K) (𝟙 K) (by simp)
  have hS : S.ShortExact :=
    { exact := (S.exact_iff_mono rfl).2 inferInstance
      mono_f := by dsimp [S]; infer_instance
      epi_g := by dsimp [S]; infer_instance }
  have hA : ∀ i, IsZero (S.X₁.homology i) := by
    intro i
    exact (HomologicalComplex.homologyFunctor C c i).map_isZero
      (_root_.CategoryTheory.Limits.isZero_zero _)
  exact HomologicalComplex.quasiIso_of_shortExact_isZero_homology S hS hA
