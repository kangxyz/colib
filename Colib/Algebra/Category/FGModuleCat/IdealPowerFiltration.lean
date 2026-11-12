/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.Algebra.Category.FGModuleCat.IdealClosedSupport
public import Colib.CategoryTheory.ExactCategory.Filtration.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.ShortExact

/-!
# Actual ideal-power filtrations of finite modules

The recursive filtration uses the actual submodule I M and its quotient.
Every step lowers an annihilating ideal-power exponent. Hence the displayed
finite filtration consists of actual submodules, with I-annihilated factors.
-/
@[expose] public section

open CategoryTheory.ExactCategory
open FGModuleCat.IdealSupport


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat.IdealSupport
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R)

/-- The actual first ideal-power submodule. -/
def idealProduct (M : FGModuleCat.{u} R) : Submodule R M := I • ⊤

/-- The genuine finite ideal-product module. -/
def idealProductModule (M : FGModuleCat.{u} R) : FGModuleCat.{u} R :=
  FGModuleCat.of R (idealProduct I M)

/-- Its genuine finite quotient. -/
def idealQuotientModule (M : FGModuleCat.{u} R) : FGModuleCat.{u} R :=
  FGModuleCat.of R (M ⧸ idealProduct I M)

/-- The actual short complex I M → M → M/I M. -/
def idealProductSequence (M : FGModuleCat.{u} R) : ShortComplex (FGModuleCat.{u} R) :=
  ShortComplex.mk (FGModuleCat.ofHom (idealProduct I M).subtype)
    (FGModuleCat.ofHom (idealProduct I M).mkQ) (by
      ext x
      change (idealProduct I M).mkQ x.val = 0
      exact (Submodule.Quotient.mk_eq_zero (idealProduct I M)).mpr x.property)

/-- The sequence of actual ideal-product and quotient modules is short exact. -/
theorem idealProductSequence_shortExact (M : FGModuleCat.{u} R) :
    (idealProductSequence I M).ShortExact := by
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (forget₂ (FGModuleCat R) (ModuleCat R))
  exact ModuleCat.shortComplex_shortExact _ (LinearMap.exact_subtype_mkQ _)
    (idealProduct I M).subtype_injective (idealProduct I M).mkQ_surjective

omit [IsNoetherianRing R] in
/-- The quotient by I M is genuinely annihilated by I. -/
theorem idealQuotientModule_killed (M : FGModuleCat.{u} R) :
    killedBy I (idealQuotientModule I M) := by
  intro r hr m
  obtain ⟨x, rfl⟩ := (idealProduct I M).mkQ_surjective m
  change (idealProduct I M).mkQ (r • x) = 0
  exact (Submodule.Quotient.mk_eq_zero (idealProduct I M)).mpr
    (Submodule.smul_mem_smul hr (Submodule.mem_top))

/-- Passing to I M lowers the exponent of a genuine annihilating ideal power. -/
theorem idealProductModule_power_annihilator (M : FGModuleCat.{u} R) (n : ℕ)
    (h : I ^ (n + 1) ≤ Module.annihilator R M) :
    I ^ n ≤ Module.annihilator R (idealProductModule I M) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  apply Subtype.ext
  change r • x.val = 0
  refine Submodule.smul_induction_on x.property (fun a ha m _ ↦ ?_)
    (fun m m' hm hm' ↦ by simp [smul_add, hm, hm'])
  rw [smul_smul]
  apply Module.mem_annihilator.mp (h ?_) m
  rw [pow_succ]
  exact Ideal.mul_mem_mul hr ha

/-- If a finite module is killed by I^n, its actual ideal-power tower gives
a finite categorical filtration by modules killed by I. -/
theorem idealPowerFiltration (M : FGModuleCat.{u} R) (n : ℕ)
    (h : I ^ n ≤ Module.annihilator R M) :
    Nonempty ((abelianExactStructure (FGModuleCat.{u} R)).Filtration (killedBy I) M) := by
  induction n generalizing M with
  | zero =>
    refine ⟨.zero ?_⟩
    rw [IsZero.iff_id_eq_zero]
    ext m
    have h1 : (1 : R) ∈ Module.annihilator R M := h (by simp)
    simpa using Module.mem_annihilator.mp h1 m
  | succ n ih =>
    obtain ⟨F⟩ := ih (idealProductModule I M) (idealProductModule_power_annihilator I M n h)
    exact ⟨.step (idealProductSequence I M) (idealProductSequence_shortExact I M) F
      (idealQuotientModule_killed I M)⟩

end FGModuleCat.IdealSupport
