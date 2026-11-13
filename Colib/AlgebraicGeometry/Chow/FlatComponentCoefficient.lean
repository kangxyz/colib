/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatProduct
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.StalkBridge.Basic
public import StacksFrontier.RingTheory.Length.FlatLocalHom
public import StacksFrontier.Topology.Sober.Generization

/-!
# Original generic weights under an actual flat scheme morphism

At a generic point upstairs, flatness sends its image to an original generic
point downstairs. The actual local flat length formula factors the upstairs
self-length into the original generic self-length and the actual comap-component
quotient length. Every other component contributes zero. The original stalk map,
comap ideal and full nonreduced component inverse image are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators TensorProduct

universe u

namespace Stacks.Chow

variable {D E : Scheme.{u}}

/-- The reduced closure of a point cuts out its residue field in its actual stalk. -/
theorem stalk_integralComponentAt_self (z : D) :
    IdealSheafData.stalk (integralComponentAt z) z =
      IsLocalRing.maximalIdeal (D.presheaf.stalk z) := by
  have := isIntegral_integralComponentAt z
  let Z := (integralComponentAt z).subscheme
  have h := Stacks.AlgebraicGeometry.Tag01YEStalkBridge.ker_stalkMap_eq_maximalIdeal
    (integralComponentAt z).subschemeι (genericPoint Z) (genericPoint_spec Z)
  rw [ker_stalkMap_eq_idealStalk_ker, Scheme.IdealSheafData.ker_subschemeι] at h
  have hz : (integralComponentAt z).subschemeι (genericPoint Z) = z := by
    simpa only [genericPointOf, Z] using genericPointOf_integralComponentAt z
  let P : D → Prop := fun x => IdealSheafData.stalk (integralComponentAt z) x =
    IsLocalRing.maximalIdeal (D.presheaf.stalk x)
  exact Eq.mp (congrArg P hz) h

/-- Actual generic self-length after flat base change, with its actual component ideal. -/
theorem length_stalk_self_eq_mul_comap_component
    (f : E ⟶ D) [Flat f] (x : E) :
    Module.length (E.presheaf.stalk x) (E.presheaf.stalk x) =
      Module.length (D.presheaf.stalk (f x)) (D.presheaf.stalk (f x)) *
        Module.length (E.presheaf.stalk x)
          (E.presheaf.stalk x ⧸ IdealSheafData.stalk ((integralComponentAt (f x)).comap f) x) := by
  let A := D.presheaf.stalk (f x)
  let B := E.presheaf.stalk x
  let : Algebra A B := (f.stalkMap x).hom.toAlgebra
  have : IsLocalHom (algebraMap A B) := LocallyRingedSpace.isLocalHomStalkMap f.toLRSHom x
  have : Module.Flat A B := Flat.stalkMap f x
  have h := length_baseChange_eq_length_mul_length_quotient A B A
  rw [(TensorProduct.AlgebraTensorModule.rid A B B).length_eq] at h
  rw [IdealSheafData.stalk_comap, stalk_integralComponentAt_self]
  exact h.symm

variable [IsNoetherian D] [IsNoetherian E] (f : E ⟶ D) [Flat f]

omit [AlgebraicGeometry.IsNoetherian D] [Flat f] in
/-- A full pulled component has its exact ambient quotient coefficient over a
generic point of the whole pullback. -/
theorem finiteCyclePushforward_comap_fundamentalCycle_apply_generic
    (I : D.IdealSheafData) (x : genericPoints E) :
    letI := Scheme.isNoetherian_of_finiteType_of_isNoetherian (I.comap f).subschemeι
    finiteCyclePushforward (I.comap f).subschemeι
      (AlgebraicCycle.fundamentalCycle (I.comap f).subscheme) x.val =
        ((Module.length (E.presheaf.stalk x.val)
          (E.presheaf.stalk x.val ⧸ IdealSheafData.stalk (I.comap f) x.val)).toNat : ℤ) := by
  have := Scheme.isNoetherian_of_finiteType_of_isNoetherian (I.comap f).subschemeι
  calc
    _ = ((closedImmersionQuotientStalkLength (I.comap f).subschemeι x.val).toNat : ℤ) :=
      finiteCyclePushforward_fundamentalCycle_apply_eq_quotientStalkLength
        (𝟙 E) (I.comap f).subschemeι x.val x.property
    _ = _ := by
      unfold closedImmersionQuotientStalkLength
      rw [Scheme.IdealSheafData.ker_subschemeι]

omit [AlgebraicGeometry.IsNoetherian D] in
/-- Actual flat pullback generic coefficients assemble with all original weights. -/
theorem fundamentalCycle_apply_eq_sum_flat_components [Fintype (genericPoints D)]
    (x : genericPoints E) :
    letI : ∀ z : genericPoints D, IsNoetherian ((integralComponentAt z.val).comap f).subscheme :=
      fun z =>
        Scheme.isNoetherian_of_finiteType_of_isNoetherian
          ((integralComponentAt z.val).comap f).subschemeι
    AlgebraicCycle.fundamentalCycle E x.val =
      ∑ z : genericPoints D,
        ((Module.length (D.presheaf.stalk z.val) (D.presheaf.stalk z.val)).toNat : ℤ) *
          finiteCyclePushforward ((integralComponentAt z.val).comap f).subschemeι
            (AlgebraicCycle.fundamentalCycle
              ((integralComponentAt z.val).comap f).subscheme) x.val := by
  classical
  let : ∀ z : genericPoints D, IsNoetherian ((integralComponentAt z.val).comap f).subscheme :=
    fun z =>
      Scheme.isNoetherian_of_finiteType_of_isNoetherian
        ((integralComponentAt z.val).comap f).subschemeι
  let z₀ : genericPoints D := ⟨f x.val, mem_genericPoints_of_flat f x.property⟩
  rw [Finset.sum_eq_single z₀]
  · rw [finiteCyclePushforward_comap_fundamentalCycle_apply_generic,
      AlgebraicCycle.fundamentalCycle_apply_generic]
    have h := congrArg (fun l : ℕ∞ => (l.toNat : ℤ))
      (length_stalk_self_eq_mul_comap_component f x.val)
    simpa only [ENat.toNat_mul, Nat.cast_mul] using h
  · intro z hz hne
    have hnot : f x.val ∉ closure ({z.val} : Set D) := by
      intro hmem
      apply hne
      exact Subtype.ext (forall_specializes_eq_of_mem_genericPoints z₀.property z.val
        (specializes_iff_mem_closure.mpr hmem))
    have hnot' : x.val ∉ Set.range ((integralComponentAt z.val).comap f).subschemeι := by
      simpa only [Scheme.IdealSheafData.range_subschemeι,
        Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
        Set.mem_preimage, coe_support_integralComponentAt] using hnot
    rw [finiteCyclePushforward_fundamentalCycle_eq_zero_of_notMem_range _ _ hnot', mul_zero]
  · intro hz
    exact (hz (Finset.mem_univ z₀)).elim

end Stacks.Chow
