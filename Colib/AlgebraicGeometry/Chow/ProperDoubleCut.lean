/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Intersection.AffineLineFiber
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.FlatCodimensionZero
import StacksFrontier.Topology.Sober.Generization

/-!
# Properness of a principal cut and a source face

If every component of the first cut dominates a component of the source,
then none is contained in an affine coordinate face. For regular scalars
in the original stalk, Krull's principal ideal theorem gives the same
avoidance with the two cuts interchanged.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Ideal

/-- Properness on the minimal components is symmetric for two principal
cuts by nonzerodivisors in a Noetherian ring. -/
theorem notMem_minimalPrimes_span_singleton_symm {R : Type u} [CommRing R]
    [IsNoetherianRing R] {s t : R} (hs : s ∈ nonZeroDivisors R)
    (ht : ∀ q : PrimeSpectrum R, q.asIdeal ∈ (Ideal.span {s}).minimalPrimes → t ∉ q.asIdeal)
    (q : PrimeSpectrum R) (hq : q.asIdeal ∈ (Ideal.span {t}).minimalPrimes) :
    s ∉ q.asIdeal := by
  intro hsq
  have hp : q.asIdeal.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq
  have hq' : q.asIdeal ∈ (Ideal.span {s}).minimalPrimes :=
    Ideal.mem_minimalPrimes_of_height_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsq))
      (hp.trans (Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hs))
  exact ht q hq' (hq.1.2 (Ideal.subset_span (Set.mem_singleton t)))

end Ideal

namespace AlgebraicGeometry.Scheme.AffineLineFiber

open Stacks.Chow

variable {k : Type u} [Field k] {P Y : Scheme.{u}}

private theorem point_notMem_genericPoints (a : k) (z : Spec (.of k)) :
    point a z ∉ genericPoints (Spec (.of (Polynomial k)) : Scheme) := by
  intro h
  have hspec : (⊥ : PrimeSpectrum (Polynomial k)) ⤳ point a z :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  have he : (⊥ : PrimeSpectrum (Polynomial k)) = point a z :=
    forall_specializes_eq_of_mem_genericPoints h _ hspec
  have hm : Polynomial.X - Polynomial.C a ∈ (point a z).asIdeal := by
    change Polynomial.evalRingHom a (Polynomial.X - Polynomial.C a) ∈ z.asIdeal
    simp
  rw [← he] at hm
  exact Polynomial.X_sub_C_ne_zero a (Ideal.mem_bot.mp hm)

private theorem support_ker_eq_range {A B : Scheme.{u}} (i : A ⟶ B) [IsClosedImmersion i] :
    (i.ker.support : Set B) = Set.range i := by
  rw [Scheme.Hom.support_ker, i.isClosedEmbedding.isClosed_range.closure_eq]

/-- The coordinate face equation avoids every minimal prime of the closed
cut when the cut components have generic images in the original source. -/
theorem scalar_notMem_minimalPrimes_of_cut_genericImage
    (p : P ⟶ Y) (q : Y ⟶ Spec (.of (Polynomial k))) [Flat q] (a : k)
    (g : P ⟶ Spec (.of (Polynomial k))) (b : k)
    (hgen : ∀ y : genericPoints (fiber g b),
      p (inclusion g b y.val) ∈ genericPoints Y)
    (x : P) (r : PrimeSpectrum (P.presheaf.stalk x))
    (hr : r.asIdeal ∈ (Ideal.span {scalar g b x}).minimalPrimes) :
    scalar (p ≫ q) a x ∉ r.asIdeal := by
  intro hs
  let j := inclusion g b
  let i := inclusion (p ≫ q) a
  let η := P.fromSpecStalk x r
  have hr' : r.asIdeal ∈ (IdealSheafData.stalk j.ker x).minimalPrimes := by
    rw [show j = inclusion g b from rfl, inclusion_stalk]
    exact hr
  have hη : η ∈ componentGenericPointsThrough j.ker x :=
    (fromSpecStalk_mem_componentGenericPointsThrough_iff j.ker x r).mpr hr'
  obtain ⟨y, hy⟩ : η ∈ Set.range j := (support_ker_eq_range j) ▸ hη.1
  have hygen : y ∈ genericPoints (fiber g b) := by
    apply mem_genericPoints_of_forall_specializes_eq
    intro w hw
    have hw' : j w ∈ (j.ker.support : Set P) := (support_ker_eq_range j).symm ▸ ⟨w, rfl⟩
    have hwy : j w ⤳ η := hy ▸ hw.map j.continuous
    exact j.isClosedEmbedding.injective ((hη.2.2 _ hw' hwy).trans hy.symm)
  have hfg : (p ≫ q) η ∈ genericPoints (Spec (.of (Polynomial k)) : Scheme) := by
    rw [← hy]
    exact mem_genericPoints_of_flat q (hgen ⟨y, hygen⟩)
  have hle : IdealSheafData.stalk i.ker x ≤ r.asIdeal := by
    rw [show i = inclusion (p ≫ q) a from rfl, inclusion_stalk]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hs)
  have hi : η ∈ (i.ker.support : Set P) :=
    (le_iff_fromSpecStalk_mem_support i.ker x r).mp hle
  obtain ⟨z, hz⟩ : η ∈ Set.range i := (support_ker_eq_range i) ▸ hi
  have he : (p ≫ q) η = point a (pullback.fst (point a) (p ≫ q) z) := by
    rw [← hz]
    exact (congrArg (fun m : fiber (p ≫ q) a ⟶ Spec (.of (Polynomial k)) => m z)
      (pullback.condition (f := point a) (g := p ≫ q))).symm
  rw [he] at hfg
  exact point_notMem_genericPoints a _ hfg

end AlgebraicGeometry.Scheme.AffineLineFiber
