/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalComparison
import Colib.AlgebraicGeometry.PresheavesWithTransfers.SingularComplex.TotalExact
import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
import Mathlib.Algebra.Homology.Embedding.AreComplementary
import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso

/-!
# Singular totalization of a bounded-above complex with invariant cohomology

First compare the augmentation of a bounded complex using its cohomology
objects. For a general bounded-above complex the three adjacent
antidiagonals retain a finite range of coefficient degrees.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex₂
open StacksDraft.TotalComplexQuasiIso

universe u v

namespace AlgebraicGeometry.PresheafWithTransfers

variable {k : Type u} [Field k]

local notation "c" => ComplexShape.up ℤ

private theorem singularTotalUnit_quasiIso_middle
    (S : ShortComplex (CochainComplex (PresheafWithTransfers.{v} k) ℤ))
    (hS : S.ShortExact)
    (h₁ : QuasiIso (singularTotalUnitApp k S.X₁))
    (h₃ : QuasiIso (singularTotalUnitApp k S.X₃)) :
    QuasiIso (singularTotalUnitApp k S.X₂) := by
  let η := singularTotalUnit k
  let t : S ⟶ S.map (singularTotalFunctor k) :=
    ⟨η.app S.X₁, η.app S.X₂, η.app S.X₃, (η.naturality S.f).symm, (η.naturality S.g).symm⟩
  let : QuasiIso t.τ₁ := h₁
  let : QuasiIso t.τ₃ := h₃
  exact quasiIso_τ₂ t hS (singularTotalFunctor_shortExact S hS)

private theorem singularTotalUnit_quasiIso_iff_of_quasiIso
    {K L : CochainComplex (PresheafWithTransfers.{v} k) ℤ} (f : K ⟶ L)
    (b : ℤ) [K.IsStrictlyLE b] [L.IsStrictlyLE b] [QuasiIso f] :
    QuasiIso (singularTotalUnitApp k K) ↔ QuasiIso (singularTotalUnitApp k L) := by
  let C := singularTotalFunctor k
  let η := singularTotalUnit k
  let : QuasiIso (C.map f) := singularTotalFunctor_quasiIso f b
  have h : f ≫ η.app L = η.app K ≫ C.map f := η.naturality f
  constructor
  · intro hk
    let : QuasiIso (η.app K) := hk
    have : QuasiIso (f ≫ η.app L) := h.symm ▸ quasiIso_comp (η.app K) (C.map f)
    exact quasiIso_of_comp_left f (η.app L)
  · intro hl
    let : QuasiIso (η.app L) := hl
    have : QuasiIso (η.app K ≫ C.map f) := h ▸ quasiIso_comp f (η.app L)
    exact quasiIso_of_comp_right (η.app K) (C.map f)

private theorem singularTotalUnit_quasiIso_of_supportedAt
    (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) (a : ℤ)
    [K.IsStrictlyLE a] [K.IsStrictlyGE a] (h : (K.homology a).IsA1Invariant) :
    QuasiIso (singularTotalUnitApp k K) := by
  have hz (i : ℤ) (hi : i ≠ a) : IsZero (K.X i) := by
    by_cases hia : i < a
    · exact K.isZero_of_isStrictlyGE a i hia
    · exact K.isZero_of_isStrictlyLE a i (by omega)
  let h₁ := (hz (a - 1) (by omega)).eq_of_src (K.d (a - 1) a) 0
  let h₂ := (hz (a + 1) (by omega)).eq_of_tgt (K.d a (a + 1)) 0
  let : IsIso (K.iCycles a) := K.isIso_iCycles a (a + 1) ((c).next_eq' rfl) h₂
  let : IsIso (K.homologyπ a) :=
    K.isIso_homologyπ (a - 1) a ((c).prev_eq' (by change a - 1 + 1 = a; omega)) h₁
  let e : K.X a ≅ K.homology a := (asIso (K.iCycles a)).symm ≪≫ asIso (K.homologyπ a)
  have hx : (K.X a).IsA1Invariant := h.of_iso e.symm
  exact singularTotalUnitApp_quasiIso_of_terms K a fun i => by
    by_cases hi : i = a
    · exact hi.symm ▸ hx
    · exact isA1Invariant_of_isZero (hz i hi)

private theorem invariant_homology_of_quasiIsoAt
    {K L : CochainComplex (PresheafWithTransfers.{v} k) ℤ} (f : K ⟶ L) (i : ℤ)
    [QuasiIsoAt f i] :
    (K.homology i).IsA1Invariant ↔ (L.homology i).IsA1Invariant :=
  ⟨fun h => h.of_iso (asIso (HomologicalComplex.homologyMap f i)),
    fun h => h.of_iso (asIso (HomologicalComplex.homologyMap f i)).symm⟩

private theorem singularTotalUnit_quasiIso_of_bounded (a : ℤ) :
    ∀ (n : ℕ) (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ),
      K.IsStrictlyGE a → K.IsStrictlyLE (a + (n : ℤ)) →
      (∀ i : ℤ, (K.homology i).IsA1Invariant) → QuasiIso (singularTotalUnitApp k K) := by
  intro n
  induction n with
  | zero =>
    intro K h₀ h₁ h
    let : K.IsStrictlyGE a := h₀
    let : K.IsStrictlyLE a := by simpa only [Nat.cast_zero, add_zero] using h₁
    exact singularTotalUnit_quasiIso_of_supportedAt K a (h a)
  | succ n ih =>
    intro K h₀ h₁ h
    let b := a + (n : ℤ)
    let d := b + 1
    let : K.IsStrictlyGE a := h₀
    let : K.IsStrictlyLE d := by simpa only [Nat.cast_succ, ← add_assoc, d, b] using h₁
    let S := K.shortComplexTruncLE b
    let U := K.truncGE d
    let f := K.shortComplexTruncLEX₃ToTruncGE b d
    have hu : U.IsStrictlyLE d := by
      apply (CochainComplex.isStrictlyLE_iff U d).2
      intro i hi
      exact (K.isZero_of_isStrictlyLE d i hi).of_iso (K.truncGEXIso d i hi)
    let : U.IsStrictlyLE d := hu
    have hu' : (U.homology d).IsA1Invariant :=
      (invariant_homology_of_quasiIsoAt (K.πTruncGE d) d).1 (h d)
    have huq := singularTotalUnit_quasiIso_of_supportedAt U d hu'
    have hs₃ : S.X₃.IsStrictlyLE d := by
      apply (CochainComplex.isStrictlyLE_iff _ d).2
      intro i hi
      have hg : Epi (S.g.f i) := inferInstance
      exact IsZero.of_epi (S.g.f i) (K.isZero_of_isStrictlyLE d i hi)
    let : S.X₃.IsStrictlyLE d := hs₃
    have h₃ := (singularTotalUnit_quasiIso_iff_of_quasiIso f d).2 huq
    have hs₁ : (K.truncLE b).IsStrictlyGE a := by
      apply (CochainComplex.isStrictlyGE_iff _ a).2
      intro i hi
      exact IsZero.of_mono ((K.ιTruncLE b).f i) (K.isZero_of_isStrictlyGE a i hi)
    have h₁' (i : ℤ) : ((K.truncLE b).homology i).IsA1Invariant := by
      by_cases hi : i ≤ b
      · let : QuasiIsoAt (K.ιTruncLE b) i := K.quasiIsoAt_ιTruncLE b i hi
        exact (invariant_homology_of_quasiIsoAt (K.ιTruncLE b) i).2 (h i)
      · exact isA1Invariant_of_isZero ((K.truncLE b).isZero_of_isLE b i (by omega))
    have hs₁' : (K.truncLE b).IsStrictlyLE (a + (n : ℤ)) := by
      change (K.truncLE b).IsStrictlyLE b
      infer_instance
    exact singularTotalUnit_quasiIso_middle S (K.shortComplexTruncLE_shortExact b)
      (ih (K.truncLE b) hs₁ hs₁' h₁') h₃

private theorem isIso_singularBicomplex_total_map_f
    {K L : CochainComplex (PresheafWithTransfers.{v} k) ℤ} (f : K ⟶ L) (a n : ℤ)
    (ha : a < n) (hf : ∀ p : ℤ, a < p → IsIso (f.f p)) :
    IsIso (((singularTotalFunctor k).map f).f n) := by
  let B := (singularBicomplexFunctor k).obj K
  let C := (singularBicomplexFunctor k).obj L
  let g := (singularBicomplexFunctor k).map f
  have h (p q : ℤ) (hpq : p + q = n) : IsIso ((g.f p).f q) := by
    by_cases hq : 0 < q
    · exact (isZero_singularCochainComplex_X (K.X p) 0 q hq).isIso
        (isZero_singularCochainComplex_X (L.X p) 0 q hq) _
    · let : IsIso (f.f p) := hf p (by omega)
      let E := singularCochainFunctor 0 ⋙
        HomologicalComplex.eval (PresheafWithTransfers.{v} k) c q
      exact inferInstanceAs (IsIso (E.map (f.f p)))
  let e : (C.total c).X n ⟶ (B.total c).X n := C.totalDesc fun p q hpq =>
    letI := h p q hpq
    inv ((g.f p).f q) ≫ B.ιTotal c p q n hpq
  change IsIso ((HomologicalComplex₂.total.map g c).f n)
  refine ⟨e, ?_, ?_⟩
  · apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    let : IsIso ((g.f p).f q) := h p q hpq
    rw [ιTotal_map_assoc, Category.comp_id]
    dsimp only [e]
    rw [ι_totalDesc, IsIso.hom_inv_id_assoc]
  · apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    let : IsIso ((g.f p).f q) := h p q hpq
    dsimp only [e]
    rw [ι_totalDesc_assoc, Category.assoc, ιTotal_map, IsIso.inv_hom_id_assoc, Category.comp_id]

private theorem quasiIsoAt_of_adjacent_iso
    {K L : CochainComplex (PresheafWithTransfers.{v} k) ℤ} (f : K ⟶ L) (i : ℤ)
    [IsIso (f.f (i - 1))] [IsIso (f.f i)] [IsIso (f.f (i + 1))] :
    QuasiIsoAt f i := by
  rw [quasiIsoAt_iff' f (i - 1) i (i + 1) (by simp) (by simp)]
  let g := (HomologicalComplex.shortComplexFunctor' _ c (i - 1) i (i + 1)).map f
  let : IsIso g.τ₁ := ‹IsIso (f.f (i - 1))›
  let : IsIso g.τ₂ := ‹IsIso (f.f i)›
  let : IsIso g.τ₃ := ‹IsIso (f.f (i + 1))›
  let : IsIso g := ShortComplex.isIso_of_isIso g
  infer_instance

/-- The original total singular unit is a quasi-isomorphism on
bounded-above transfer complexes with A¹-invariant cohomology. -/
theorem singularTotalUnitApp_quasiIso_of_homology
    (K : CochainComplex (PresheafWithTransfers.{v} k) ℤ) (b : ℤ) [K.IsStrictlyLE b]
    (hK : ∀ i : ℤ, (K.homology i).IsA1Invariant) : QuasiIso (singularTotalUnitApp k K) := by
  refine ⟨fun i => ?_⟩
  let a := i - 2
  let B := max a b
  let L := K.truncGE a
  let f := K.πTruncGE a
  have hl : L.IsStrictlyLE B := by
    apply (CochainComplex.isStrictlyLE_iff L B).2
    intro p hp
    exact (K.isZero_of_isStrictlyLE b p (by dsimp [B] at hp; omega)).of_iso
      (K.truncGEXIso a p (by dsimp [B] at hp; omega))
  have hL (q : ℤ) : (L.homology q).IsA1Invariant := by
    by_cases hq : a ≤ q
    · let : QuasiIsoAt f q := K.quasiIsoAt_πTruncGE a q hq
      exact (invariant_homology_of_quasiIsoAt f q).1 (hK q)
    · exact isA1Invariant_of_isZero (L.isZero_of_isGE a q (by omega))
  have he : a + ((B - a).toNat : ℤ) = B := by dsimp [B]; omega
  let : QuasiIso (singularTotalUnitApp k L) :=
    singularTotalUnit_quasiIso_of_bounded a (B - a).toNat L inferInstance (he.symm ▸ hl) hL
  let C := singularTotalFunctor k
  have hf (p : ℤ) (hp : a < p) : IsIso (f.f p) := by
    let e := ComplexShape.embeddingUpIntGE a
    let j := (p - a).toNat
    have hj : e.f j = p := by
      rw [ComplexShape.embeddingUpIntGE_f]
      dsimp [j]
      omega
    have hb' : ¬ e.BoundaryGE j := by
      rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff]
      dsimp [j]
      omega
    change IsIso ((e.liftExtend (K.restrictionToTruncGE' e)
      (K.restrictionToTruncGE'_hasLift e)).f p)
    exact (e.isIso_liftExtend_f_iff _ _ hj).2 (K.isIso_restrictionToTruncGE' e j hb')
  let : IsIso ((C.map f).f (i - 1)) :=
    isIso_singularBicomplex_total_map_f f a (i - 1) (by dsimp [a]; omega) hf
  let : IsIso ((C.map f).f i) :=
    isIso_singularBicomplex_total_map_f f a i (by dsimp [a]; omega) hf
  let : IsIso ((C.map f).f (i + 1)) :=
    isIso_singularBicomplex_total_map_f f a (i + 1) (by dsimp [a]; omega) hf
  let : QuasiIsoAt (C.map f) i := quasiIsoAt_of_adjacent_iso (C.map f) i
  let : QuasiIsoAt f i := K.quasiIsoAt_πTruncGE a i (by dsimp [a]; omega)
  let : QuasiIsoAt (singularTotalUnitApp k L) i :=
    QuasiIso.quasiIsoAt (f := singularTotalUnitApp k L) i
  have h := (singularTotalUnit k).naturality f
  let : QuasiIsoAt (singularTotalUnitApp k K ≫ C.map f) i :=
    h ▸ quasiIsoAt_comp f (singularTotalUnitApp k L) i
  exact quasiIsoAt_of_comp_right _ (C.map f) i

end AlgebraicGeometry.PresheafWithTransfers
