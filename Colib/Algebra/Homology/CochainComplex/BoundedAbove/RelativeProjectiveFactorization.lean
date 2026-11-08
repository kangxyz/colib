/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.OppositeQuasiIso
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Genuine relative projective factorization

The full opposite CM5a theorem factors an original bounded-above chain map
through a bounded-above middle complex. The second map is an actual
quasi-isomorphism. The first has degreewise projective cokernel and is
split in every degree. No projectivity of the original source is assumed.
The explicit resulting upper bound is one more than the common input bound.

Adapted from the same-named Quillen module at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Mathlib opposite CM5a.
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Dual CM5a gives a relative projective factorization with actual original endpoints. -/
theorem exists_boundedAbove_relative_projective_factorization [EnoughProjectives C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b] :
    ∃ (M : CochainComplex C ℤ) (i : K ⟶ M) (p : M ⟶ L),
      M.IsStrictlyLE (b + 1) ∧ QuasiIso p ∧ i ≫ p = f ∧
      ∀ n, Abelian.epiWithInjectiveKernel ((i.f n).op) := by
  let E := CochainComplex.opEquivalence C
  let KO := E.functor.obj (op K)
  let LO := E.functor.obj (op L)
  let fO : LO ⟶ KO := E.functor.map f.op
  have : LO.IsStrictlyGE (-(b + 1) + 1) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (L.isZero_of_isStrictlyLE b (-n) (by omega)).op
  have : KO.IsStrictlyGE (-(b + 1)) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact (K.isZero_of_isStrictlyLE b (-n) (by omega)).op
  obtain ⟨MO, hMO, iO, pO, hiO, hqiO, hpO, hfac⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.cm5a fO (-(b + 1))
  let M := (E.inverse.obj MO).unop
  let i : K ⟶ M := (E.unitIso.app (op K)).inv.unop ≫ (E.inverse.map pO).unop
  let p : M ⟶ L := (E.inverse.map iO).unop ≫ (E.unitIso.app (op L)).hom.unop
  refine ⟨M, i, p, ?_, ?_, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact (MO.isZero_of_isStrictlyGE (-(b + 1)) (-n) (by omega)).unop
  · let : QuasiIso iO := hqiO
    have := quasiIso_cochain_opEquivalence_inverse_map iO
    dsimp [p, E]
    infer_instance
  · have hmid : (E.inverse.map pO).unop ≫ (E.inverse.map iO).unop =
        (E.inverse.map fO).unop := by
      rw [← unop_comp, ← E.inverse.map_comp, hfac]
    have hn := congrArg Quiver.Hom.unop (E.unitIso.hom.naturality f.op)
    dsimp only [Functor.id_map, Functor.comp_map, unop_comp] at hn
    dsimp only [i, p]
    calc
      _ = (E.unitIso.app (op K)).inv.unop ≫
          ((E.inverse.map pO).unop ≫ (E.inverse.map iO).unop) ≫
            (E.unitIso.app (op L)).hom.unop := by simp only [Category.assoc]
      _ = (E.unitIso.app (op K)).inv.unop ≫
          (E.inverse.map fO).unop ≫ (E.unitIso.app (op L)).hom.unop := by rw [hmid]
      _ = (E.unitIso.app (op K)).inv.unop ≫ (E.unitIso.app (op K)).hom.unop ≫ f := by
        simpa only [Category.assoc, fO, Iso.app_hom, Quiver.Hom.unop_op] using
          congrArg (fun t => (E.unitIso.app (op K)).inv.unop ≫ t) hn.symm
      _ = f := by simp
  · intro n
    change Abelian.epiWithInjectiveKernel
      (((E.unitIso.app (op K)).inv.unop.f n ≫ (E.inverse.map pO).unop.f n).op)
    rw [op_comp]
    apply MorphismProperty.comp_mem
    · exact hpO (-n)
    · apply Abelian.epiWithInjectiveKernel_of_iso

/-- The genuine opposite injective-kernel property provides a split monomorphism
and a projective cokernel, without any assumed projectivity of the source. -/
theorem splitMono_projective_cokernel_of_op_epiWithInjectiveKernel
    {A B : C} (i : A ⟶ B) (hi : Abelian.epiWithInjectiveKernel i.op) :
    IsSplitMono i ∧ Projective (cokernel i) := by
  obtain ⟨Q, hQ, g, hg, ⟨s⟩⟩ := (Abelian.epiWithInjectiveKernel_iff _).mp hi
  have e : Q.unop ≅ cokernel i := IsColimit.coconePointUniqueUpToIso
    s.unop.shortExact.gIsCokernel (colimit.isColimit _)
  exact ⟨IsSplitMono.mk' ⟨s.unop.r, s.unop.f_r⟩,
    Projective.of_iso e inferInstance⟩

/-- Relative projective factorizations retain genuine projective quotient terms. -/
theorem relative_factorization_projective_cokernel
    {K M : CochainComplex C ℤ} (i : K ⟶ M)
    (hi : ∀ n, Abelian.epiWithInjectiveKernel ((i.f n).op)) (n : ℤ) :
    Projective ((cokernel i).X n) := by
  have : Projective (cokernel ((HomologicalComplex.eval C (.up ℤ) n).map i)) :=
    (splitMono_projective_cokernel_of_op_epiWithInjectiveKernel (i.f n) (hi n)).2
  exact Projective.of_iso
    (PreservesCokernel.iso (HomologicalComplex.eval C (.up ℤ) n) i).symm inferInstance

end CochainComplex
