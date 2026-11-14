/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-! # Exactness of diagonal coproduct totalization

An objectwise short exact sequence of bicomplexes induces a short exact sequence of their
actual total complexes when coproducts of the relevant shape are exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex₂

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

local notation "c" => ComplexShape.up ℤ
local notation "BC" => HomologicalComplex₂ C c c

/-- The actual entire antidiagonal, including its zero summands. -/
abbrev DiagonalIndex (n : ℤ) := (ComplexShape.π c c c) ⁻¹' ({n} : Set ℤ)

/-- Evaluation of a bicomplex on a diagonal. -/
def diagonalFunctor (n : ℤ) : BC ⥤ (Discrete (DiagonalIndex n) ⥤ C) where
  obj K := Discrete.functor (fun p => (K.X p.val.1).X p.val.2)
  map f := Discrete.natTrans (fun p => (f.f p.as.val.1).f p.as.val.2)
  map_id K := by
    ext p
    rfl
  map_comp f g := by
    ext p
    rfl

instance diagonalFunctor_additive (n : ℤ) : (diagonalFunctor (C := C) n).Additive where
  map_add {K L f g} := by
    ext p
    rfl

private theorem discrete_shortExact {I : Type} (S : ShortComplex (Discrete I ⥤ C))
    (hS : ∀ i, (S.map ((evaluation _ _).obj (Discrete.mk i))).ShortExact) : S.ShortExact where
  mono_f := by
    have : ∀ i, Mono (S.f.app i) := fun i => (hS i.as).mono_f
    exact NatTrans.mono_of_mono_app S.f
  epi_g := by
    have : ∀ i, Epi (S.g.app i) := fun i => (hS i.as).epi_g
    exact NatTrans.epi_of_epi_app S.g
  exact := by
    rw [ShortComplex.exact_iff_isZero_homology, IsZero.iff_id_eq_zero]
    apply NatTrans.ext
    funext i
    have hz := ((ShortComplex.exact_iff_isZero_homology _).mp (hS i.as).exact).of_iso
      (S.mapHomologyIso ((evaluation _ _).obj i)).symm
    exact hz.eq_of_src _ _

variable [HasCoproducts.{0} C] [AB4OfSize.{0} C]
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts

/-- Each degree of the native totalization is the coproduct of its actual diagonal. -/
def totalDegreeIso (n : ℤ) :
    totalFunctor C c c c ⋙ HomologicalComplex.eval C c n ≅
      diagonalFunctor n ⋙ colim :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro K L f
    change (total.map f c).f n ≫ 𝟙 ((L.total c).X n) =
      𝟙 ((K.total c).X n) ≫ colim.map ((diagonalFunctor n).map f)
    have h : (total.map f c).f n = colim.map ((diagonalFunctor n).map f) := by
      apply HomologicalComplex₂.total.hom_ext
      intro p q hpq
      exact (ιTotal_map K L f c p q n hpq).trans
        (ι_colimMap ((diagonalFunctor n).map f) (Discrete.mk ⟨(p, q), hpq⟩)).symm
    exact (Category.comp_id _).trans (h.trans (Category.id_comp _).symm))

instance totalFunctor_additive : (totalFunctor C c c c).Additive where
  map_add {K L f g} := by
    ext1 n
    let F := totalFunctor C c c c ⋙ HomologicalComplex.eval C c n
    let : (colim : (Discrete (DiagonalIndex n) ⥤ C) ⥤ C).Additive :=
      Functor.additive_of_preservesBinaryBiproducts _
    let : F.Additive := Functor.additive_of_iso (totalDegreeIso (C := C) n).symm
    exact F.map_add

/-- A termwise short exact sequence of bicomplexes remains short exact on totalization. -/
theorem total_shortExact {S : ShortComplex BC}
    (hS : ∀ p q : ℤ,
      ((S.map (HomologicalComplex.eval _ c p)).map (HomologicalComplex.eval _ c q)).ShortExact) :
    (S.map (totalFunctor C c c c)).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have hdiag : (S.map (diagonalFunctor n)).ShortExact :=
    discrete_shortExact _ (fun p => hS p.val.1 p.val.2)
  have hsum := hdiag.map_of_exact (colim (J := Discrete (DiagonalIndex n)) (C := C))
  exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso (totalDegreeIso n))).mpr hsum

end HomologicalComplex₂
