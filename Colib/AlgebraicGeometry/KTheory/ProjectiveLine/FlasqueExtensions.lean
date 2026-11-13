/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Mathlib.Topology.Sheaves.Flasque

/-! # Extension closure of flasque sheaves -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace TopCat.Sheaf.IsFlasque

universe u

variable {X : TopCat.{u}}

/-- A short exact extension of flasque abelian sheaves is flasque. -/
theorem of_shortExact_of_isFlasque₁₃ {S : ShortComplex (Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) [S.X₁.IsFlasque] [S.X₃.IsFlasque] : S.X₂.IsFlasque where
  epi {U V} k := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro z
    obtain ⟨c, hc⟩ := (AddCommGrpCat.epi_iff_surjective (S.X₃.obj.map k)).mp
      inferInstance (S.g.hom.app V z)
    obtain ⟨b, hb⟩ := (AddCommGrpCat.epi_iff_surjective _).mp
      (epi_of_shortExact (U := unop U) hS) c
    have hn := ConcreteCategory.congr_hom (S.g.hom.naturality k) b
    change S.g.hom.app V (S.X₂.obj.map k b) =
      S.X₃.obj.map k (S.g.hom.app U b) at hn
    have hz : S.g.hom.app V (z - S.X₂.obj.map k b) = 0 := by
      rw [map_sub, hn, hb, hc, sub_self]
    obtain ⟨a, ha⟩ := TopCat.Sheaf.sections_exact_of_left_exact
      hS.exact hS.mono_f (z - S.X₂.obj.map k b) hz
    obtain ⟨d, hd⟩ := (AddCommGrpCat.epi_iff_surjective (S.X₁.obj.map k)).mp
      inferInstance a
    refine ⟨b + S.f.hom.app U d, ?_⟩
    have hf := ConcreteCategory.congr_hom (S.f.hom.naturality k) d
    change S.f.hom.app V (S.X₁.obj.map k d) = S.X₂.obj.map k (S.f.hom.app U d) at hf
    rw [map_add, ← hf, hd, ha]
    abel

/-- Flasqueness is invariant under a sheaf isomorphism. -/
theorem of_iso {F G : Sheaf AddCommGrpCat.{u} X} (e : F ≅ G) (hF : F.IsFlasque) :
    G.IsFlasque where
  epi {U V} i := by
    let := hF
    have h (W : _) : IsIso (e.hom.hom.app W) := ⟨⟨e.inv.hom.app W,
      congrArg (fun g => g.hom.app W) e.hom_inv_id, congrArg (fun g => g.hom.app W) e.inv_hom_id⟩⟩
    have h₂ : Epi (F.obj.map i ≫ e.hom.hom.app V) := inferInstance
    rw [e.hom.hom.naturality i] at h₂
    exact (CategoryTheory.epi_comp_iff_of_epi (e.hom.hom.app U) (G.obj.map i)).1 h₂

end TopCat.Sheaf.IsFlasque
