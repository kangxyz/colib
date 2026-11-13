/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.CoefficientModules
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusTorsionFree

/-!
# The original finite motivic cone computes its strict coefficient quotient

The all-axis reduced torus is a genuine direct summand of the original
representable. Its integer cancellation passes through the actual singular
terms and exact sheafification. The statement concerns the original cone.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]

/-- Multiplication cancels in every original singular presheaf term. -/
theorem motivicSingularPresheaf_nsmul_mono (q r n : ℕ) (hn : n ≠ 0) :
    Mono (n • 𝟙 (motivicSingularPresheaf k q r)) := by
  have : ∀ X, Mono ((n • 𝟙 (motivicSingularPresheaf k q r)).app X) := by
    intro X
    rw [NatTrans.app_nsmul]
    apply (AddCommGrpCat.mono_iff_injective _).mpr
    change Function.Injective (fun x : sections (reducedTorus k q)
      (Cor.simplexProduct (Cor.mk X.unop) r) => n • x)
    exact reducedTorus_sections_nsmul_injective k q _ n hn
  exact NatTrans.mono_of_mono_app _

variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

/-- Nonzero natural multiplication is monic on each actual motivic sheaf term. -/
theorem motivicSheafComplex_nsmul_id_X_mono (q n : ℕ) (hn : n ≠ 0) (i : ℤ) :
    Mono (n • 𝟙 ((motivicSheafComplex k q).X i)) := by
  by_cases hi : (q : ℤ) < i
  · have hz : IsZero ((motivicSheafComplex k q).X i) :=
      (SheafWithTransfers.toSheaf k).map_isZero (isZero_motivicComplex_X k q i hi)
    exact ⟨fun f g _ => hz.eq_of_tgt f g⟩
  · obtain ⟨r, rfl⟩ : ∃ r : ℕ, i = (q : ℤ) - r :=
      ⟨Int.toNat ((q : ℤ) - i), by omega⟩
    let F := presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}
    have := motivicSingularPresheaf_nsmul_mono k q r n hn
    have hm : Mono (F.map (n • 𝟙 (motivicSingularPresheaf k q r))) := inferInstance
    have : Mono (n • 𝟙 (F.obj (motivicSingularPresheaf k q r))) := by
      simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id] using hm
    let e := motivicSheafComplexXIso k q r
    have he : n • 𝟙 ((motivicSheafComplex k q).X ((q : ℤ) - r)) =
        e.hom ≫ (n • 𝟙 _) ≫ e.inv := by
      simp only [Preadditive.comp_nsmul,
        Preadditive.nsmul_comp, Category.id_comp, Iso.hom_inv_id]
    rw [he]
    infer_instance

/-- Nonzero natural multiplication is monic on the original ordinary motivic complex. -/
theorem motivicSheafComplex_nsmul_id_mono (q n : ℕ) (hn : n ≠ 0) :
    Mono (n • 𝟙 (motivicSheafComplex k q)) := by
  apply HomologicalComplex.mono_of_mono_f
  intro i
  exact motivicSheafComplex_nsmul_id_X_mono k q n hn i

/-- The original finite cone maps quasi-isomorphically to its actual strict quotient. -/
@[colib_tag "COL-1229",
  colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/HomotopyCategory/ShortExact.lean:138-154"
  "specialization" "Native cone comparison after proving actual motivic multiplication monic"]
theorem motivicFiniteToCoefficientQuotient_quasiIso (q n : ℕ) (hn : n ≠ 0) :
    QuasiIso (motivicFiniteToCoefficientQuotient k q n) := by
  have := motivicSheafComplex_nsmul_id_mono k q n hn
  exact CochainComplex.finiteCoefficients.quasiIso_toQuotient (motivicSheafComplex k q) n

variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k))) CommRingCat.{u + 1}]
variable [(SmoothSite.nisnevichTopology (Spec (.of k))).WEqualsLocallyBijective
  CommRingCat.{u + 1}]
variable [(SmoothSite.nisnevichTopology (Spec (.of k))).WEqualsLocallyBijective
  AddCommGrpCat.{u + 1}]

/-- The original finite cone computes the underlying actual coefficient module complex. -/
theorem motivicFiniteToCoefficientModuleComplex_quasiIso (q n : ℕ) (hn : n ≠ 0) :
    QuasiIso (motivicFiniteToCoefficientModuleComplex k q n) := by
  unfold motivicFiniteToCoefficientModuleComplex
  have := motivicFiniteToCoefficientQuotient_quasiIso k q n hn
  infer_instance

end AlgebraicGeometry.PresheafWithTransfers
