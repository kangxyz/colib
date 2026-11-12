/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import Mathlib.Topology.KrullDimension
import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop

/-!
# Finite Krull dimension of smooth-site objects over a field

The actual finite affine subcover has finite-type coordinate rings over
the field of global sections of the base spectrum. Each chart has finite
Krull dimension. Coheight is preserved by the chart open immersions, so
the maximum of the finitely many chart bounds bounds the whole scheme.
-/

@[expose] public noncomputable section

open CategoryTheory Order Topology TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

private theorem exists_nat_bound_of_ne_top (a : WithBot ℕ∞) (ha : a ≠ ⊤) :
    ∃ d : ℕ, a ≤ d := by
  cases a using WithBot.recBotCoe with
  | bot => exact ⟨0, bot_le⟩
  | coe a =>
    have h : a ≠ ⊤ := by simpa using ha
    obtain ⟨d, hd⟩ := ENat.exists_nat_gt h
    exact ⟨d, WithBot.coe_le_coe.mpr hd.le⟩

attribute [local instance] specializationOrder in
/-- The underlying scheme of an actual smooth-site object over a field
has a natural-number bound on its topological Krull dimension. -/
theorem exists_nat_topologicalKrullDim_le (k : Type u) [Field k]
    (X : SmoothSite (Spec (.of k))) : ∃ d : ℕ, topologicalKrullDim X.left ≤ d := by
  classical
  let : CompactSpace (Spec (.of k) : Scheme.{u}) :=
    inferInstanceAs (CompactSpace (PrimeSpectrum k))
  let : CompactSpace X.left :=
    QuasiCompact.compactSpace_of_compactSpace (Y := Spec (.of k)) X.hom
  let U := X.left.affineCover.finiteSubcover
  let : Fintype U.I₀ := Fintype.ofFinite _
  let : Field Γ(Spec (.of k), ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)).toField
  have hChart (i : U.I₀) : ∃ d : ℕ, topologicalKrullDim (U.X i) ≤ d := by
    let : IsAffine (U.X i) :=
      inferInstanceAs (IsAffine (X.left.affineCover.finiteSubcover.X i))
    let f : U.X i ⟶ Spec (.of k) := U.f i ≫ X.hom
    let : LocallyOfFiniteType f :=
      inferInstanceAs (LocallyOfFiniteType (U.f i ≫ X.hom))
    let : Algebra Γ(Spec (.of k), ⊤) Γ(U.X i, ⊤) := f.appTop.hom.toAlgebra
    have : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(U.X i, ⊤) :=
      RingHom.finiteType_algebraMap.mp
        (HasRingHomProperty.appTop @LocallyOfFiniteType f inferInstance)
    have hDim : topologicalKrullDim (U.X i) = ringKrullDim Γ(U.X i, ⊤) := by
      calc
        topologicalKrullDim (U.X i) = topologicalKrullDim (Spec Γ(U.X i, ⊤)) :=
          IsHomeomorph.topologicalKrullDim_eq _
            (Scheme.homeoOfIso (U.X i).isoSpec).isHomeomorph
        _ = ringKrullDim Γ(U.X i, ⊤) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    rw [hDim]
    exact exists_nat_bound_of_ne_top _
      (ringKrullDim_ne_top_of_finiteType (κ := Γ(Spec (.of k), ⊤)))
  choose d hd using hChart
  let D := Finset.univ.sup d
  refine ⟨D, ?_⟩
  have hDim (Z : Scheme.{u}) : krullDim Z = topologicalKrullDim Z :=
    krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Z)).symm
  rw [← hDim X.left, krullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ := U.exists_eq x
  rw [Topology.IsOpenEmbedding.coheight_eq (U.f i) (U.f i).isOpenEmbedding]
  have hi : d i ≤ D := Finset.le_sup (Finset.mem_univ i)
  exact (coheight_le_krullDim y).trans
    ((hDim (U.X i)).le.trans ((hd i).trans
      (WithBot.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hi))))

end AlgebraicGeometry.Scheme.SmoothSite
