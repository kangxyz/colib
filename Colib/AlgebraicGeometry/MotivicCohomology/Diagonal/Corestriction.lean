/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.CycleFace
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.ReducedPushforward
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.TopDegree

import Colib.Util.References

/-!
# Finite corestriction on diagonal motivic cohomology

Finite pushforward on the original signed cycles commutes with both faces.
It therefore induces the map on the singular boundary quotient, and the
native field comparison carries this map to the derived diagonal group.

Adapted from `Motivic/Cohomology/Diagonal/Corestriction.lean:46-109,247-264`
at `a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers
open DiagonalTopDegree DiagonalFiniteCyclePushforward DiagonalReducedPushforward

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
variable (q : ℕ)

/-- Finite pushforward commutes with each actual face on the reduced torus. -/
theorem reducedPushforward_face (i : Fin 2) (x : chains E q 1) :
    reducedPushforward (k := k) (E := E) 0 q
        (transfer (reducedTorus E q) ((Cor.simplexProductCosimplicial (point E)).δ i) x) =
      transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ i)
        (reducedPushforward (k := k) (E := E) 1 q x) := by
  let δE : Cor.mk (source E 0) ⟶ Cor.mk (source E 1) :=
    (Cor.simplexProductCosimplicial (point E)).δ i
  let δk : Cor.mk (source k 0) ⟶ Cor.mk (source k 1) :=
    (Cor.simplexProductCosimplicial (point k)).δ i
  obtain ⟨⟨z⟩, rfl⟩ := toReducedTorus_surjective E q (Cor.mk (source E 1)) x
  let α : Cor.mk (source E 1) ⟶ Cor.mk (target E q) := z
  let β : Cor.mk (source k 1) ⟶ Cor.mk (target k q) :=
    cyclePushforward (k := k) 1 q α
  have hE := congrArg (reducedPushforward (k := k) (E := E) 0 q)
    (reducedTorus_transfer_apply E q δE α)
  have h₀ := reducedPushforward_quotient (k := k) (E := E) 0 q (δE ≫ α)
  have h₁ := reducedPushforward_quotient (k := k) (E := E) 1 q α
  have hpush : cyclePushforward (k := k) 0 q (δE ≫ α) = δk ≫ β :=
    cyclePushforward_face (k := k) (E := E) q i α
  have hclass := congrArg (fun γ : Cor.mk (source k 0) ⟶ Cor.mk (target k q) =>
    (toReducedTorus k q).hom.app (op (Cor.mk (source k 0))) (ULift.up γ)) hpush
  exact (hE.trans h₀).trans (hclass.trans
    ((reducedTorus_transfer_apply k q δk β).symm.trans
      (congrArg (transfer (reducedTorus k q) δk) h₁.symm)))

/-- Both endpoints retain the original alternating boundary signs. -/
theorem reducedPushforward_boundary (x : chains E q 1) :
    reducedPushforward (k := k) (E := E) 0 q (boundary E q x) =
      boundary k q (reducedPushforward (k := k) (E := E) 1 q x) := by
  let push : chains E q 0 →+ chains k q 0 :=
    (reducedPushforward (k := k) (E := E) 0 q).hom
  let y : chains k q 1 := reducedPushforward (k := k) (E := E) 1 q x
  let dE (i : Fin 2) : chains E q 0 :=
    transfer (reducedTorus E q) ((Cor.simplexProductCosimplicial (point E)).δ i) x
  let dk (i : Fin 2) : chains k q 0 :=
    transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ i) y
  change push (boundary E q x) = boundary k q y
  calc
    _ = push (dE 0 - dE 1) := congrArg push (boundary_eq_endpoints E q x)
    _ = push (dE 0) - push (dE 1) := map_sub push _ _
    _ = dk 0 - dk 1 := congrArg₂ (· - ·)
      (reducedPushforward_face (k := k) (E := E) q 0 x)
      (reducedPushforward_face (k := k) (E := E) q 1 x)
    _ = _ := (boundary_eq_endpoints k q y).symm

/-- Finite transfer descends through the original singular boundary quotient. -/
def quotientCorestriction : zeroHomology E q →+ zeroHomology k q :=
  QuotientAddGroup.map (boundary E q).range (boundary k q).range
    (reducedPushforward (k := k) (E := E) 0 q).hom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨reducedPushforward (k := k) (E := E) 1 q x,
        (reducedPushforward_boundary q x).symm⟩)

/-- The quotient transfer retains the finite pushforward of each representative. -/
theorem quotientCorestriction_mk (x : chains E q 0) :
    quotientCorestriction (k := k) q (QuotientAddGroup.mk x) =
      QuotientAddGroup.mk (reducedPushforward (k := k) (E := E) 0 q x) := rfl

/-- Finite corestriction on the original raw diagonal homology in every weight. -/
def corestriction : (motivicRawBaseComplex E q).homology q →+
    (motivicRawBaseComplex k q).homology q :=
  (quotientToRawEquiv k q).toAddMonoidHom.comp
    ((quotientCorestriction (k := k) (E := E) q).comp
      (quotientToRawEquiv E q).symm.toAddMonoidHom)

/-- The class of a reduced zero-chain transfers by the native finite pushforward. -/
theorem corestriction_singularClass (x : chains E q 0) :
    corestriction (k := k) q (singularClass E q x) =
      singularClass k q (reducedPushforward (k := k) (E := E) 0 q x) := by
  rw [← quotientToRawEquiv_mk]
  change quotientToRawEquiv k q (quotientCorestriction (k := k) q
    ((quotientToRawEquiv E q).symm (quotientToRawEquiv E q _))) = _
  rw [AddEquiv.symm_apply_apply, quotientCorestriction_mk]
  let y : chains k q 0 := reducedPushforward (k := k) (E := E) 0 q x
  exact quotientToRawEquiv_mk k q y

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Finite corestriction on the original derived diagonal groups. -/
def integralCorestriction :
    motivicCohomology E q q (SmoothSite.base (Spec (.of E))) →+
      motivicCohomology k q q (SmoothSite.base (Spec (.of k))) :=
  (motivicRawBaseEvaluationComparison k q q).symm.toAddMonoidHom.comp
    ((corestriction (k := k) (E := E) q).comp
      (motivicRawBaseEvaluationComparison E q q).toAddMonoidHom)

/-- The derived transfer commutes with the actual raw field comparisons. -/
theorem integralCorestriction_comparison
    (x : motivicCohomology E q q (SmoothSite.base (Spec (.of E)))) :
    motivicRawBaseEvaluationComparison k q q (integralCorestriction (k := k) q x) =
      corestriction (k := k) q (motivicRawBaseEvaluationComparison E q q x) :=
  (motivicRawBaseEvaluationComparison k q q).apply_symm_apply _


attribute [colib_tag "COL-1025",
  colib_ref "motivic_source_a6805c4"
    "Motivic/Cohomology/Diagonal/Corestriction.lean:46-110" "adaptation"
    "The finite transfer preserves the actual signed singular boundary and cycle class"]
  reducedPushforward_boundary quotientCorestriction_mk corestriction corestriction_singularClass

attribute [colib_tag "COL-1025",
  colib_ref "motivic_source_a6805c4"
    "Motivic/Cohomology/Diagonal/Corestriction.lean:250-263" "adaptation"
    "The actual integral transfer is transported by the base-field comparison"]
  integralCorestriction integralCorestriction_comparison

end AlgebraicGeometry.MotivicCohomology.DiagonalCorestriction
