/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FieldChangeFaces
public import Colib.AlgebraicGeometry.MotivicCohomology.Diagonal.FieldChangeReduced

/-!
# Field change on the actual diagonal motivic group

Scalar pullback of signed correspondences preserves the original
identity-axis and simplex-endpoint relations. The resulting map acts on
the original raw diagonal homology, via its native singular quotient.
The rational graph of a tuple changes to the graph of its image units.

Adapted from `Motivic/Cohomology/Diagonal/FieldChange.lean:43-137` at
`a6805c4a87cdfd7717dd7a94039246a167f15380`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Stacks.Chow TopologicalSpace
open Function.locallyFinsuppWithin
open scoped Simplicial

universe u

namespace AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange

open _root_.AlgebraicGeometry.Scheme PresheafWithTransfers
open DiagonalTopDegree DiagonalFiniteCyclePushforward DiagonalReducedPushforward
open DiagonalCycleSymbols (rationalTuple cycleClass cycleClass_apply graphSymbol)
open DiagonalCorestriction DiagonalCorestrictionBaseChange

section Algebra

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

private theorem reducedPullback_face (q : ℕ) (i : Fin 2) (x : chains k q 1) :
    reducedPullback (k := k) (L := L) 0 q
      (transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ i) x) =
      transfer (reducedTorus L q) ((Cor.simplexProductCosimplicial (point L)).δ i)
        (reducedPullback (k := k) (L := L) 1 q x) := by
  let δk : Cor.mk (source k 0) ⟶ Cor.mk (source k 1) :=
    (Cor.simplexProductCosimplicial (point k)).δ i
  let δL : Cor.mk (source L 0) ⟶ Cor.mk (source L 1) :=
    (Cor.simplexProductCosimplicial (point L)).δ i
  obtain ⟨⟨z⟩, rfl⟩ := toReducedTorus_surjective k q (Cor.mk (source k 1)) x
  let α : Cor.mk (source k 1) ⟶ Cor.mk (target k q) := z
  let β : Cor.mk (source L 1) ⟶ Cor.mk (target L q) := cyclePullback (k := k) 1 q α
  have h0 := congrArg (reducedPullback (k := k) (L := L) 0 q)
    (reducedTorus_transfer_apply k q δk α)
  have h1 := reducedPullback_quotient (k := k) (L := L) 0 q (δk ≫ α)
  have h2 := reducedPullback_quotient (k := k) (L := L) 1 q α
  have hface : cyclePullback (k := k) (L := L) 0 q (δk ≫ α) = δL ≫ β :=
    cyclePullback_face (k := k) (L := L) q i α
  have hclass := congrArg (fun γ : Cor.mk (source L 0) ⟶ Cor.mk (target L q) =>
    (toReducedTorus L q).hom.app (op (Cor.mk (source L 0))) (ULift.up γ)) hface
  exact (h0.trans h1).trans (hclass.trans
    ((reducedTorus_transfer_apply L q δL β).symm.trans
      (congrArg (transfer (reducedTorus L q) δL) h2.symm)))

/-- Both changed faces retain the original alternating singular boundary signs. -/
theorem reducedPullback_boundary (q : ℕ) (x : chains k q 1) :
    reducedPullback (k := k) (L := L) 0 q (boundary k q x) =
      boundary L q (reducedPullback (k := k) (L := L) 1 q x) := by
  let pull : chains k q 0 →+ chains L q 0 := (reducedPullback (k := k) (L := L) 0 q).hom
  let y : chains L q 1 := reducedPullback (k := k) (L := L) 1 q x
  let dk (i : Fin 2) : chains k q 0 :=
    transfer (reducedTorus k q) ((Cor.simplexProductCosimplicial (point k)).δ i) x
  let dL (i : Fin 2) : chains L q 0 :=
    transfer (reducedTorus L q) ((Cor.simplexProductCosimplicial (point L)).δ i) y
  change pull (boundary k q x) = boundary L q y
  calc
    _ = pull (dk 0 - dk 1) := congrArg pull (boundary_eq_endpoints k q x)
    _ = pull (dk 0) - pull (dk 1) := map_sub pull _ _
    _ = dL 0 - dL 1 := congrArg₂ (· - ·)
      (reducedPullback_face (k := k) (L := L) q 0 x) (reducedPullback_face (k := k) (L := L) q 1 x)
    _ = _ := (boundary_eq_endpoints L q y).symm

/-- The scalar pullback descends through the actual singular boundary. -/
def quotientFieldChange (q : ℕ) : zeroHomology k q →+ zeroHomology L q :=
  QuotientAddGroup.map (boundary k q).range (boundary L q).range
    (reducedPullback (k := k) (L := L) 0 q).hom (by
      rintro _ ⟨x, rfl⟩
      exact ⟨reducedPullback (k := k) (L := L) 1 q x, (reducedPullback_boundary q x).symm⟩)

/-- Field restriction on the original raw diagonal group along an algebra map. -/
def fieldChangeOfAlgebra (q : ℕ) :
    (motivicRawBaseComplex k q).homology q →+ (motivicRawBaseComplex L q).homology q :=
  (quotientToRawEquiv L q).toAddMonoidHom.comp
    ((quotientFieldChange (k := k) (L := L) q).comp (quotientToRawEquiv k q).symm.toAddMonoidHom)

/-- Restriction sends each literal singular class to its scalar pullback. -/
theorem fieldChangeOfAlgebra_singularClass (q : ℕ) (x : chains k q 0) :
    fieldChangeOfAlgebra (k := k) (L := L) q (singularClass k q x) =
      singularClass L q (reducedPullback (k := k) (L := L) 0 q x) := by
  rw [← quotientToRawEquiv_mk]
  change quotientToRawEquiv L q (quotientFieldChange (k := k) (L := L) q
    ((quotientToRawEquiv k q).symm (quotientToRawEquiv k q _))) = _
  rw [AddEquiv.symm_apply_apply]
  exact quotientToRawEquiv_mk L q (reducedPullback (k := k) (L := L) 0 q x)

end Algebra

/-- Field restriction on the original raw diagonal homology along any field homomorphism. -/
def fieldChange {k L : Type u} [Field k] [Field L] (φ : k →+* L) (q : ℕ) :
    (motivicRawBaseComplex k q).homology q →+ (motivicRawBaseComplex L q).homology q :=
  letI : Algebra k L := φ.toAlgebra
  fieldChangeOfAlgebra (k := k) (L := L) q

@[simp]
theorem fieldChange_algebraMap {k L : Type u} [Field k] [Field L] [Algebra k L] (q : ℕ) :
    fieldChange (algebraMap k L) q = fieldChangeOfAlgebra (k := k) (L := L) q := by
  have h : (algebraMap k L).toAlgebra = (inferInstance : Algebra k L) := toAlgebra_algebraMap
  exact congrArg (fun A : Algebra k L => @fieldChangeOfAlgebra k L _ _ A q) h

section Classes

variable {k L : Type u} [Field k] [Field L] [Algebra k L]

/-- Field restriction of a signed point class is the class of its actual whole scalar pullback. -/
theorem fieldChange_cycleClass (q : ℕ) (α : point k ⟶ DiagonalCycleSymbols.target k q) :
    fieldChange (algebraMap k L) q (cycleClass k q α) =
      cycleClass L q (pointCycleFieldChange (k := k) (L := L) q α) := by
  rw [fieldChange_algebraMap, cycleClass_apply, fieldChangeOfAlgebra_singularClass]
  let β : Cor.mk (source k 0) ⟶ Cor.mk (target k q) := WeightOne.zeroSimplexProjection k ≫ α
  have hq := reducedPullback_quotient (k := k) (L := L) 0 q β
  have hpoint := zeroProjection_cyclePullback (k := k) (L := L) q α
  have hclass := congrArg (fun z : Cor.mk (source L 0) ⟶ Cor.mk (target L q) =>
    (toReducedTorus L q).hom.app (op (Cor.mk (source L 0))) (ULift.up z)) hpoint
  exact (congrArg (singularClass L q) (hq.trans hclass)).trans
    (cycleClass_apply L q _).symm

end Classes

/-- The original raw diagonal graph symbol commutes with every field homomorphism. -/
theorem graphSymbol_fieldChange {k L : Type u} [Field k] [Field L] (φ : k →+* L)
    (q : ℕ) (a : Fin q → kˣ) :
    fieldChange φ q (graphSymbol k q a) =
      graphSymbol L q (fun i => Units.map φ.toMonoidHom (a i)) := by
  let : Algebra k L := φ.toAlgebra
  have hφ : algebraMap k L = φ := RingHom.algebraMap_toAlgebra φ
  rw [← hφ]
  simp only [graphSymbol, fieldChange_cycleClass, pointCycleFieldChange_graph]

end AlgebraicGeometry.MotivicCohomology.DiagonalFieldChange
