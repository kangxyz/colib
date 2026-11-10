/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.TorusIdentityAxisIntegral
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# The actual weight-one cokernel on integral sources

The existing `reducedTorus` is retained literally. Its evaluated quotient map
kills precisely the integer multiples of the actual canonical identity graph.
This is independent of any affine-coordinate choice or determinant norm.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/Cohomology/WeightOne/Geometry/ReducedTorusExact.lean:150-193`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable {k : Type u} [Field k]

/-- Weight one has exactly the image of its unique actual identity-axis map. -/
theorem torusIdentityRelations_one (X : Cor k) :
    torusIdentityRelations k 1 X = ((torusIdentityAxis k 1 0).hom.app (op X)).hom.range := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact le_of_eq (congrArg
      (fun j => ((torusIdentityAxis k 1 j).hom.app (op X)).hom.range)
      (Subsingleton.elim i 0))
  · exact le_iSup (fun i => ((torusIdentityAxis k 1 i).hom.app (op X)).hom.range) 0

/-- The relation subgroup is the genuine cyclic graph subgroup, with all signed coefficients. -/
theorem mem_torusIdentityRelations_one_iff (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] (z : sections (torusRepresentable k 1) (Cor.mk X)) :
    z ∈ torusIdentityRelations k 1 (Cor.mk X) ↔
      ∃ n : ℤ, z = ULift.up (n • torusIdentityGraph k X) := by
  rw [torusIdentityRelations_one]
  exact mem_range_torusIdentityAxis_one_iff k X z

/-- The canonical quotient kills the genuine constant-one graph. -/
@[simp] theorem toReducedTorus_identityGraph (X : SmoothSite (Spec (.of k))) :
    (toReducedTorus k 1).hom.app (op (Cor.mk X))
      (ULift.up (torusIdentityGraph k X)) = 0 := by
  have h := congrArg (fun η => η.hom.app (op (Cor.mk X))
    (ULift.up ((Cor.graphFunctor k).map (structureMorphism X))))
      (torusIdentityAxis_toReducedTorus k 1 0)
  change (toReducedTorus k 1).hom.app (op (Cor.mk X))
    (ULift.up ((Cor.graphFunctor k).map (structureMorphism X) ≫
      (Cor.graphFunctor k).map (torusInsertOne (Spec (.of k)) 0 0))) = 0 at h
  simpa only [torusIdentityGraph, Functor.map_comp] using h

/-- No additional relation is introduced by the existing presheaf cokernel. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightOne/Geometry/ReducedTorusExact.lean:170-193"
  "adaptation" "The kernel of the actual evaluated weight-one cokernel is the identity graph"]
theorem toReducedTorus_eq_zero_iff_identityGraph (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] (z : sections (torusRepresentable k 1) (Cor.mk X)) :
    (toReducedTorus k 1).hom.app (op (Cor.mk X)) z = 0 ↔
      ∃ n : ℤ, z = ULift.up (n • torusIdentityGraph k X) := by
  constructor
  · intro hz
    let E := (evaluation (Cor k)ᵒᵖ AddCommGrpCat.{u + 1}).obj (op (Cor.mk X))
    have hex := (ShortComplex.cokernelSequence_exact (torusRelation k 1)).map E
    obtain ⟨s, hs⟩ := (ShortComplex.ab_exact_iff _).mp hex z hz
    have hr : z ∈ ((torusRelation k 1).app (op (Cor.mk X))).hom.range := ⟨s, hs⟩
    rw [range_torusRelation] at hr
    exact (mem_torusIdentityRelations_one_iff X z).mp hr
  · rintro ⟨n, rfl⟩
    change (toReducedTorus k 1).hom.app (op (Cor.mk X))
      (n • ULift.up (torusIdentityGraph k X)) = 0
    rw [map_zsmul, toReducedTorus_identityGraph, smul_zero]

/-- Adding any signed identity graph leaves the original reduced section unchanged. -/
theorem toReducedTorus_add_identityGraph (X : SmoothSite (Spec (.of k)))
    (z : Cor.mk X ⟶ Cor.mk (torusPower (Spec (.of k)) 1)) (n : ℤ) :
    (toReducedTorus k 1).hom.app (op (Cor.mk X))
        (ULift.up (z + n • torusIdentityGraph k X)) =
      (toReducedTorus k 1).hom.app (op (Cor.mk X)) (ULift.up z) := by
  change (toReducedTorus k 1).hom.app (op (Cor.mk X))
    (ULift.up z + n • ULift.up (torusIdentityGraph k X)) = _
  rw [map_add, map_zsmul, toReducedTorus_identityGraph, smul_zero, add_zero]

end AlgebraicGeometry.PresheafWithTransfers
