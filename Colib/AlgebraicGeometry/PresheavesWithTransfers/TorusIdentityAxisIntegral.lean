/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.BaseChange.IntegralSource
public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorus

/-!
# The actual weight-one identity axis on integral sources

An arbitrary signed correspondence from an integral smooth scheme to the base
is its actual structure-graph coefficient times that graph. Postcomposition
with the weight-one identity axis therefore has image exactly the integer
multiples of the genuine constant-one graph. The target stays the existing
relative first torus power, and the coefficient group stays in universe `u + 1`.
After the already chosen `torusPowerOneIso`, this is the graph of the actual
unit-one section of the native multiplicative group.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/Cohomology/WeightOne/Geometry/TorusNormRelation.lean:40-97`.
This supplies its structure-graph and identity-axis geometry. It does not
assert the missing affine divisor norm or its vanishing on the unit-one graph.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Chow

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The original structure morphism retained inside the actual smooth site. -/
def structureMorphism {S : Scheme.{u}} (X : SmoothSite S) : X ⟶ base S :=
  homMk X.hom (Category.comp_id _)

end AlgebraicGeometry.Scheme.SmoothSite

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable {k : Type u} [Field k]

/-- On an integral smooth source, the actual graph sum is the structure prime cycle. -/
theorem graph_structureMorphism (X : SmoothSite (Spec (.of k))) [IsIntegral X.left] :
    (graphFunctor k).map (structureMorphism X) =
      structureGraphCorrespondence (X := X.left) X.hom := by
  change graphCorrespondenceOfComponents X.hom (𝟙 (Spec (.of k))) X.hom
    (Category.comp_id X.hom) (finite_genericPoints k (Cor.mk X)) = _
  exact graphCorrespondenceOfComponents_structure (X := X.left) X.hom _

/-- Every signed correspondence to the base retains its actual structure-graph coefficient. -/
theorem baseCorrespondence_eq_coeff_zsmul (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] (a : Cor.mk X ⟶ Cor.mk (base (Spec (.of k)))) :
    a = structureCorrespondenceCoeff (X := X.left) X.hom a •
      (graphFunctor k).map (structureMorphism X) := by
  rw [graph_structureMorphism]
  exact eq_coeff_zsmul_structureGraph (X := X.left) X.hom a

/-- Postcomposition with a point of a smooth target retains the original integer coefficient. -/
theorem baseCorrespondence_comp_graph (X Y : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] (a : Cor.mk X ⟶ Cor.mk (base (Spec (.of k))))
    (s : base (Spec (.of k)) ⟶ Y) :
    a ≫ (graphFunctor k).map s =
      structureCorrespondenceCoeff (X := X.left) X.hom a •
        (graphFunctor k).map (structureMorphism X ≫ s) := by
  calc
    a ≫ (graphFunctor k).map s =
        (structureCorrespondenceCoeff (X := X.left) X.hom a •
          (graphFunctor k).map (structureMorphism X)) ≫ (graphFunctor k).map s :=
      congrArg (fun b => b ≫ (graphFunctor k).map s)
        (baseCorrespondence_eq_coeff_zsmul X a)
    _ = structureCorrespondenceCoeff (X := X.left) X.hom a •
        ((graphFunctor k).map (structureMorphism X) ≫ (graphFunctor k).map s) :=
      Preadditive.zsmul_comp _ _ _
    _ = _ := by rw [← Functor.map_comp]

end AlgebraicGeometry.Cor

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k]

/-- The actual constant-one graph with target the existing first torus power. -/
def torusIdentityGraph (X : SmoothSite (Spec (.of k))) :
    Cor.mk X ⟶ Cor.mk (torusPower (Spec (.of k)) 1) :=
  (Cor.graphFunctor k).map (structureMorphism X ≫ torusInsertOne (Spec (.of k)) 0 0)

/-- The existing first-power comparison carries this graph to the actual unit-one graph. -/
@[reassoc]
theorem torusIdentityGraph_powerOneIso (X : SmoothSite (Spec (.of k))) :
    torusIdentityGraph k X ≫
        (Cor.graphFunctor k).map (torusPowerOneIso (Spec (.of k))).hom =
      (Cor.graphFunctor k).map (structureMorphism X ≫ torusOne (Spec (.of k))) := by
  rw [torusIdentityGraph, ← Functor.map_comp, Category.assoc,
    torusInsertOne_zero_powerOneIso]

/-- The large-coefficient identity-axis map is the actual signed graph-coefficient formula. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/Cohomology/WeightOne/Geometry/TorusNormRelation.lean:45-62,87-98"
  "adaptation" "The actual identity-axis cycle retains the structure-graph integer coefficient"]
theorem torusIdentityAxis_one_app_eq_coeff (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] (a : Cor.mk X ⟶ Cor.mk (base (Spec (.of k)))) :
    (torusIdentityAxis k 1 0).hom.app (op (Cor.mk X)) (ULift.up a) =
      ULift.up (structureCorrespondenceCoeff (X := X.left) X.hom a • torusIdentityGraph k X) := by
  rw [torusIdentityAxis_app_apply]
  exact congrArg ULift.up
    (Cor.baseCorrespondence_comp_graph X (torusPower (Spec (.of k)) 1) a
      (torusInsertOne (Spec (.of k)) 0 0))

/-- Exactly the integer multiples of the genuine identity graph occur in the axis image. -/
theorem mem_range_torusIdentityAxis_one_iff (X : SmoothSite (Spec (.of k)))
    [IsIntegral X.left] (z : sections (torusRepresentable k 1) (Cor.mk X)) :
    z ∈ ((torusIdentityAxis k 1 0).hom.app (op (Cor.mk X))).hom.range ↔
      ∃ n : ℤ, z = ULift.up (n • torusIdentityGraph k X) := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨structureCorrespondenceCoeff (X := X.left) X.hom a.down,
      ha.symm.trans (torusIdentityAxis_one_app_eq_coeff k X a.down)⟩
  · rintro ⟨n, rfl⟩
    refine ⟨ULift.up (n • (Cor.graphFunctor k).map (structureMorphism X)), ?_⟩
    rw [torusIdentityAxis_one_app_eq_coeff]
    simp only [map_zsmul, Cor.graph_structureMorphism, structureCorrespondenceCoeff_graph,
      zsmul_eq_mul, mul_one, Int.cast_id]

end AlgebraicGeometry.PresheafWithTransfers
