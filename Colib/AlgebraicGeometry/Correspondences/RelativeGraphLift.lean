/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.Graph.FiniteSupportPushforward
public import Colib.AlgebraicGeometry.Correspondences.Graph.TargetPushforward
public import Colib.AlgebraicGeometry.Sites.Smooth.Products

/-!
# Canonical relative graph lifts of finite correspondences

Push original signed primes along the actual closed relative graph, keeping
the source projection unchanged. No graph-base-change naturality is asserted.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor
namespace RelativeGraph
variable (k : Type u) [Field k]
variable (U Y : SmoothSite (Spec (CommRingCat.of k)))
local notation "B" => SmoothSite.product U Y

/-- Native graph of the source projection, followed by native pullback symmetry:
(u,y) |-> (u,(u,y)). -/
def ambientLift : (B).left ⟶ pullback U.hom (B).hom :=
  pullback.lift (𝟙 (B).left) (pullback.fst U.hom Y.hom)
    (Category.id_comp ((pullback.fst U.hom Y.hom) ≫ U.hom)) ≫
      (pullbackSymmetry (B).hom U.hom).hom

/-- The graph is closed because the source structure map is separated. -/
instance ambientLift_isClosedImmersion : IsClosedImmersion (ambientLift k U Y) := by
  unfold ambientLift
  infer_instance

/-- The source map is literally unchanged, preserving admissibility. -/
@[reassoc (attr := simp)]
theorem ambientLift_fst :
    ambientLift k U Y ≫ pullback.fst U.hom (pullback.fst U.hom Y.hom ≫ U.hom) =
    pullback.fst U.hom Y.hom := by
  simp only [ambientLift, Category.assoc, SmoothSite.product_hom, pullbackSymmetry_hom_comp_fst]
  exact pullback.lift_snd _ _ _

/-- Forgetting the new source coordinate recovers the identical old support. -/
@[reassoc (attr := simp)]
theorem ambientLift_snd :
    ambientLift k U Y ≫ pullback.snd U.hom (pullback.fst U.hom Y.hom ≫ U.hom) =
    𝟙 (B).left := by
  simp only [ambientLift, Category.assoc, SmoothSite.product_hom, pullbackSymmetry_hom_comp_snd]
  exact pullback.lift_fst _ _ _

/-- Native finite-map image admissibility, using the unchanged source map. -/
theorem image_admissible (z : pullback (C := Scheme) U.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint U.hom Y.hom z) :
    IsFiniteCorrespondencePoint U.hom (B).hom (ambientLift k U Y z) := by
  apply isFiniteCorrespondencePoint_finiteMap U.hom (B).hom (ambientLift k U Y) z
  · simpa only [Category.assoc, SmoothSite.product_hom, ambientLift_fst] using hz.1
  · simpa only [Category.assoc, SmoothSite.product_hom, ambientLift_fst] using hz.2

/-- Canonical additive lift. Each actual point maps to its closed-immersion
image, with the same integer coefficient (residue degree is one). -/
def relativeGraphLift : (Cor.mk U ⟶ Cor.mk Y) →+
    (Cor.mk U ⟶ Cor.mk B) :=
  liftFiniteCorrespondence U.hom Y.hom fun z hz =>
    singleFiniteCorrespondence U.hom (B).hom (ambientLift k U Y z)
      (image_admissible k U Y z hz) 1

/-- No existential choice: on each original signed prime this is its literal
closed-immersion image with precisely the original coefficient. -/
theorem relativeGraphLift_single (z : pullback (C := Scheme) U.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint U.hom Y.hom z) (m : ℤ) :
    relativeGraphLift k U Y (singleFiniteCorrespondence U.hom Y.hom z hz m) =
      m • singleFiniteCorrespondence U.hom (B).hom (ambientLift k U Y z)
        (image_admissible k U Y z hz) 1 :=
  liftFiniteCorrespondence_single U.hom Y.hom _ z hz m

end RelativeGraph
end AlgebraicGeometry.Cor
