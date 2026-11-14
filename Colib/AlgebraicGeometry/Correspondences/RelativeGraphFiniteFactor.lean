/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module
public import Colib.AlgebraicGeometry.Correspondences.RelativeGraphIncidenceOver

/-! # Finiteness of the canonical relative graph incidence factor -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme Stacks.Chow
universe u
namespace AlgebraicGeometry.Cor.RelativeGraph
variable (k : Type u) [Field k]
variable {V U Y : SmoothSite (Spec (CommRingCat.of k))} (f : V ⟶ U)

/-- Forgetting the retained coordinate on the original incidence is finite.
The proof uses the actual closed factorization, not flatness of the source map. -/
theorem isFinite_incidenceForget (s : genericPoints V.left)
    (z : pullback (C := Scheme) U.hom Y.hom)
    (hz : IsFiniteCorrespondencePoint U.hom Y.hom z) :
    IsFinite (correspondenceIncidenceMap V.hom U.hom (SmoothSite.product U Y).hom
      (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s.val)
      (ambientLift k U Y z) ≫ ambientForget k) := by
  let m := correspondenceIncidenceMap V.hom U.hom (SmoothSite.product U Y).hom
    (correspondenceGraphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s.val)
    (ambientLift k U Y z)
  have hm : IsFinite m := isFinite_correspondenceIncidenceMap
    V.hom U.hom (SmoothSite.product U Y).hom _ _
    (isFiniteCorrespondencePoint_graphMap V.hom U.hom f.left (MorphismProperty.Over.w f) s)
    (image_admissible k U Y z hz)
  have : IsFinite ((m ≫ ambientForget k) ≫ ambientOver k (Y := Y) f) := by
    rw [incidenceMap_factor_over]
    exact hm
  exact IsFinite.of_comp (m ≫ ambientForget k) (ambientOver k (Y := Y) f)

end AlgebraicGeometry.Cor.RelativeGraph
