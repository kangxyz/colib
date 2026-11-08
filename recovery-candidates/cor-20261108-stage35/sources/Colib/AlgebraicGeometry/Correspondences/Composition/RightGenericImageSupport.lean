/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RightRemainingImage
public import Colib.AlgebraicGeometry.Correspondences.Composition.TripleGenericImageSupport

/-!
# Actual triple generic support on the whole right image

Reuse original-source genericity of the actual triple and the finite original-source
map of the right whole image. Discrete fibres reflect genericity. The right finite image
map is not asserted flat or open; F is not asserted flat over Y. This lower geometry leaf
has no Tor-family or Euler dependency. References: Stacks 0F32, 040F and 02R4; MVW Lemma 1.7,
printed page 5. Compare motivic a6805c4a87cdfd7717dd7a94039246a167f15380,
RightFirstStageWeightedRemainingCoefficient.lean, lines 214-260.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace Stacks.Chow

variable {K : Type u} [Field K] {X Y Z W : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
  (h : Z ⟶ Spec (.of K)) (i : W ⟶ Spec (.of K))
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- Original triple generics map to actual right whole-image generics. -/
theorem mem_genericPoints_correspondenceTripleToRightImageIncidence
    [Smooth f] [Smooth g] [Smooth h] [IsSeparated i] [LocallyOfFiniteType i]
    (hz : IsFiniteCorrespondencePoint f g z) (hw : IsFiniteCorrespondencePoint g h w)
    (hv : IsFiniteCorrespondencePoint h i v)
    (t : correspondenceTripleIncidence f g h i z w v)
    (ht : t ∈ genericPoints (correspondenceTripleIncidence f g h i z w v)) :
    correspondenceTripleToRightImageIncidence f g h i z w v t ∈
      genericPoints (correspondenceRightImageIncidence f g h i z w v) := by
  let := isFinite_correspondenceRightImageIncidenceSource f g h i z w v hz hw hv
  apply mem_genericPoints_of_finite_image
    (correspondenceRightImageIncidenceSource f g h i z w v)
  have hsource : correspondenceTripleToRightImageIncidence f g h i z w v ≫
      correspondenceRightImageIncidenceSource f g h i z w v =
      correspondenceTripleIncidenceSource f g h i z w v := by
    rw [← correspondenceRightImageIncidenceMap_fst, ← Category.assoc,
      correspondenceTripleToRightImageIncidence_map, correspondenceTripleIncidenceMap_fst]
  rw [← Scheme.Hom.comp_apply, hsource]
  exact mem_genericPoints_correspondenceIncidenceLeft_of_smooth f g h z w hz hw _
    (mem_genericPoints_correspondenceTripleIncidenceFst_of_smooth f g h i z w v hv t ht)

end Stacks.Chow
