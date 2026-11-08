/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.StalkModules
public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.IntersectionIdeal

/-!
# The scheme-theoretic ambient intersection of correspondence supports

The incidence scheme is the actual pullback of the support product and the
middle diagonal inside the four-factor ambient product. When the middle
structure map is separated, the actual kernel ideal of the incidence closed
immersion is exactly the sum of those two ideals. This identifies the full
scheme structure and preserves nilpotents, without defining an intersection
cycle or asserting a Tor-vanishing property.

Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Correspondences/Composition/Intersection/AmbientIdeal.lean,
Git blob 0dc9977c3d22fe9ad458ba66699e99de485b9d8f. The existing native
integralComponentAt supports replace the original generator wrapper.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow
open AlgebraicGeometry.Scheme.Hom

variable {S X Y Z : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The actual incidence scheme is the Cartesian intersection in the ambient product. -/
theorem isPullback_correspondenceAmbientIncidence :
    IsPullback (correspondenceIncidenceInclusion f g h z w)
      (correspondenceIncidenceToSupportProduct f g h z w)
      (correspondenceTripleInclusion f g h) (correspondenceSupportProductInclusion f g h z w) where
  w := (correspondenceIncidence_ambient_comm f g h z w)
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    have ha := congrArg
      (fun k => k ≫ pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g))
      s.condition
    have hb := congrArg
      (fun k => k ≫ pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g))
      s.condition
    simp only [Category.assoc, correspondenceTripleInclusion_fst,
      correspondenceSupportProductInclusion_fst] at ha
    simp only [Category.assoc, correspondenceTripleInclusion_snd,
      correspondenceSupportProductInclusion_snd] at hb
    have hab :
        (s.snd ≫ pullback.fst (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
          (((integralComponentAt w).subschemeι ≫ pullback.fst g h) ≫ g)) ≫
          ((integralComponentAt z).subschemeι ≫ pullback.snd f g) =
        (s.snd ≫ pullback.snd (((integralComponentAt z).subschemeι ≫ pullback.snd f g) ≫ g)
          (((integralComponentAt w).subschemeι ≫ pullback.fst g h) ≫ g)) ≫
          ((integralComponentAt w).subschemeι ≫ pullback.fst g h) := by
      change (s.snd ≫ pullback.fst _ _) ≫ ((integralComponentAt z).subschemeι ≫ pullback.snd f g) =
        (s.snd ≫ pullback.snd _ _) ≫ ((integralComponentAt w).subschemeι ≫ pullback.fst g h)
      simp only [Category.assoc]
      calc
        _ = s.fst ≫ pullback.fst (pullback.snd f g) (pullback.fst g h) ≫
            pullback.snd f g := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ pullback.snd f g) ha.symm
        _ = s.fst ≫ pullback.snd (pullback.snd f g) (pullback.fst g h) ≫
            pullback.fst g h := by rw [pullback.condition]
        _ = _ := by
          simpa only [Category.assoc] using
            congrArg (fun k => k ≫ pullback.fst g h) hb
    let liftIncidence : s.pt ⟶ (correspondenceIncidence f g h z w) := pullback.lift
      (s.snd ≫ pullback.fst _ _) (s.snd ≫ pullback.snd _ _) hab
    have hw₁ : liftIncidence ≫ (correspondenceIncidenceInclusion f g h z w) = s.fst := by
      apply pullback.hom_ext
      · simpa only [liftIncidence, Category.assoc, correspondenceIncidenceInclusion_fst,
        pullback.lift_fst_assoc] using ha.symm
      · simpa only [liftIncidence, Category.assoc, correspondenceIncidenceInclusion_snd,
        pullback.lift_snd_assoc] using hb.symm
    have hw₂ : liftIncidence ≫ (correspondenceIncidenceToSupportProduct f g h z w) = s.snd := by
      apply pullback.hom_ext
      · rw [Category.assoc, correspondenceIncidenceToSupportProduct_fst]
        exact pullback.lift_fst _ _ _
      · rw [Category.assoc, correspondenceIncidenceToSupportProduct_snd]
        exact pullback.lift_snd _ _ _
    refine ⟨liftIncidence, hw₁, hw₂, ?_⟩
    intro m hm _
    exact (cancel_mono (correspondenceIncidenceInclusion f g h z w)).mp (hm.trans hw₁.symm))⟩

/-- The actual incidence ideal in the ambient product is the sum of the diagonal
pullback ideal and the support-product ideal. -/
theorem correspondenceIncidenceAmbientInclusion_ker [IsSeparated g] :
    (correspondenceIncidenceAmbientInclusion f g h z w).ker =
      (correspondenceTripleInclusion f g h).ker ⊔ (correspondenceSupportProductInclusion f g h z
        w).ker :=
  ker_comp_eq_sup_of_isPullback _ _ _ _ ((isPullback_correspondenceAmbientIncidence f g h z w))

end Stacks.Chow
