/- Recovery reconstruction scope test. Uncompiled. -/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.GlobalActualTorComparison

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow

universe u

-- The statement retains arbitrary schemes and arbitrary fields. In particular it
-- adds no smoothness, nonemptiness, integrality, connectedness or finite-length assumptions.
example (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
    (z : pullback f g) (w : pullback g h)
    (t : correspondenceIncidence f g h z w) (n : ℕ) :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t))
      (((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t))) n).obj
        (correspondenceIncidenceSupportStalkModule f g h z w t)).obj
        (correspondenceIncidenceTripleStalkModule f g h z w t)) =
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z w t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z w t)) :=
  incidenceTor_length_eq_pulledStalkTor k f g h z w t n

#check exists_openIntegralComponentAt
#check CorrespondenceOpenNeighborhoods.incidenceMap_inclusion
#check CorrespondenceOpenNeighborhoods.incidenceTor_length_eq_open
#check CorrespondenceOpenNeighborhoods.pulledTor_length_eq_open
#check incidenceTor_length_eq_pulledStalkTor
