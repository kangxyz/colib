/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

import Colib.AlgebraicGeometry.Correspondences.Principal.GraphIncidenceStalkTor

/-!
# Graph incidence to literal endpoint stalk regression tests

The comparisons hold in every Tor degree, do not assume support flatness,
and preserve full module length. Residue restriction also permits infinite
length and does not require surjectivity of the ambient local ring map.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

example {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f]
    (hf : Function.Surjective (IsLocalRing.ResidueField.map f)) (M : ModuleCat S) :
    Module.length R ((ModuleCat.restrictScalars f).obj M) = Module.length S M :=
  ModuleCat.length_restrictScalars_of_residue_surjective f hf M

section Geometry

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
    [IsIntegral X] [IsSeparated g] (φ : X ⟶ Y) (hφ : φ ≫ g = f)
    (s : genericPoints X)

-- No flatness of φ or integral support is needed for the full graph-pullback isomorphism.
example : IsIso
    (Stacks.Chow.correspondenceLeftPulledInclusion f g h
      (Stacks.Chow.correspondenceGraphMap f g φ hφ s.val) ≫
      Stacks.Chow.correspondenceTripleOuterProjection f g h) :=
  Stacks.Chow.isIso_leftGraphPulled_outerProjection f g h φ hφ s

-- Closed endpoint maps, rather than flat maps, give the residue-field comparison.
example [IsClosedImmersion φ] : IsClosedImmersion
    (Stacks.Chow.correspondenceLeftPulledInclusion f g h
      (Stacks.Chow.correspondenceGraphMap f g φ hφ s.val) ≫
      pullback.snd (pullback.snd f g) (pullback.fst g h)) :=
  Stacks.Chow.leftGraphPulled_rightProjection_closed f g h φ hφ s

open Stacks.Chow in
-- The Tor degree is unrestricted and neither original integral support is assumed flat.
example [Flat f] [IsClosedImmersion φ] (w : pullback (C := Scheme) g h)
    (t : correspondenceIncidence f g h (correspondenceGraphMap f g φ hφ s.val) w)
    (n : ℕ) :
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h (correspondenceGraphMap f g φ hφ s.val) w t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
        (correspondenceIncidenceInclusion f g h
          (correspondenceGraphMap f g φ hφ s.val) w t))) (n + 2)).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h
          (correspondenceGraphMap f g φ hφ s.val) w t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h
          (correspondenceGraphMap f g φ hφ s.val) w t)) =
    Module.length ((pullback g h).presheaf.stalk
      (pullback.snd (pullback.snd f g) (pullback.fst g h)
        (correspondenceIncidenceInclusion f g h
          (correspondenceGraphMap f g φ hφ s.val) w t)))
      (((Tor (ModuleCat ((pullback g h).presheaf.stalk
        (pullback.snd (pullback.snd f g) (pullback.fst g h)
          (correspondenceIncidenceInclusion f g h
            (correspondenceGraphMap f g φ hφ s.val) w t)))) (n + 2)).obj
        (leftGraphEndpointStalkModule f g h φ hφ s
          (correspondenceIncidenceInclusion f g h
            (correspondenceGraphMap f g φ hφ s.val) w t)
          (correspondenceIncidenceToLeftPulled f g h
            (correspondenceGraphMap f g φ hφ s.val) w t)
          (correspondenceIncidence_leftPulled_point_eq f g h
            (correspondenceGraphMap f g φ hφ s.val) w t))).obj
        (graphIncidenceOriginalSupportStalkModule f g h φ hφ s w t)) :=
  graphPulledStalkTor_length_eq_endpointStalkTor f g h φ hφ s w t (n + 2)

end Geometry

#print axioms ModuleCat.length_restrictScalars_of_residue_surjective
#print axioms Scheme.Hom.comapStalkIsoExtendScalarsOfEq
#print axioms Scheme.Hom.comapStalkTorIsoOfFlat
#print axioms Scheme.Hom.length_restrictScalars_stalkMap_of_preimmersion_comp
#print axioms Scheme.Hom.comapStalkTor_length_of_flat
#print axioms Stacks.Chow.leftGraphPulledOuterIso
#print axioms Stacks.Chow.leftGraphPulledOuterIso_ambient
#print axioms Stacks.Chow.leftGraphPulledStalkIso
#print axioms Stacks.Chow.graphPulledStalkTor_length_eq_endpointStalkTor

#print axioms Stacks.Chow.graphIncidenceTor_length_eq_endpointStalkTor
