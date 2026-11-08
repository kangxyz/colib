module

import Colib.AlgebraicGeometry.Correspondences.Composition.AffineActualTorComparison

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Algebra.TensorProduct.MiddleDiagonal
open scoped TensorProduct

universe u

open Stacks.Chow

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

local instance affineActualTorTestAtPrimeRing {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Ring (Localization.AtPrime p) := (inferInstance : CommRing (Localization.AtPrime p)).toRing

local notation "fA" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "fB" => Spec.map (CommRingCat.ofHom (algebraMap k B))
local notation "fC" => Spec.map (CommRingCat.ofHom (algebraMap k C))

example
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC)
    (t : correspondenceIncidence fA fB fC z w) (n : ℕ) :
      Module.length
        ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
          (correspondenceIncidenceAmbientInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
            (correspondenceIncidenceAmbientInclusion fA fB fC z w t))) n).obj
          (correspondenceIncidenceSupportStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceTripleStalkModule fA fB fC z w t)) =
      Module.length ((correspondenceTripleProduct fA fB fC).presheaf.stalk
        (correspondenceIncidenceInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceTripleProduct fA fB fC).presheaf.stalk
            (correspondenceIncidenceInclusion fA fB fC z w t))) n).obj
          (correspondenceIncidenceLeftPulledStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceRightPulledStalkModule fA fB fC z w t)) := by
  exact affineIncidenceTor_length_eq_pulledStalkTor k A B C z w t n

example
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC)
    (t : correspondenceIncidence fA fB fC z w) :
      Module.length
        ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
          (correspondenceIncidenceAmbientInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
            (correspondenceIncidenceAmbientInclusion fA fB fC z w t))) 0).obj
          (correspondenceIncidenceSupportStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceTripleStalkModule fA fB fC z w t)) =
      Module.length ((correspondenceTripleProduct fA fB fC).presheaf.stalk
        (correspondenceIncidenceInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceTripleProduct fA fB fC).presheaf.stalk
            (correspondenceIncidenceInclusion fA fB fC z w t))) 0).obj
          (correspondenceIncidenceLeftPulledStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceRightPulledStalkModule fA fB fC z w t)) := by
  exact affineIncidenceTor_length_eq_pulledStalkTor k A B C z w t 0

example
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC)
    (t : correspondenceIncidence fA fB fC z w) (n : ℕ) :
      Module.length
        ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
          (correspondenceIncidenceAmbientInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
            (correspondenceIncidenceAmbientInclusion fA fB fC z w t))) n).obj
          (correspondenceIncidenceSupportStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceTripleStalkModule fA fB fC z w t)) < ⊤ ↔
      Module.length ((correspondenceTripleProduct fA fB fC).presheaf.stalk
        (correspondenceIncidenceInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceTripleProduct fA fB fC).presheaf.stalk
            (correspondenceIncidenceInclusion fA fB fC z w t))) n).obj
          (correspondenceIncidenceLeftPulledStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceRightPulledStalkModule fA fB fC z w t)) < ⊤ := by
  rw [affineIncidenceTor_length_eq_pulledStalkTor k A B C z w t n]
