module

import Colib.AlgebraicGeometry.Correspondences.Composition.AffineTorComparison

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open Algebra.TensorProduct.MiddleDiagonal
open scoped TensorProduct

noncomputable section

universe u

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

local instance {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Ring (Localization.AtPrime p) := (inferInstance : CommRing (Localization.AtPrime p)).toRing

local notation "fA" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "fB" => Spec.map (CommRingCat.ofHom (algebraMap k B))
local notation "fC" => Spec.map (CommRingCat.ofHom (algebraMap k C))

example
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC) :
    ∃ I : Ideal (A ⊗[k] B), ∃ J : Ideal (B ⊗[k] C),
    ∀ (t : correspondenceIncidence fA fB fC z w) (n : ℕ),
      Module.length
        ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
          (correspondenceIncidenceAmbientInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
            (correspondenceIncidenceAmbientInclusion fA fB fC z w t))) n).obj
          (correspondenceIncidenceSupportStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceTripleStalkModule fA fB fC z w t)) =
      Module.length (Localization.AtPrime
        ((correspondenceAffineTripleIso k A B C).hom
          (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal)
        (ModuleCat.Tor.middleSupportTorAtPrime k A B C
          ((correspondenceAffineTripleIso k A B C).hom
            (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal I J n) := by
  exact exists_affineIncidenceTor_length_eq_middleSupportTor k A B C z w

example
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC) :
    ∃ I : Ideal (A ⊗[k] B), ∃ J : Ideal (B ⊗[k] C),
    ∀ (t : correspondenceIncidence fA fB fC z w) ,
      Module.length
        ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
          (correspondenceIncidenceAmbientInclusion fA fB fC z w t))
        (((Tor (ModuleCat ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalk
            (correspondenceIncidenceAmbientInclusion fA fB fC z w t))) 0).obj
          (correspondenceIncidenceSupportStalkModule fA fB fC z w t)).obj
          (correspondenceIncidenceTripleStalkModule fA fB fC z w t)) =
      Module.length (Localization.AtPrime
        ((correspondenceAffineTripleIso k A B C).hom
          (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal)
        (ModuleCat.Tor.middleSupportTorAtPrime k A B C
          ((correspondenceAffineTripleIso k A B C).hom
            (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal I J 0) := by
  obtain ⟨I, J, h⟩ := exists_affineIncidenceTor_length_eq_middleSupportTor k A B C z w
  exact ⟨I, J, fun t => h t 0⟩
