/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.StalkModules
public import Colib.AlgebraicGeometry.Correspondences.Composition.AffineSupportCoordinates
public import Colib.AlgebraicGeometry.Correspondences.Composition.AffineMiddleDiagonal
public import Colib.AlgebraicGeometry.Intersection.AffineTorStalkComparison
public import Colib.Algebra.Category.ModuleCat.Tor.LocalizedMiddleDiagonal.Length

/-!
# Actual affine incidence Tor and the localized middle-diagonal comparison

The quotient ideals and support charts are constructed from the actual adjacent
integral supports. At every point of their actual incidence, the literal ambient
stalk Tor length is the middle-diagonal support Tor length at the actual triple
coordinate prime. The product support is the first Tor argument throughout.
No coordinate chart, module comparison, Tor isomorphism or finite length is
assumed. The potentially nonreduced support product is retained.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/Aglib/AlgebraicGeometry/Intersection/AffineClosedSupportTor.lean` and
`AffineMiddleTor.lean`. This is the affine all-degree length bridge, before
neighborhood globalization, Euler sums and weighted finite pushforward.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Algebra.TensorProduct.MiddleDiagonal
open scoped TensorProduct

universe u

namespace Stacks.Chow

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- The ring structure on a prime localization, projected from its commutative ring. -/
local instance affineTorAtPrimeRing {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime] :
    Ring (Localization.AtPrime p) := (inferInstance : CommRing (Localization.AtPrime p)).toRing

local notation "fA" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "fB" => Spec.map (CommRingCat.ofHom (algebraMap k B))
local notation "fC" => Spec.map (CommRingCat.ofHom (algebraMap k C))

/-- The pointwise ambient comparison for an actual product-support chart.
This lower interface retains the chart used by both sides of the final comparison. -/
theorem affineIncidenceTor_length_eq_middleSupportTor_of_supportProductChart
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC)
    (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))
    (eP : correspondenceSupportProduct fA fB fC z w ≅
      Spec (.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))))
    (hP : correspondenceSupportProductInclusion fA fB fC z w ≫
      (correspondenceAffineAmbientIso k A B C).hom =
        eP.hom ≫ Spec.map (CommRingCat.ofHom
          (ModuleCat.Tor.productQuotientMap (k := k) I J).toRingHom))
    (t : correspondenceIncidence fA fB fC z w) (n : ℕ) :
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
  let x := correspondenceIncidenceAmbientInclusion fA fB fC z w t
  let q : PrimeSpectrum (tripleRing k A B C) :=
    (correspondenceAffineTripleIso k A B C).hom
      (correspondenceIncidenceInclusion fA fB fC z w t)
  have hD := (correspondenceAffine_middleDiagonal_square k A B C).symm
  have hp : (correspondenceAffineAmbientIso k A B C).hom x =
      q.comap (quotientMap k A B C).toRingHom :=
    Scheme.affineChart_point_comap (correspondenceTripleInclusion fA fB fC)
      (correspondenceAffineAmbientIso k A B C) (correspondenceAffineTripleIso k A B C)
      (quotientMap k A B C).toRingHom hD
      (correspondenceIncidenceInclusion fA fB fC z w t)
  have h₀ := Scheme.length_torClosedStalks_eq_of_affineCharts
    (correspondenceSupportProductInclusion fA fB fC z w)
    (correspondenceTripleInclusion fA fB fC)
    (correspondenceAffineAmbientIso k A B C) eP (correspondenceAffineTripleIso k A B C)
    (ModuleCat.Tor.productQuotientMap (k := k) I J).toRingHom
    (quotientMap k A B C).toRingHom hP hD
    x (correspondenceIncidenceToSupportProduct fA fB fC z w t)
    (correspondenceIncidenceInclusion fA fB fC z w t)
    (correspondenceIncidence_ambient_point_eq fA fB fC z w t) rfl n
  rw [hp] at h₀
  let e := ModuleCat.extendScalarsTargetAtPrimeIso
    (quotientMap k A B C).toRingHom (quotientMap_surjective k A B C) q
  let M : ModuleCat (Localization.AtPrime (ambientPrime k A B C q.asIdeal)) :=
    (ModuleCat.extendScalars (R := ambientRing k A B C)
      (S := Localization.AtPrime (ambientPrime k A B C q.asIdeal))
    (algebraMap (ambientRing k A B C)
      (Localization.AtPrime (ambientPrime k A B C q.asIdeal)))).obj
      ((ModuleCat.restrictScalars (ModuleCat.Tor.productQuotientMap (k := k) I J).toRingHom).obj
        (ModuleCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
          (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))))
  have h₁ := (((Tor (ModuleCat (Localization.AtPrime (ambientPrime k A B C q.asIdeal)))
    n).obj M).mapIso e).toLinearEquiv.length_eq
  have h₂ := (h₀.trans h₁).trans
    (ModuleCat.Tor.middleDiagonalTorAtPrime_length k A B C q.asIdeal I J n)
  have hrefl :
      ((correspondenceIntersectionAmbient fA fB fC).presheaf.stalkCongr
        (.of_eq (show x = correspondenceTripleInclusion fA fB fC
          (correspondenceIncidenceInclusion fA fB fC z w t) from rfl))).hom = 𝟙 _ := by
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
    rfl
  rw [hrefl, Category.id_comp] at h₂
  exact h₂

/-- Constructed affine support ideals give the actual middle Tor length at every
incidence point and every degree over any field. Length may be infinite. -/
theorem exists_affineIncidenceTor_length_eq_middleSupportTor
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
  obtain ⟨I, J, eI, eJ, hI, hJ, eP, hP⟩ :=
    exists_correspondenceAffineSupportProductCoordinates k A B C z w
  exact ⟨I, J, affineIncidenceTor_length_eq_middleSupportTor_of_supportProductChart
    k A B C z w I J eP hP⟩

end Stacks.Chow
