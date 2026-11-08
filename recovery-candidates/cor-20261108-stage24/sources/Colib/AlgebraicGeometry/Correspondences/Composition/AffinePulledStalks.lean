/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.AffinePulledSupports
public import Colib.AlgebraicGeometry.Correspondences.Composition.PulledStalkModules
public import Colib.AlgebraicGeometry.Intersection.AffineTensorStalkModules
public import StacksFrontier.Homology.Tor.Independence
public import Colib.Algebra.Category.ModuleCat.Tor.LocalizedMiddleDiagonal.Length

/-!
# The actual pulled-support stalks and localized middle-support Tor

Each literal pulled-support stalk is identified with the existing scalar-extended
quotient module over the triple-coordinate prime. Its scalar action is derived
from the actual chart square. Native scalar-extension composition identifies the
localized tensor-product ring with the original quotient extended along the
specified localized adjacent map. The right action is explicitly `rightMap`.

Consequently, native Tor of the actual two pulled-support stalks has the existing
`middleSupportTorAtPrime` length in every degree. The left support remains first.
The full pulled scheme structures are retained, with no support flatness or
finite-length assumption.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/Aglib/AlgebraicGeometry/Intersection/AffineMiddleTor.lean`,
`pulledStalkTor` and `stalkTor_length`, and
`Motivic/Aglib/Algebra/Category/ModuleCat/Tor/SupportModulesMiddle.lean`.
The lower statements take actual quotient chart squares; the final two-sided
comparison constructs those charts from the actual adjacent closed supports.
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

local instance affinePulledStalkAtPrimeRing {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] :
    Ring (Localization.AtPrime p) := (inferInstance : CommRing (Localization.AtPrime p)).toRing

local notation "fA" => Spec.map (CommRingCat.ofHom (algebraMap k A))
local notation "fB" => Spec.map (CommRingCat.ofHom (algebraMap k B))
local notation "fC" => Spec.map (CommRingCat.ofHom (algebraMap k C))



/-- The actual left pulled stalk is the left middle-support module, with its actual action. -/
def correspondenceAffineLeftPulledStalkModuleIso
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC)
    (I : Ideal (A ⊗[k] B))
    (eI : (integralComponentAt (X := pullback (C := Scheme) fA fB) z).subscheme ≅
      Spec (.of ((A ⊗[k] B) ⧸ I)))
    (hI : (integralComponentAt (X := pullback (C := Scheme) fA fB) z).subschemeι ≫
      (pullbackSpecIso k A B).hom =
      eI.hom ≫ Spec.map (CommRingCat.ofHom (R := A ⊗[k] B)
        (S := (A ⊗[k] B) ⧸ I) (Ideal.Quotient.mk I)))
    (t : correspondenceIncidence fA fB fC z w) :
    correspondenceIncidenceLeftPulledStalkModule fA fB fC z w t ≅
      (ModuleCat.restrictScalars
        (Scheme.stalkIsoOfAffineChart (correspondenceAffineTripleIso k A B C)
          (correspondenceIncidenceInclusion fA fB fC z w t)).hom.hom).obj
        ((ModuleCat.extendScalars (localizedLeftMap k A B C
          ((correspondenceAffineTripleIso k A B C).hom
            (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal).toRingHom).obj
          (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I))) := by
  exact Scheme.closedImmersionTensorStalkModuleIsoOfAffineChartOfEq
    (R := A ⊗[k] B) (S := tripleRing k A B C) (T := (A ⊗[k] B) ⧸ I)
    (correspondenceLeftPulledInclusion fA fB fC z)
    (correspondenceAffineTripleIso k A B C)
    (correspondenceAffineLeftPulledIso k A B C z I eI hI)
    (correspondenceAffineLeftPulledIso_inclusion k A B C z I eI hI).symm
    (correspondenceIncidenceToLeftPulled fA fB fC z w t)
    (correspondenceIncidenceInclusion fA fB fC z w t)
    (correspondenceIncidence_leftPulled_point_eq fA fB fC z w t)

/-- The actual right pulled stalk is the right middle-support module, with its actual action. -/
def correspondenceAffineRightPulledStalkModuleIso
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC)
    (J : Ideal (B ⊗[k] C))
    (eJ : (integralComponentAt (X := pullback (C := Scheme) fB fC) w).subscheme ≅
      Spec (.of ((B ⊗[k] C) ⧸ J)))
    (hJ : (integralComponentAt (X := pullback (C := Scheme) fB fC) w).subschemeι ≫
      (pullbackSpecIso k B C).hom =
      eJ.hom ≫ Spec.map (CommRingCat.ofHom (R := B ⊗[k] C)
        (S := (B ⊗[k] C) ⧸ J) (Ideal.Quotient.mk J)))
    (t : correspondenceIncidence fA fB fC z w) :
    correspondenceIncidenceRightPulledStalkModule fA fB fC z w t ≅
      (ModuleCat.restrictScalars
        (Scheme.stalkIsoOfAffineChart (correspondenceAffineTripleIso k A B C)
          (correspondenceIncidenceInclusion fA fB fC z w t)).hom.hom).obj
        ((ModuleCat.extendScalars (localizedRightMap k A B C
          ((correspondenceAffineTripleIso k A B C).hom
            (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal).toRingHom).obj
          (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J))) := by
  letI : Algebra (B ⊗[k] C) (tripleRing k A B C) := (rightMap k A B C).toRingHom.toAlgebra
  exact Scheme.closedImmersionTensorStalkModuleIsoOfAffineChartOfEq
    (R := B ⊗[k] C) (S := tripleRing k A B C) (T := (B ⊗[k] C) ⧸ J)
    (correspondenceRightPulledInclusion fA fB fC w)
    (correspondenceAffineTripleIso k A B C)
    (correspondenceAffineRightPulledIso k A B C w J eJ hJ)
    (correspondenceAffineRightPulledIso_inclusion k A B C w J eJ hJ).symm
    (correspondenceIncidenceToRightPulled fA fB fC z w t)
    (correspondenceIncidenceInclusion fA fB fC z w t)
    (correspondenceIncidence_rightPulled_point_eq fA fB fC z w t)

/-- The actual triple-stalk Tor is the existing middle-support Tor in its actual chart. -/
def correspondenceAffinePulledStalkTorIso
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC)
    (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))
  (eI : (integralComponentAt (X := pullback (C := Scheme) fA fB) z).subscheme ≅
      Spec (.of ((A ⊗[k] B) ⧸ I)))
  (eJ : (integralComponentAt (X := pullback (C := Scheme) fB fC) w).subscheme ≅
      Spec (.of ((B ⊗[k] C) ⧸ J)))
  (hI : (integralComponentAt (X := pullback (C := Scheme) fA fB) z).subschemeι ≫
      (pullbackSpecIso k A B).hom =
    eI.hom ≫ Spec.map (CommRingCat.ofHom (R := A ⊗[k] B)
        (S := (A ⊗[k] B) ⧸ I) (Ideal.Quotient.mk I)))
  (hJ : (integralComponentAt (X := pullback (C := Scheme) fB fC) w).subschemeι ≫
      (pullbackSpecIso k B C).hom =
    eJ.hom ≫ Spec.map (CommRingCat.ofHom (R := B ⊗[k] C)
        (S := (B ⊗[k] C) ⧸ J) (Ideal.Quotient.mk J)))
    (t : correspondenceIncidence fA fB fC z w) (n : ℕ) :
    (((Tor (ModuleCat ((correspondenceTripleProduct fA fB fC).presheaf.stalk
        (correspondenceIncidenceInclusion fA fB fC z w t))) n).obj
      (correspondenceIncidenceLeftPulledStalkModule fA fB fC z w t)).obj
      (correspondenceIncidenceRightPulledStalkModule fA fB fC z w t)) ≅
    (ModuleCat.restrictScalars
      (Scheme.stalkIsoOfAffineChart (correspondenceAffineTripleIso k A B C)
        (correspondenceIncidenceInclusion fA fB fC z w t)).hom.hom).obj
      (ModuleCat.Tor.middleSupportTorAtPrime k A B C
        ((correspondenceAffineTripleIso k A B C).hom
          (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal I J n) := by
  let a := correspondenceAffineLeftPulledStalkModuleIso k A B C z w I eI hI t
  let b := correspondenceAffineRightPulledStalkModuleIso k A B C z w J eJ hJ t
  exact (((Tor (ModuleCat ((correspondenceTripleProduct fA fB fC).presheaf.stalk
      (correspondenceIncidenceInclusion fA fB fC z w t))) n).mapIso a).app _) ≪≫
    ((Tor (ModuleCat ((correspondenceTripleProduct fA fB fC).presheaf.stalk
      (correspondenceIncidenceInclusion fA fB fC z w t))) n).obj _).mapIso b ≪≫
    RingTheory.TorIndependence.torRestrictIso
      (Scheme.stalkIsoOfAffineChart (correspondenceAffineTripleIso k A B C)
        (correspondenceIncidenceInclusion fA fB fC z w t)).commRingCatIsoToRingEquiv _ _ n

/-- Actual pulled-stalk Tor length equals localized middle-support Tor length in every degree. -/
theorem affinePulledStalkTor_length_eq_middleSupportTor
    (z : pullback (C := Scheme) fA fB) (w : pullback (C := Scheme) fB fC)
    (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C))
  (eI : (integralComponentAt (X := pullback (C := Scheme) fA fB) z).subscheme ≅
      Spec (.of ((A ⊗[k] B) ⧸ I)))
  (eJ : (integralComponentAt (X := pullback (C := Scheme) fB fC) w).subscheme ≅
      Spec (.of ((B ⊗[k] C) ⧸ J)))
  (hI : (integralComponentAt (X := pullback (C := Scheme) fA fB) z).subschemeι ≫
      (pullbackSpecIso k A B).hom =
    eI.hom ≫ Spec.map (CommRingCat.ofHom (R := A ⊗[k] B)
        (S := (A ⊗[k] B) ⧸ I) (Ideal.Quotient.mk I)))
  (hJ : (integralComponentAt (X := pullback (C := Scheme) fB fC) w).subschemeι ≫
      (pullbackSpecIso k B C).hom =
    eJ.hom ≫ Spec.map (CommRingCat.ofHom (R := B ⊗[k] C)
        (S := (B ⊗[k] C) ⧸ J) (Ideal.Quotient.mk J)))
    (t : correspondenceIncidence fA fB fC z w) (n : ℕ) :
    Module.length ((correspondenceTripleProduct fA fB fC).presheaf.stalk
      (correspondenceIncidenceInclusion fA fB fC z w t))
      (((Tor (ModuleCat ((correspondenceTripleProduct fA fB fC).presheaf.stalk
          (correspondenceIncidenceInclusion fA fB fC z w t))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule fA fB fC z w t)).obj
        (correspondenceIncidenceRightPulledStalkModule fA fB fC z w t)) =
    Module.length (Localization.AtPrime
      ((correspondenceAffineTripleIso k A B C).hom
        (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal)
      (ModuleCat.Tor.middleSupportTorAtPrime k A B C
        ((correspondenceAffineTripleIso k A B C).hom
          (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal I J n) := by
  have h₁ := (correspondenceAffinePulledStalkTorIso k A B C z w
    I J eI eJ hI hJ t n).toLinearEquiv.length_eq
  let e := Scheme.stalkIsoOfAffineChart (correspondenceAffineTripleIso k A B C)
    (correspondenceIncidenceInclusion fA fB fC z w t)
  exact h₁.trans (ModuleCat.length_restrictScalars_of_surjective
    (R := (correspondenceTripleProduct fA fB fC).presheaf.stalk
      (correspondenceIncidenceInclusion fA fB fC z w t))
    (S := Localization.AtPrime ((correspondenceAffineTripleIso k A B C).hom
      (correspondenceIncidenceInclusion fA fB fC z w t)).asIdeal)
    e.hom.hom e.commRingCatIsoToRingEquiv.surjective _)

end Stacks.Chow
