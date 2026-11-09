/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.MiddleDiagonal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.DiagonalTorStalk

/-!
# The localized middle-diagonal Tor comparison

The actual ambient comparison can first be formed with a localized target ring and then
localized in the ambient ring. The factorization through the ambient localization is an exact
ring-map equality. Both localization cancellations are the native scalar-extension isomorphism,
so the result retains the actual action of the localized ambient ring.

In particular, for the literal middle-diagonal quotient `P → Q`, a prime `q` of `Q` determines
`p = q.comap (quotientMap k A B C)`. The map `P_p → Q_q` is Mathlib's `localRingHom`.
Its surjectivity is derived from the surjectivity of the actual middle-diagonal quotient.
No support module is assumed flat, and no Tor comparison is supplied as a hypothesis.

## References

* Stacks Project, Tag 00M8: flat base change for Tor, used for the ambient localization.
* Stacks Project, Tag 0B0T: reduction to the diagonal, used through the native ambient comparison.
* `motivic_source_a6805c4`, `Motivic/Aglib/Algebra/Category/ModuleCat/Tor/AmbientMiddle.lean` and
  `Motivic/Aglib/Algebra/Category/ModuleCat/Tor/SupportModulesMiddle.lean`: provenance of the
  actual middle-support Tor target. The localization interface here is a new composition of
  native Mathlib and Stacks constructions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat.Tor

section General

variable {k U V Q Pₗ : Type u} [Field k] [CommRing U] [CommRing V] [CommRing Q]
  [CommRing Pₗ] [Algebra k U] [Algebra k V] [Algebra k Q]

/-- Localize the actual ambient comparison, retaining the localized ambient scalar action.
The target `Q` may itself already be a localization. -/
def localizedFlatAmbientQuotientTorIso (a : U →ₐ[k] Q) (b : V →ₐ[k] Q)
    (ha : a.Flat) (hb : b.Flat) (φ : U ⊗[k] V →+* Pₗ) (T : Submonoid (U ⊗[k] V))
    (hT : letI := φ.toAlgebra; IsLocalization T Pₗ) (d : Pₗ →+* Q)
    (hd : (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom =
      d.comp φ) (I : Ideal U) (J : Ideal V) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} Pₗ) n).obj
      ((ModuleCat.extendScalars φ).obj
        ((ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
          (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J)))))).obj
      ((ModuleCat.restrictScalars d).obj (ModuleCat.of Q Q)) ≅
    (ModuleCat.restrictScalars d).obj
      (((CategoryTheory.Tor (ModuleCat.{u} Q) n).obj
        ((ModuleCat.extendScalars a.toRingHom).obj (ModuleCat.of U (U ⧸ I)))).obj
        ((ModuleCat.extendScalars b.toRingHom).obj (ModuleCat.of V (V ⧸ J)))) := by
  letI := φ.toAlgebra
  letI := hT
  let μ := (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom
  let M := (ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
    (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J)))
  let N := (ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q)
  exact (((CategoryTheory.Tor (ModuleCat.{u} Pₗ) n).obj
      ((ModuleCat.extendScalars φ).obj M)).mapIso
        (Stacks.Intersection.Diagonal.localizationBaseChangeRestrictIso
          φ T hT μ d hd (ModuleCat.of Q Q))).symm ≪≫
    (Stacks.Intersection.Diagonal.torLocalizationIso Pₗ T n M N).symm ≪≫
    (ModuleCat.extendScalars φ).mapIso (flatAmbientQuotientTorIso a b ha hb I J n) ≪≫
    Stacks.Intersection.Diagonal.localizationBaseChangeRestrictIso φ T hT μ d hd _

end General

section Middle

open Algebra.TensorProduct.MiddleDiagonal

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
variable {Pₗ Qₗ : Type u} [CommRing Pₗ] [CommRing Qₗ] [Algebra k Qₗ]

/-- The actual middle-diagonal comparison at compatible localizations of the ambient and
triple rings. Flatness of both adjacent maps is derived, including after localization. -/
def localizedMiddleDiagonalTorIso (ℓ : tripleRing k A B C →ₐ[k] Qₗ)
    (S : Submonoid (tripleRing k A B C))
    (hS : letI := ℓ.toRingHom.toAlgebra; IsLocalization S Qₗ)
    (φ : ambientRing k A B C →+* Pₗ) (T : Submonoid (ambientRing k A B C))
    (hT : letI := φ.toAlgebra; IsLocalization T Pₗ) (d : Pₗ →+* Qₗ)
    (hd : (ℓ.comp (quotientMap k A B C)).toRingHom = d.comp φ)
    (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} Pₗ) n).obj
      ((ModuleCat.extendScalars φ).obj
        ((ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
          (ModuleCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
            (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)))))).obj
      ((ModuleCat.restrictScalars d).obj (ModuleCat.of Qₗ Qₗ)) ≅
    (ModuleCat.restrictScalars d).obj
      (((CategoryTheory.Tor (ModuleCat.{u} Qₗ) n).obj
        ((ModuleCat.extendScalars (ℓ.comp (leftMap k A B C)).toRingHom).obj
          (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I)))).obj
        ((ModuleCat.extendScalars (ℓ.comp (rightMap k A B C)).toRingHom).obj
          (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)))) := by
  have hℓ : ℓ.Flat := by
    let := ℓ.toRingHom.toAlgebra
    let := hS
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Qₗ S)
  have hcomp :
      (Algebra.TensorProduct.lift (ℓ.comp (leftMap k A B C))
        (ℓ.comp (rightMap k A B C)) (fun _ _ => Commute.all _ _)).toRingHom =
      d.comp φ := by
    rw [← hd]
    ext <;> simp [quotientMap]
  exact localizedFlatAmbientQuotientTorIso
    (ℓ.comp (leftMap k A B C)) (ℓ.comp (rightMap k A B C))
    ((leftMap_flat k A B C).comp hℓ) ((rightMap_flat k A B C).comp hℓ)
    φ T hT d hcomp I J n

end Middle

end ModuleCat.Tor

namespace Algebra.TensorProduct.MiddleDiagonal

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

/-- The actual prime of the ambient ring over a prime of the triple ring. -/
abbrev ambientPrime (q : Ideal (tripleRing k A B C)) : Ideal (ambientRing k A B C) :=
  q.comap (quotientMap k A B C).toRingHom

variable (q : Ideal (tripleRing k A B C)) [q.IsPrime]

/-- The actual middle-diagonal map on the two prime localizations. -/
def localizedQuotientMap :
    Localization.AtPrime (ambientPrime k A B C q) →+* Localization.AtPrime q :=
  Localization.localRingHom (ambientPrime k A B C q) q (quotientMap k A B C).toRingHom rfl

/-- The prime-localized map factors the original quotient exactly. -/
theorem localizedQuotientMap_comp :
    (algebraMap (tripleRing k A B C) (Localization.AtPrime q)).comp
      (quotientMap k A B C).toRingHom =
    (localizedQuotientMap k A B C q).comp
      (algebraMap (ambientRing k A B C) (Localization.AtPrime (ambientPrime k A B C q))) := by
  apply RingHom.ext
  intro x
  exact (Localization.localRingHom_to_map (ambientPrime k A B C q) q
    (quotientMap k A B C).toRingHom rfl x).symm

/-- Surjectivity at the actual induced prime follows from the ambient quotient, not an
additional geometric or Tor hypothesis. -/
theorem localizedQuotientMap_surjective :
    Function.Surjective (localizedQuotientMap k A B C q) := by
  let μ := (quotientMap k A B C).toRingHom
  have hmap : (ambientPrime k A B C q).primeCompl.map μ = q.primeCompl :=
    Ideal.map_primeCompl_comap_of_surjective μ (quotientMap_surjective k A B C) q
  let : IsLocalization ((ambientPrime k A B C q).primeCompl.map μ)
      (Localization.AtPrime q) := hmap.symm ▸ inferInstance
  exact IsLocalization.map_surjective_of_surjective
    (ambientPrime k A B C q).primeCompl
    (Localization.AtPrime (ambientPrime k A B C q)) (Localization.AtPrime q)
    (quotientMap_surjective k A B C)

end Algebra.TensorProduct.MiddleDiagonal

namespace Algebra.TensorProduct.MiddleDiagonal

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
variable (q : Ideal (tripleRing k A B C)) [q.IsPrime]

/-- The structural map into the actual prime localization of the triple ring. -/
def tripleLocalizationMap : tripleRing k A B C →ₐ[k] Localization.AtPrime q :=
  IsScalarTower.toAlgHom k (tripleRing k A B C) (Localization.AtPrime q)

/-- The actual first adjacent coordinate map into the localized triple ring. -/
def localizedLeftMap : A ⊗[k] B →ₐ[k] Localization.AtPrime q :=
  (tripleLocalizationMap k A B C q).comp (leftMap k A B C)

/-- The actual second adjacent coordinate map into the localized triple ring. -/
def localizedRightMap : B ⊗[k] C →ₐ[k] Localization.AtPrime q :=
  (tripleLocalizationMap k A B C q).comp (rightMap k A B C)

end Algebra.TensorProduct.MiddleDiagonal

namespace ModuleCat.Tor

open Algebra.TensorProduct.MiddleDiagonal

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
variable (q : Ideal (tripleRing k A B C)) [q.IsPrime]

-- Normalize the native ring projection for categorical instance search on localizations.
/-- The ring structure on the localized triple ring, projected from its commutative ring. -/
local instance : Ring (Localization.AtPrime q) :=
  (inferInstance : CommRing (Localization.AtPrime q)).toRing

/-- The ring structure at the induced ambient prime, projected from its commutative ring. -/
local instance : Ring (Localization.AtPrime (ambientPrime k A B C q)) :=
  (inferInstance : CommRing (Localization.AtPrime (ambientPrime k A B C q))).toRing

/-- Native Tor over the induced ambient prime, with product support first and localized
triple-ring coefficients second. This abbreviation changes neither Tor nor its scalar action. -/
abbrev middleDiagonalTorAtPrime (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    ModuleCat.{u} (Localization.AtPrime (ambientPrime k A B C q)) :=
  ((CategoryTheory.Tor (ModuleCat.{u} (Localization.AtPrime (ambientPrime k A B C q))) n).obj
    ((ModuleCat.extendScalars
      (algebraMap (ambientRing k A B C) (Localization.AtPrime (ambientPrime k A B C q)))).obj
      ((ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
        (ModuleCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
          (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)))))).obj
    ((ModuleCat.restrictScalars (localizedQuotientMap k A B C q)).obj
      (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q)))

/-- Native Tor of the two actual scalar-extended quotient supports over the prime-localized
triple ring. No new realization of Tor is introduced. -/
abbrev middleSupportTorAtPrime (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    ModuleCat.{u} (Localization.AtPrime q) :=
  ((CategoryTheory.Tor (ModuleCat.{u} (Localization.AtPrime q)) n).obj
    ((ModuleCat.extendScalars (localizedLeftMap k A B C q).toRingHom).obj
      (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I)))).obj
    ((ModuleCat.extendScalars (localizedRightMap k A B C q).toRingHom).obj
      (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)))

/-- The all-degree middle-diagonal Tor isomorphism at the actual induced prime.
The only data are the field, its three commutative algebras, the triple-ring prime, the two
support ideals, and the degree. Localization, factorization, and factor flatness are derived. -/
def middleDiagonalTorAtPrimeIso (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    middleDiagonalTorAtPrime k A B C q I J n ≅
      (ModuleCat.restrictScalars (localizedQuotientMap k A B C q)).obj
        (middleSupportTorAtPrime k A B C q I J n) := by
  let e := localizedMiddleDiagonalTorIso k A B C
    (Pₗ := Localization.AtPrime (ambientPrime k A B C q)) (Qₗ := Localization.AtPrime q)
    (tripleLocalizationMap k A B C q)
    q.primeCompl (by
      change letI := (algebraMap (tripleRing k A B C) (Localization.AtPrime q)).toAlgebra
             IsLocalization q.primeCompl (Localization.AtPrime q)
      rw [toAlgebra_algebraMap]
      infer_instance)
    (algebraMap (ambientRing k A B C) (Localization.AtPrime (ambientPrime k A B C q)))
    (ambientPrime k A B C q).primeCompl (by
      rw [toAlgebra_algebraMap]
      infer_instance)
    (localizedQuotientMap k A B C q) (localizedQuotientMap_comp k A B C q) I J n
  exact e

end ModuleCat.Tor
