module

import Colib.Algebra.Category.ModuleCat.Tor.LocalizedMiddleDiagonal.Length

noncomputable section

open CategoryTheory ModuleCat.Tor
open Algebra.TensorProduct.MiddleDiagonal
open scoped TensorProduct

universe u

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]
variable (q : Ideal (tripleRing k A B C)) [q.IsPrime]

local instance : Ring (Localization.AtPrime q) :=
  (inferInstance : CommRing (Localization.AtPrime q)).toRing

local instance : Ring (Localization.AtPrime (ambientPrime k A B C q)) :=
  (inferInstance : CommRing (Localization.AtPrime (ambientPrime k A B C q))).toRing

-- The ambient prime is the actual inverse image, not an arbitrary chosen prime.
example : ambientPrime k A B C q = q.comap (quotientMap k A B C).toRingHom := rfl

-- The localized quotient is the native local ring map at that inverse image.
example : localizedQuotientMap k A B C q =
    Localization.localRingHom (q.comap (quotientMap k A B C).toRingHom) q
      (quotientMap k A B C).toRingHom rfl := rfl

-- Exact factorization of the scalar maps, not just an abstract ring isomorphism.
example :
    (algebraMap (tripleRing k A B C) (Localization.AtPrime q)).comp
      (quotientMap k A B C).toRingHom =
    (localizedQuotientMap k A B C q).comp
      (algebraMap (ambientRing k A B C) (Localization.AtPrime (ambientPrime k A B C q))) :=
  localizedQuotientMap_comp k A B C q

-- Surjectivity is derived without assuming it at the localized level.
example : Function.Surjective (localizedQuotientMap k A B C q) :=
  localizedQuotientMap_surjective k A B C q

-- Arbitrary ideals and arbitrary degrees; no support-flatness or regularity hypothesis.
example (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} (Localization.AtPrime (ambientPrime k A B C q))) n).obj
      ((ModuleCat.extendScalars
        (algebraMap (ambientRing k A B C) (Localization.AtPrime (ambientPrime k A B C q)))).obj
        ((ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
          (ModuleCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
            (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J)))))).obj
      ((ModuleCat.restrictScalars (localizedQuotientMap k A B C q)).obj
        (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q))) ≅
    (ModuleCat.restrictScalars (localizedQuotientMap k A B C q)).obj
      (((CategoryTheory.Tor (ModuleCat.{u} (Localization.AtPrime q)) n).obj
        ((ModuleCat.extendScalars (localizedLeftMap k A B C q).toRingHom).obj
          (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I)))).obj
        ((ModuleCat.extendScalars (localizedRightMap k A B C q).toRingHom).obj
          (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)))) :=
  middleDiagonalTorAtPrimeIso k A B C q I J n

-- The result is an actual isomorphism, with both inverse identities.
example (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    (middleDiagonalTorAtPrimeIso k A B C q I J n).hom ≫
      (middleDiagonalTorAtPrimeIso k A B C q I J n).inv = 𝟙 _ :=
  (middleDiagonalTorAtPrimeIso k A B C q I J n).hom_inv_id

example (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    (middleDiagonalTorAtPrimeIso k A B C q I J n).inv ≫
      (middleDiagonalTorAtPrimeIso k A B C q I J n).hom = 𝟙 _ :=
  (middleDiagonalTorAtPrimeIso k A B C q I J n).inv_hom_id

-- The comparison respects the actual localized ambient scalar action.
example (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ)
    (r : Localization.AtPrime (ambientPrime k A B C q))
    (x : middleDiagonalTorAtPrime k A B C q I J n) :
    (middleDiagonalTorAtPrimeIso k A B C q I J n).toLinearEquiv (r • x) =
      r • (middleDiagonalTorAtPrimeIso k A B C q I J n).toLinearEquiv x :=
  (middleDiagonalTorAtPrimeIso k A B C q I J n).toLinearEquiv.map_smul r x

-- Length is compared in the two actual rings even when it may be infinite.
example (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    Module.length (Localization.AtPrime (ambientPrime k A B C q))
      (middleDiagonalTorAtPrime k A B C q I J n) =
    Module.length (Localization.AtPrime q) (middleSupportTorAtPrime k A B C q I J n) :=
  middleDiagonalTorAtPrime_length k A B C q I J n

-- Finiteness transfers, rather than being introduced as a universal assertion.
example (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    Module.length (Localization.AtPrime (ambientPrime k A B C q))
        (middleDiagonalTorAtPrime k A B C q I J n) < ⊤ ↔
      Module.length (Localization.AtPrime q) (middleSupportTorAtPrime k A B C q I J n) < ⊤ :=
  middleDiagonalTorAtPrime_length_lt_top_iff k A B C q I J n
