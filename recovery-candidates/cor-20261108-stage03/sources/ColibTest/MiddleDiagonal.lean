module

import Colib.Algebra.Category.ModuleCat.Tor.MiddleDiagonal

noncomputable section

open CategoryTheory ModuleCat.Tor
open Algebra.TensorProduct.MiddleDiagonal
open scoped TensorProduct

universe u

section FlatRestriction

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

-- The second coefficient need not be extended from the smaller ring or flat.
example (hφ : φ.Flat) (N : ModuleCat.{u} S) (M : ModuleCat.{u} R) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj N)).obj M ≅
      (ModuleCat.restrictScalars φ).obj
        (((CategoryTheory.Tor (ModuleCat.{u} S) n).obj N).obj
          ((ModuleCat.extendScalars φ).obj M)) :=
  flatRestrictionIso φ hφ N M n

-- The quotient-to-tensor comparison retains its actual S-module action.
example (I : Ideal R) :
    ModuleCat.of S (S ⧸ I.map φ) ≅
      (ModuleCat.extendScalars φ).obj (ModuleCat.of R (R ⧸ I)) :=
  quotientExtensionIso φ I

end FlatRestriction

section Middle

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

-- No balanced-tensor ring abbreviation replaces the literal triple ring.
example : tripleRing k A B C = (A ⊗[k] B) ⊗[k] C := rfl

example (a : A) (b b' : B) (c : C) :
    quotientMap k A B C ((a ⊗ₜ[k] b) ⊗ₜ[k] (b' ⊗ₜ[k] c)) =
      (a ⊗ₜ[k] (b * b')) ⊗ₜ[k] c :=
  quotientMap_tmul_tmul k A B C a b b' c

-- This equality controls the P-action of the final comparison.
example :
    (Algebra.TensorProduct.lmul' k (S := (A ⊗[k] B) ⊗[k] C)).comp
      (fullDiagonalMap k A B C) = quotientMap k A B C :=
  fullDiagonal_comp k A B C

example : Function.Surjective (quotientMap k A B C) :=
  quotientMap_surjective k A B C

-- Only the map to the full tensor square, not the middle quotient, is asserted flat.
example : RingHom.Flat (R := ambientRing k A B C)
    (S := tripleRing k A B C ⊗[k] tripleRing k A B C)
    (fullDiagonalMap k A B C).toRingHom :=
  fullDiagonalMap_flat k A B C

-- All degrees, arbitrary ideals, and raw literal rings on both sides.
example (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} ((A ⊗[k] B) ⊗[k] (B ⊗[k] C))) n).obj
      ((ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
        (ModuleCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
          (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))))).obj
      ((ModuleCat.restrictScalars (quotientMap k A B C).toRingHom).obj
        (ModuleCat.of ((A ⊗[k] B) ⊗[k] C) ((A ⊗[k] B) ⊗[k] C))) ≅
    (ModuleCat.restrictScalars (quotientMap k A B C).toRingHom).obj
      (((CategoryTheory.Tor (ModuleCat.{u} ((A ⊗[k] B) ⊗[k] C)) n).obj
        ((ModuleCat.extendScalars (leftMap k A B C).toRingHom).obj
          (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I)))).obj
        ((ModuleCat.extendScalars (rightMap k A B C).toRingHom).obj
          (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)))) :=
  middleDiagonalTorIso k A B C I J n

-- A genuine invertible P-linear comparison, rather than an assumed equality of lengths.
example (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    (middleDiagonalTorIso k A B C I J n).hom ≫
      (middleDiagonalTorIso k A B C I J n).inv = 𝟙 _ :=
  (middleDiagonalTorIso k A B C I J n).hom_inv_id

end Middle
