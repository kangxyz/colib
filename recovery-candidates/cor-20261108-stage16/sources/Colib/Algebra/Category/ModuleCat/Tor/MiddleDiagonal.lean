/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.ExteriorQuotient
public import Colib.Algebra.Category.ModuleCat.Tor.FlatRestriction
public import Colib.Algebra.Category.ModuleCat.Tor.MiddleDiagonal.Rings
public import StacksFrontier.RingTheory.Tor.Balancing.Naturality

/-!
# The actual middle-diagonal Tor comparison

For arbitrary commutative algebras `A`, `B`, `C` over a field `k`, put
`P = (A ⊗[k] B) ⊗[k] (B ⊗[k] C)` and `Q = (A ⊗[k] B) ⊗[k] C`.
The middle-diagonal ring map `P → Q` multiplies the middle `B` coordinates.
For ideals `I` of `A ⊗[k] B` and `J` of `B ⊗[k] C`, this file compares
actual categorical Tor over `P` of the product support ring and `Q` with
actual Tor over `Q` of the two scalar-extended support rings. The comparison
is an isomorphism of `P`-modules, not just of underlying abelian groups.

The more general `flatAmbientQuotientTorIso` works for two flat algebra maps
`U → Q` and `V → Q`. Their tensor product `U ⊗[k] V → Q ⊗[k] Q` is flat.
Native Tor symmetry puts `Q` first, one-sided flat change of rings extends
an actual projective resolution of the product support, and the native
full-diagonal theorem applies over `Q`. Restriction of scalars then uses
the exact equality of the composite ring map with the actual ambient map.
The ambient quotient map itself need not be flat, and neither support
module is assumed flat, projective, regular, or finite.

## References

* Stacks Project, Tag 0B0T, reduction to the diagonal.
* Stacks Project, Tag 00M3, balanced Tor and symmetry.
* `motivic_source_a6805c4`, `Algebra/Category/ModuleCat/Tor/Ambient.lean`
  and `AmbientMiddle.lean`: the source ambient comparison and its
  middle-diagonal specialization. The construction here instead reuses
  native full-diagonal Tor through a flat map to the tensor square of `Q`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped TensorProduct

universe u

namespace ModuleCat.Tor

section General

variable {k U V Q : Type u} [Field k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V] [Algebra k Q]

/-- The quotient by the extended ideal is the actual scalar-extended quotient module. -/
def quotientExtensionIso (a : U →+* Q) (I : Ideal U) :
    ModuleCat.of Q (Q ⧸ I.map a) ≅
      (ModuleCat.extendScalars a).obj (ModuleCat.of U (U ⧸ I)) :=
  letI := a.toAlgebra
  LinearEquiv.toModuleIso
    (X₁ := ModuleCat.of Q (Q ⧸ I.map a))
    (X₂ := (ModuleCat.extendScalars a).obj (ModuleCat.of U (U ⧸ I)))
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Q I).toLinearEquiv

/-- The actual ambient Tor comparison, first expressed using the extended quotient ideals. -/
def flatAmbientQuotientTorQuotientIso (a : U →ₐ[k] Q) (b : V →ₐ[k] Q)
    (ha : a.Flat) (hb : b.Flat) (I : Ideal U) (J : Ideal V) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} (U ⊗[k] V)) n).obj
      ((ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
        (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J))))).obj
      ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom).obj
        (ModuleCat.of Q Q)) ≅
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom).obj
      (((CategoryTheory.Tor (ModuleCat.{u} Q) n).obj
        (ModuleCat.of Q (Q ⧸ I.map a.toRingHom))).obj
        (ModuleCat.of Q (Q ⧸ J.map b.toRingHom))) := by
  let φ : U ⊗[k] V →+* Q ⊗[k] Q := (Algebra.TensorProduct.map a b).toRingHom
  let δ : Q ⊗[k] Q →+* Q := (Algebra.TensorProduct.lmul' k (S := Q)).toRingHom
  let μ : U ⊗[k] V →+* Q :=
    (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom
  have hμ : μ = δ.comp φ := by
    ext <;> simp [μ, δ, φ]
  let M := (ModuleCat.restrictScalars
    (productQuotientMap (k := k) I J).toRingHom).obj
      (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J)))
  let N := (ModuleCat.restrictScalars δ).obj (ModuleCat.of Q Q)
  let N₀ := (ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q)
  let eN : N₀ ≅ (ModuleCat.restrictScalars φ).obj N :=
    ModuleCat.restrictScalarsComp'App φ δ μ hμ (ModuleCat.of Q Q)
  let eM : (ModuleCat.extendScalars φ).obj M ≅
      Stacks.Intersection.Diagonal.extObj (k := k)
        (Q ⧸ I.map a.toRingHom) (Q ⧸ J.map b.toRingHom) :=
    (ModuleCat.extendScalars φ).mapIso (exteriorQuotientRestrictIso I J).symm ≪≫
      extendExteriorQuotientIso a b I J
  exact ((Tor_iso_Tor' (U ⊗[k] V) n).app M).app N₀ ≪≫
    (((torFlip_iso_Tor' (U ⊗[k] V) n).app M).app N₀).symm ≪≫
    ((CategoryTheory.Tor (ModuleCat.{u} (U ⊗[k] V)) n).mapIso eN).app M ≪≫
    flatRestrictionIso φ (ha.tensorProductMap hb) N M n ≪≫
    (ModuleCat.restrictScalars φ).mapIso
      (((CategoryTheory.Tor (ModuleCat.{u} (Q ⊗[k] Q)) n).obj N).mapIso eM ≪≫
        Stacks.Intersection.Diagonal.diagonalTorIso (k := k) (A := Q) n
          (Q ⧸ I.map a.toRingHom) (Q ⧸ J.map b.toRingHom)) ≪≫
    (ModuleCat.restrictScalarsComp'App φ δ μ hμ _).symm

/-- The ambient comparison with the actual two scalar-extension modules on the right. -/
def flatAmbientQuotientTorIso (a : U →ₐ[k] Q) (b : V →ₐ[k] Q)
    (ha : a.Flat) (hb : b.Flat) (I : Ideal U) (J : Ideal V) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} (U ⊗[k] V)) n).obj
      ((ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
        (ModuleCat.of ((U ⧸ I) ⊗[k] (V ⧸ J)) ((U ⧸ I) ⊗[k] (V ⧸ J))))).obj
      ((ModuleCat.restrictScalars
        (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom).obj
        (ModuleCat.of Q Q)) ≅
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom).obj
      (((CategoryTheory.Tor (ModuleCat.{u} Q) n).obj
        ((ModuleCat.extendScalars a.toRingHom).obj (ModuleCat.of U (U ⧸ I)))).obj
        ((ModuleCat.extendScalars b.toRingHom).obj (ModuleCat.of V (V ⧸ J)))) :=
  flatAmbientQuotientTorQuotientIso a b ha hb I J n ≪≫
    (ModuleCat.restrictScalars
      (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).toRingHom).mapIso
      (((CategoryTheory.Tor (ModuleCat.{u} Q) n).mapIso
          (quotientExtensionIso a.toRingHom I)).app (ModuleCat.of Q (Q ⧸ J.map b.toRingHom)) ≪≫
        ((CategoryTheory.Tor (ModuleCat.{u} Q) n).obj
          ((ModuleCat.extendScalars a.toRingHom).obj (ModuleCat.of U (U ⧸ I)))).mapIso
            (quotientExtensionIso b.toRingHom J))

end General

variable (k A B C : Type u) [Field k] [CommRing A] [CommRing B] [CommRing C]
  [Algebra k A] [Algebra k B] [Algebra k C]

open Algebra.TensorProduct.MiddleDiagonal

/-- Genuine all-degree middle-diagonal Tor over the literal three-factor tensor ring.
Both sides retain their actual `ambientRing`-module structures. -/
def middleDiagonalTorIso (I : Ideal (A ⊗[k] B)) (J : Ideal (B ⊗[k] C)) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} (ambientRing k A B C)) n).obj
      ((ModuleCat.restrictScalars (productQuotientMap (k := k) I J).toRingHom).obj
        (ModuleCat.of (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))
          (((A ⊗[k] B) ⧸ I) ⊗[k] ((B ⊗[k] C) ⧸ J))))).obj
      ((ModuleCat.restrictScalars (quotientMap k A B C).toRingHom).obj
        (ModuleCat.of (tripleRing k A B C) (tripleRing k A B C))) ≅
    (ModuleCat.restrictScalars (quotientMap k A B C).toRingHom).obj
      (((CategoryTheory.Tor (ModuleCat.{u} (tripleRing k A B C)) n).obj
        ((ModuleCat.extendScalars (leftMap k A B C).toRingHom).obj
          (ModuleCat.of (A ⊗[k] B) ((A ⊗[k] B) ⧸ I)))).obj
        ((ModuleCat.extendScalars (rightMap k A B C).toRingHom).obj
          (ModuleCat.of (B ⊗[k] C) ((B ⊗[k] C) ⧸ J)))) :=
  flatAmbientQuotientTorIso (leftMap k A B C) (rightMap k A B C)
    (leftMap_flat k A B C) (rightMap_flat k A B C) I J n

end ModuleCat.Tor
