/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.Tor.RingTower
public import Colib.Algebra.Category.ModuleCat.QuotientSquare
public import Colib.RingTheory.Koszul.RestrictionComparison
public import StacksFrontier.RingTheory.Koszul.TorIndependence
public import StacksFrontier.RingTheory.Sequence.Regular.Basic

/-!
# Tor after removing a regular leading block

For a square of literal ring maps `ψ.comp φ = θ.comp f`, the leading list `t`
is regular over `R`, generates `ker f`, and its image under `φ` is weakly
regular over `C` and generates `ker ψ`. The remaining list `s` is regular
only over `B` and generates `ker g`. Surjectivity of `f`, `g`, and `ψ` gives
an every-degree `R`-module isomorphism

`Tor_n^R(Res_φ C, Res_(g.comp f) A) ≅ Res_(ψ.comp φ) H_n(K_D(θ ∘ s.get); D)`.

The leading-pair vanishing is proved independently of `A` and `s`. The proof
then composes native change of rings, the actual tensor/quotient coefficient
comparison `b ⊗ c ↦ θ(b) * ψ(c)`, and the native Koszul comparison for `s`.
There is no assumption on regularity of `θ(s)`, surjectivity of `φ`, flatness,
finite length, or nonemptiness of either list. Degree zero is included.

## Source references

At AxiomMath/Stacks commit `5ed82d14634e8d9576bb844c7bd4e3da66d450e7`:
* `StacksFrontier/RingTheory/Koszul/Regular.lean:846-858`, Tag 062F;
* `StacksFrontier/RingTheory/Koszul/Defs.lean:274-276`;
* `StacksFrontier/RingTheory/Sequence/Regular/Basic.lean:711-713`;
* `StacksFrontier/RingTheory/Koszul/TorIndependence.lean:134-153`;
* `StacksFrontier/Homology/Tor/Independence.lean:199-221`;
* `StacksFrontier/RingTheory/Koszul/TorComparison/QuotientTor.lean:138-155`;
* `StacksFrontier/RingTheory/Tor/Balancing/Naturality.lean:740-742`, Tag 00M3.

At Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`:
* `Mathlib/RingTheory/Ideal/Quotient/Operations.lean:551-554`;
* `Mathlib/RingTheory/Regular/RegularSequence.lean:60-63`;
* `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:248-254`.

Colib `Koszul.homologySeqComplexTensorRestrictScalarsIso` retains the literal map
and mapped list. The imported ring-change and quotient-square comparisons preserve
the specified scalar maps.
This supplies the generic algebra needed by Motivic commit
`a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Exterior/Identity/IncidenceTorReduction.lean:33-124`.
It does not prove the geometric application and is not attributed to Tag 068M.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits
open RingTheory.Sequence

universe u

namespace ModuleCat.Tor

variable {R B A C D : Type u}
  [CommRing R] [CommRing B] [CommRing A] [CommRing C] [CommRing D]

/-- The leading regular quotient is Tor-independent of the coefficient ring.
Only `R`, `B`, `C`, and the leading list occur here, not the final quotient
or the remaining equations. Weak regularity of the coefficient image suffices. -/
theorem isZero_of_regularLeadingPair (f : R →+* B) (φ : R →+* C)
    (hf : Function.Surjective f) (t : List R)
    (ht : IsRegular R t) (hft : RingHom.ker f = Ideal.ofList t)
    (hCt : IsWeaklyRegular C (t.map φ)) (n : ℕ) (hn : 0 < n) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))) := by
  let := f.toAlgebra
  let := φ.toAlgebra
  have ht' : Koszul.IsKoszulRegular t.get :=
    (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := R)).2.2
      (by simpa only [List.ofFn_get] using ht)
  have hCt' : Koszul.IsKoszulRegular (fun i => φ (t.get i)) :=
    (Koszul.isKoszulRegularOn_self_iff _).mp
      ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := C)).1
        (by simpa only [List.ofFn_comp', List.ofFn_get] using hCt))
  have hft' : RingHom.ker (algebraMap R B) = Ideal.span (Set.range t.get) := by
    change RingHom.ker f = Ideal.span (Set.range t.get)
    simpa only [← Ideal.ofList_ofFn, List.ofFn_get] using hft
  have h := Koszul.torIndependent_of_isKoszulRegular_map
    (R := R) (C := B) (S := C) hf t.get ht' hft' hCt'
  exact (RingTheory.TorIndependence.torIndependent_iff_isZero_tor R B C).mp h n hn

/-- Every-degree regular-leading-block reduction with the actual restricted
scalar action and literal mapped remaining list. Regularity is required for
`s` over `B`, not for its image over `D`. -/
def regularLeadingBlockIso (f : R →+* B) (g : B →+* A) (φ : R →+* C)
    (ψ : C →+* D) (θ : B →+* D) (hsq : ψ.comp φ = θ.comp f)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hψ : Function.Surjective ψ) (t : List R) (s : List B)
    (ht : IsRegular R t) (hft : RingHom.ker f = Ideal.ofList t)
    (hCt : IsWeaklyRegular C (t.map φ)) (hψt : RingHom.ker ψ = Ideal.ofList (t.map φ))
    (hs : IsRegular B s) (hgs : RingHom.ker g = Ideal.ofList s) (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A)) ≅
      (ModuleCat.restrictScalars (ψ.comp φ)).obj
        ((Koszul.seqComplexTensor (fun i => θ (s.get i)) (ModuleCat.of D D)).homology n) := by
  letI := g.toAlgebra
  letI := θ.toAlgebra
  let M := (ModuleCat.restrictScalars θ).obj (ModuleCat.of D D)
  let eA : ModuleCat.of B (B ⧸ RingHom.ker g) ≅
      (ModuleCat.restrictScalars g).obj (ModuleCat.of A A) :=
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Algebra.ofId B A) hg).toLinearEquiv.toModuleIso
  have hker : RingHom.ker ψ = (RingHom.ker f).map φ := by
    rw [hψt, hft, Ideal.map_ofList]
  let eC := ModuleCat.extendScalarsQuotientSquareIso f φ ψ θ hsq hf hψ hker
  let eK : ((CategoryTheory.Tor (ModuleCat.{u} B) n).obj
      ((ModuleCat.restrictScalars g).obj (ModuleCat.of A A))).obj M ≅
        (Koszul.seqComplexTensor s.get M).homology n :=
    (((CategoryTheory.Tor (ModuleCat.{u} B) n).mapIso eA.symm).app M) ≪≫
      Koszul.torIsoHomologySeqComplexTensorOfIsRegular s.get
        (by simpa only [List.ofFn_get] using hs) (RingHom.ker g)
        (by simpa only [← Ideal.ofList_ofFn, List.ofFn_get] using hgs) M n
  let eH : (Koszul.seqComplexTensor s.get M).homology n ≅
      (ModuleCat.restrictScalars θ).obj
        ((Koszul.seqComplexTensor (fun i => θ (s.get i)) (ModuleCat.of D D)).homology n) :=
    Koszul.homologySeqComplexTensorRestrictScalarsIso s.get (ModuleCat.of D D) n
  let eSymm := Classical.choice (_root_.tor_symm_canonically_iso R n)
  exact ((eSymm.app ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).app
      ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A))) ≪≫
    ringTowerIsoOfIsZeroTor f g φ
      (isZero_of_regularLeadingPair f φ hf t ht hft hCt) n ≪≫
    (ModuleCat.restrictScalars f).mapIso
      ((((CategoryTheory.Tor (ModuleCat.{u} B) n).obj
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of A A))).mapIso eC) ≪≫ eK ≪≫ eH) ≪≫
    (ModuleCat.restrictScalarsComp'App f θ (ψ.comp φ) hsq
      ((Koszul.seqComplexTensor (fun i => θ (s.get i)) (ModuleCat.of D D)).homology n)).symm

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/RingTheory/Ideal/Quotient/Operations.lean:551-554"
  "ingredient" "The actual surjective map g identifies B modulo ker g with A as a B-module"]
  regularLeadingBlockIso

attribute [colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:248-254"
  "ingredient" "Flatten the actual restrictions along f and theta using the given square"]
  regularLeadingBlockIso

end ModuleCat.Tor
