/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import StacksFrontier.RingTheory.Koszul.FlatQuotient
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# One regular family after arbitrary base change of a split quotient

Let `A → B → A` be an algebra retraction. A regular family generating its
kernel has an `A`-flat quotient. Stacks 0CEP transports the same indexed family
under an arbitrary base change `A → A'`. If a localization of `B ⊗[A] A'` is
Noetherian local and the literal map from `B` is local, Stacks 061S makes that
image a regular family again. No flatness of `A'` over `A` is assumed.

The tensor-factor equation is retained as an equality of ring homomorphisms.
Every resulting list has the original `Fin r` index order; no permutation,
choice of new target generators, or sign normalization is made.
-/

@[expose] public noncomputable section

open TensorProduct RingTheory.Sequence

namespace RingTheory.Sequence

/-- A ring isomorphism transports a regular list by its literal element map. -/
theorem IsRegular.map_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    {l : List R} (hl : IsRegular R l) (e : R ≃+* S) : IsRegular S (l.map e) := by
  apply (e.toAddEquiv.isRegular_congr ?_).mp hl
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  exact e.map_mul r x

/-- The kernel quotient of an algebra retraction is flat over its base ring. -/
theorem flat_quotient_ker_algebraRetraction
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (ε : B →ₐ[A] A) : Module.Flat A (B ⧸ RingHom.ker ε.toRingHom) := by
  exact Module.Flat.of_linearEquiv
    (Ideal.quotientKerAlgEquivOfRightInverse
      (f := ε) (g := algebraMap A B) ε.commutes).toLinearEquiv

/-- Flat-quotient base change and flat localization preserve the literal regular
family when the resulting local ring is Noetherian. The parameter algebra `A'`
need not be flat over `A`. -/
@[stacks 0CEP "application: same indexed family after arbitrary base change with flat quotient",
  stacks 061S "application: regularity of that family in the Noetherian local target"]
theorem IsRegular.map_of_quotient_flat_tensor_localization
    {A B A' D : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [Algebra A A'] [CommRing D]
    [IsLocalRing B] [IsLocalRing D] [IsNoetherianRing D]
    {r : ℕ} {s : Fin r → B} (hs : IsRegular B (List.ofFn s))
    (hflat : Module.Flat A (B ⧸ Ideal.span (Set.range s)))
    (q : B →+* D) [IsLocalHom q]
    (φ : B ⊗[A] A' →+* D)
    (hφ : φ.comp Algebra.TensorProduct.includeLeftRingHom = q)
    (hloc : letI : Algebra (B ⊗[A] A') D := φ.toAlgebra
      ∃ M : Submonoid (B ⊗[A] A'), IsLocalization M D) :
    IsRegular D (List.ofFn (fun i => q (s i))) := by
  have hkoszul : Koszul.IsKoszulRegular s :=
    (Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := B)).2.2 hs
  have hquasi : IsQuasiRegular B (List.ofFn s) :=
    Koszul.isQuasiRegular_of_isH1RegularOn
      ((Koszul.isH1RegularOn_self_iff s).2 hkoszul.isH1Regular)
  have hbase :=
    (Koszul.quasiRegular_and_h1Regular_baseChange_of_quotient_flat
      (A := A) (A' := A') s hflat).1 hquasi
  let : Algebra (B ⊗[A] A') D := φ.toAlgebra
  obtain ⟨M, hM⟩ := hloc
  let : IsLocalization M D := hM
  have hφflat : φ.Flat := IsLocalization.flat D M
  have htarget := Koszul.isQuasiRegular_map_of_flat φ hφflat hbase
  have hfamily :
      (List.ofFn (KoszulH1.fp (A := A) (A' := A') s)).map φ =
        List.ofFn (fun i => q (s i)) := by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact DFunLike.congr_fun hφ (s i)
  rw [hfamily] at htarget
  apply IsRegular.of_isQuasiRegular_of_mem_maximalIdeal ?_ htarget
  intro d hd
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hd
  have hproper : Ideal.ofList (List.ofFn s) ≠ ⊤ := by
    intro htop
    exact hs.top_ne_smul (by rw [htop, Submodule.top_smul])
  exact map_nonunit q (s i)
    (IsLocalRing.le_maximalIdeal hproper
      (Ideal.subset_span (List.mem_ofFn.mpr ⟨i, rfl⟩)))

/-- A kernel-generating regular family for a retraction survives arbitrary base
change and localization in the same order. Flatness of its quotient is proved,
not supplied as a Tor or common-family hypothesis. -/
theorem IsRegular.map_of_algebraRetraction_tensor_localization
    {A B A' D : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [CommRing A'] [Algebra A A'] [CommRing D]
    [IsLocalRing B] [IsLocalRing D] [IsNoetherianRing D]
    (ε : B →ₐ[A] A) {r : ℕ} {s : Fin r → B}
    (hs : IsRegular B (List.ofFn s))
    (hker : Ideal.span (Set.range s) = RingHom.ker ε.toRingHom)
    (q : B →+* D) [IsLocalHom q]
    (φ : B ⊗[A] A' →+* D)
    (hφ : φ.comp Algebra.TensorProduct.includeLeftRingHom = q)
    (hloc : letI : Algebra (B ⊗[A] A') D := φ.toAlgebra
      ∃ M : Submonoid (B ⊗[A] A'), IsLocalization M D) :
    IsRegular D (List.ofFn (fun i => q (s i))) := by
  apply hs.map_of_quotient_flat_tensor_localization (A := A) (A' := A')
    (q := q) (φ := φ) (hφ := hφ) (hloc := hloc)
  rw [hker]
  exact flat_quotient_ker_algebraRetraction ε

end RingTheory.Sequence
