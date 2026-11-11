/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.Algebra.Category.ModuleCat.Tor.RegularBlock

/-! # Direct consumers of regular-leading-block reduction

These consumers retain literal ring maps, permit an arbitrary target image,
cover degree zero and empty blocks, and test the actual restricted scalar action.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingTheory.Sequence

universe u

variable {R B A C D : Type u}
  [CommRing R] [CommRing B] [CommRing A] [CommRing C] [CommRing D]

section GeneralSquare

variable (f : R →+* B) (g : B →+* A) (φ : R →+* C)
  (ψ : C →+* D) (θ : B →+* D) (hsq : ψ.comp φ = θ.comp f)
  (hf : Function.Surjective f) (hg : Function.Surjective g)
  (hψ : Function.Surjective ψ) (t : List R) (s : List B)
  (ht : IsRegular R t) (hft : RingHom.ker f = Ideal.ofList t)
  (hCt : IsWeaklyRegular C (t.map φ)) (hψt : RingHom.ker ψ = Ideal.ofList (t.map φ))
  (hs : IsRegular B s) (hgs : RingHom.ker g = Ideal.ofList s)

-- Neither the final quotient nor the remaining list is an input to vanishing.
example (n : ℕ) (hn : 0 < n) :
    IsZero (((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B))).obj
        ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))) :=
  ModuleCat.Tor.isZero_of_regularLeadingPair f φ hf t ht hft hCt n hn

example (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A)) ≅
      (ModuleCat.restrictScalars (ψ.comp φ)).obj
        ((Koszul.seqComplexTensor (fun i => θ (s.get i)) (ModuleCat.of D D)).homology n) :=
  ModuleCat.Tor.regularLeadingBlockIso f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs n

-- There is no positive-degree restriction on the comparison.
example :
    ((CategoryTheory.Tor (ModuleCat.{u} R) 0).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A)) ≅
      (ModuleCat.restrictScalars (ψ.comp φ)).obj
        ((Koszul.seqComplexTensor (fun i => θ (s.get i)) (ModuleCat.of D D)).homology 0) :=
  ModuleCat.Tor.regularLeadingBlockIso f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs 0

-- R-linearity is with the literal ψ.comp φ action on D-homology.
example (n : ℕ) (r : R)
    (x : ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A))) :
    (ModuleCat.Tor.regularLeadingBlockIso
      f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs n).hom (r • x) =
        (ψ (φ r)) • (ModuleCat.Tor.regularLeadingBlockIso
          f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs n).hom x := by
  exact (ModuleCat.Tor.regularLeadingBlockIso
    f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs n).hom.hom.map_smul r x

-- The actual inverse, rather than an assumed comparison, recovers each Tor element.
example (n : ℕ)
    (x : ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A))) :
    (ModuleCat.Tor.regularLeadingBlockIso
      f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs n).inv
        ((ModuleCat.Tor.regularLeadingBlockIso
          f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs n).hom x) = x :=
  ModuleCat.inv_hom_apply (ModuleCat.Tor.regularLeadingBlockIso
    f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs n) x

-- A supplied equality of literal mapped equations changes the native complex itself.
-- In particular q may be the zero function, which need not be regular over D.
example (n : ℕ) (q : Fin s.length → D) (hq : (fun i => θ (s.get i)) = q) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A)) ≅
      (ModuleCat.restrictScalars (ψ.comp φ)).obj
        ((Koszul.seqComplexTensor q (ModuleCat.of D D)).homology n) := by
  simpa only [hq] using ModuleCat.Tor.regularLeadingBlockIso
    f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs n

-- The entire surviving list may become zero; no image-regularity premise is hidden.
example (n : ℕ) (hz : ∀ b ∈ s, θ b = 0) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars (g.comp f)).obj (ModuleCat.of A A)) ≅
      (ModuleCat.restrictScalars (ψ.comp φ)).obj
        ((Koszul.seqComplexTensor (fun _ : Fin s.length => (0 : D))
          (ModuleCat.of D D)).homology n) := by
  have hzero : (fun i => θ (s.get i)) = fun _ => (0 : D) :=
    funext fun i => hz (s.get i) (List.mem_iff_get.mpr ⟨i, rfl⟩)
  simpa only [hzero] using ModuleCat.Tor.regularLeadingBlockIso
    f g φ ψ θ hsq hf hg hψ t s ht hft hCt hψt hs hgs n

end GeneralSquare

section EmptyLeadingBlock

variable [Nontrivial R] (g : R →+* A) (φ : R →+* C)
  (hg : Function.Surjective g) (s : List R)
  (hs : IsRegular R s) (hgs : RingHom.ker g = Ideal.ofList s)

-- f and ψ are identities; φ is arbitrary, not assumed surjective or flat.
example (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars g).obj (ModuleCat.of A A)) ≅
      (ModuleCat.restrictScalars φ).obj
        ((Koszul.seqComplexTensor (fun i => φ (s.get i)) (ModuleCat.of C C)).homology n) := by
  simpa only [RingHom.comp_id, RingHom.id_comp] using
    ModuleCat.Tor.regularLeadingBlockIso (RingHom.id R) g φ (RingHom.id C) φ
      (by ext r; rfl) Function.surjective_id hg Function.surjective_id [] s
      (IsRegular.nil R R) (by ext x; simp) (by simp) (by ext x; simp) hs hgs n

end EmptyLeadingBlock

section EmptyRemainingBlock

variable [Nontrivial B] (f : R →+* B) (φ : R →+* C)
  (ψ : C →+* D) (θ : B →+* D) (hsq : ψ.comp φ = θ.comp f)
  (hf : Function.Surjective f) (hψ : Function.Surjective ψ) (t : List R)
  (ht : IsRegular R t) (hft : RingHom.ker f = Ideal.ofList t)
  (hCt : IsWeaklyRegular C (t.map φ)) (hψt : RingHom.ker ψ = Ideal.ofList (t.map φ))

-- There is no remaining equation, and the coefficient ring D may be the zero ring.
example (n : ℕ) :
    ((CategoryTheory.Tor (ModuleCat.{u} R) n).obj
      ((ModuleCat.restrictScalars φ).obj (ModuleCat.of C C))).obj
        ((ModuleCat.restrictScalars f).obj (ModuleCat.of B B)) ≅
      (ModuleCat.restrictScalars (ψ.comp φ)).obj
        ((Koszul.seqComplexTensor (fun i => θ (([] : List B).get i))
          (ModuleCat.of D D)).homology n) := by
  simpa only [RingHom.id_comp] using
    ModuleCat.Tor.regularLeadingBlockIso f (RingHom.id B) φ ψ θ hsq hf
      Function.surjective_id hψ t [] ht hft hCt hψt (IsRegular.nil B B) (by ext x; simp) n

end EmptyRemainingBlock
