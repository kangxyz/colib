/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.ArtinNormSum
public import Colib.RingTheory.KTheory.MilnorK.Norm.FieldPresentation
import Mathlib.RingTheory.Flat.Stability

/-!
# Base change of Milnor norms by Artinian fibers

A finite tensor algebra over the coefficient field has a weighted norm sum
over its actual residue fields. The flat refinement over an intermediate
field multiplies local lengths and composes residue norms. Induction on the
extension degree reduces arbitrary finite base change to the simple formula.
-/

@[expose] public noncomputable section

open IntermediateField
open scoped TensorProduct

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] finiteArtinResidueField

private def weightedFiberTerm {L E A B : Type u} [Field L] [Field E]
    [CommRing A] [CommRing B] [Algebra L A] [Algebra A B]
    [Module.Finite L A] [Module.Finite A B] (j : E →+* B) (x : MilnorKRing E)
    (p : PrimeSpectrum A) (q : PrimeSpectrum (p.asIdeal.Fiber B)) : MilnorKRing L := by
  let C := p.asIdeal.ResidueField
  let H := p.asIdeal.Fiber B
  let Q := q.asIdeal.ResidueField
  let : Module.Finite C H := Module.Finite.base_change A C B
  let : Algebra C Q := IsLocalRing.ResidueField.algebra (Localization.AtPrime q.asIdeal)
  let : Module C Q := Algebra.toModule
  let : FiniteDimensional C Q := finiteArtinResidueField (L := C) (A := H) q
  let g : B →ₐ[A] H := Algebra.TensorProduct.includeRight
  exact ((artinLocalLength p * artinLocalLength q : ℕ) : ℤ) •
    milnorKNormRing L C (milnorKNormRing C Q
      (milnorKRingMap ((algebraMap H Q).comp (g.toRingHom.comp j)) x))

private theorem weightedFiberTerm_eq {L E A B : Type u} [Field L] [Field E]
    [CommRing A] [CommRing B] [Algebra L A] [Algebra L B] [Algebra A B]
    [IsScalarTower L A B] [Module.Finite L A] [Module.Finite L B]
    [Module.Finite A B] [Module.Flat A B] [IsArtinianRing A]
    (j : E →+* B) (x : MilnorKRing E)
    (p : PrimeSpectrum A) (q : PrimeSpectrum (p.asIdeal.Fiber B)) :
    let r := artinSpectrumFiberEquiv A B ⟨p, q⟩
    weightedFiberTerm (L := L) j x p q =
      (artinLocalLength r : ℤ) • milnorKNormRing L r.asIdeal.ResidueField
        (milnorKRingMap ((algebraMap B r.asIdeal.ResidueField).comp j) x) := by
  let C := p.asIdeal.ResidueField
  let Q := q.asIdeal.ResidueField
  let r := artinSpectrumFiberEquiv A B ⟨p, q⟩
  let P := r.asIdeal.ResidueField
  let H := p.asIdeal.Fiber B
  let g : B →ₐ[A] H := Algebra.TensorProduct.includeRight
  let : Module.Finite C H := Module.Finite.base_change A C B
  let : Module.Finite L H := Module.Finite.trans C H
  let : Algebra C Q := IsLocalRing.ResidueField.algebra (Localization.AtPrime q.asIdeal)
  let : Module C Q := Algebra.toModule
  let : FiniteDimensional C Q := finiteArtinResidueField (L := C) (A := H) q
  let : FiniteDimensional L Q := finiteArtinResidueField (L := L) q
  let : FiniteDimensional L P := finiteArtinResidueField (L := L) r
  let e : P ≃+* Q := artinFiberResidueEquiv p q
  have hbase : e.toRingHom.comp (algebraMap L P) = algebraMap L Q := by
    apply RingHom.ext
    intro a
    change e (algebraMap L P a) = algebraMap L Q a
    rw [IsScalarTower.algebraMap_apply L B P]
    change artinFiberResidueEquiv p q (algebraMap B P (algebraMap L B a)) = _
    rw [artinFiberResidueEquiv_algebraMap]
    change algebraMap H Q (g (algebraMap L B a)) = _
    rw [IsScalarTower.algebraMap_apply L A B, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply A H Q, ← IsScalarTower.algebraMap_apply L A Q]
  have hmap : e.toRingHom.comp ((algebraMap B P).comp j) =
      (algebraMap H Q).comp (g.toRingHom.comp j) := by
    apply RingHom.ext
    intro a
    exact artinFiberResidueEquiv_algebraMap p q (j a)
  let y := milnorKRingMap ((algebraMap H Q).comp (g.toRingHom.comp j)) x
  have hlength : artinLocalLength p * artinLocalLength q = artinLocalLength r :=
    artinLocalLength_fiber_mul p q
  have htower : milnorKNormRing L C (milnorKNormRing C Q y) = milnorKNormRing L Q y :=
    milnorKNormRing_tower_of_finite y
  have hnorm : milnorKNormRing L P (milnorKRingMap ((algebraMap B P).comp j) x) =
      milnorKNormRing L Q y :=
    norm_map_eq_of_ringEquiv e _ _ hbase hmap x
  change ((artinLocalLength p * artinLocalLength q : ℕ) : ℤ) •
    milnorKNormRing L C (milnorKNormRing C Q y) = (artinLocalLength r : ℤ) • _
  rw [hlength, htower, hnorm]

private theorem weightedNormSum_fibers {L E A B : Type u} [Field L] [Field E]
    [CommRing A] [CommRing B] [Algebra L A] [Algebra L B] [Algebra A B]
    [IsScalarTower L A B] [Module.Finite L A] [Module.Finite L B]
    [Module.Finite A B] [Module.Flat A B] (j : E →+* B) (x : MilnorKRing E) :
    weightedNormSum (L := L) j x =
      ∑ᶠ p : PrimeSpectrum A, (artinLocalLength p : ℤ) •
        milnorKNormRing L p.asIdeal.ResidueField
          (weightedNormSum (L := p.asIdeal.ResidueField)
            ((Algebra.TensorProduct.includeRight : B →ₐ[A] p.asIdeal.Fiber B).toRingHom.comp j)
            x) := by
  classical
  let : IsArtinianRing A := IsArtinianRing.of_finite L A
  let : IsArtinianRing B := IsArtinianRing.of_finite L B
  let : ∀ p : PrimeSpectrum A, IsArtinianRing (p.asIdeal.Fiber B) :=
    fun p => IsArtinianRing.of_finite p.asIdeal.ResidueField _
  let : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  let : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  let : ∀ p : PrimeSpectrum A, Fintype (PrimeSpectrum (p.asIdeal.Fiber B)) :=
    fun p => Fintype.ofFinite _
  let t (s : Σ p : PrimeSpectrum A, PrimeSpectrum (p.asIdeal.Fiber B)) : MilnorKRing L :=
    weightedFiberTerm (L := L) j x s.1 s.2
  symm
  simp only [weightedNormSum, finsum_eq_sum_of_fintype, map_sum, map_zsmul,
    Finset.smul_sum, smul_smul, ← Nat.cast_mul]
  change (∑ p : PrimeSpectrum A, ∑ q : PrimeSpectrum (p.asIdeal.Fiber B), t ⟨p, q⟩) = _
  rw [← Fintype.sum_sigma t]
  refine Fintype.sum_equiv (artinSpectrumFiberEquiv A B) t _ ?_
  rintro ⟨p, q⟩
  exact weightedFiberTerm_eq (L := L) j x p q

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private def tensorTowerRingEquiv (k L M E : Type u) [Field k] [Field L] [Field M] [Field E]
    [Algebra k L] [Algebra k M] [Algebra M E] [Algebra k E] [IsScalarTower k M E] :
    (L ⊗[k] M) ⊗[M] E ≃+* L ⊗[k] E :=
  (Algebra.TensorProduct.comm M (L ⊗[k] M) E).toRingEquiv.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[M] E)
      (Algebra.TensorProduct.commRight k M L).symm).toRingEquiv.trans <|
    (Algebra.TensorProduct.cancelBaseChange k M M E L).toRingEquiv.trans
      (Algebra.TensorProduct.comm k E L).toRingEquiv

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem tensorTowerRingEquiv_tmul_one (k L M E : Type u)
    [Field k] [Field L] [Field M] [Field E]
    [Algebra k L] [Algebra k M] [Algebra M E] [Algebra k E] [IsScalarTower k M E]
    (a : L) (x : E) :
    tensorTowerRingEquiv k L M E ((a ⊗ₜ[k] (1 : M)) ⊗ₜ[M] x) = a ⊗ₜ[k] x := by
  let A := L ⊗[k] M
  let a₀ : A := a ⊗ₜ[k] (1 : M)
  let e₁ := Algebra.TensorProduct.comm M A E
  let e₂ := Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[M] E)
    (Algebra.TensorProduct.commRight k M L).symm
  let e₃ := Algebra.TensorProduct.cancelBaseChange k M M E L
  let e₄ := Algebra.TensorProduct.comm k E L
  have h₁ : e₁ (a₀ ⊗ₜ[M] x) = x ⊗ₜ[M] a₀ :=
    Algebra.TensorProduct.comm_tmul M a₀ x
  have hleft : (Algebra.TensorProduct.commRight k M L).symm a₀ = (1 : M) ⊗ₜ[k] a :=
    Algebra.TensorProduct.commRight_symm_tmul k (1 : M) a
  have h₂ : e₂ (x ⊗ₜ[M] a₀) = x ⊗ₜ[M] ((1 : M) ⊗ₜ[k] a) := by
    simp only [e₂, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq, hleft]
  have h₃ : e₃ (x ⊗ₜ[M] ((1 : M) ⊗ₜ[k] a)) = x ⊗ₜ[k] a := by
    simpa only [one_smul] using
      Algebra.TensorProduct.cancelBaseChange_tmul (R := k) (S := M) (T := M)
        (A := E) (B := L) x (1 : M) a
  have h₄ : e₄ (x ⊗ₜ[k] a) = a ⊗ₜ[k] x := Algebra.TensorProduct.comm_tmul k x a
  change e₄ (e₃ (e₂ (e₁ (a₀ ⊗ₜ[M] x)))) = a ⊗ₜ[k] x
  exact (congrArg (fun y => e₄ (e₃ (e₂ y))) h₁).trans
    ((congrArg (fun y => e₄ (e₃ y)) h₂).trans ((congrArg e₄ h₃).trans h₄))

private theorem weightedNormSum_tensorFiber {M E A : Type u} [Field M] [Field E]
    [CommRing A] [Algebra M A] [Algebra M E] [FiniteDimensional M E]
    (p : PrimeSpectrum A) (x : MilnorKRing E)
    (h : ∀ (C : Type u) [Field C] [Algebra M C],
      milnorKRingMap (algebraMap M C) (milnorKNormRing M E x) =
        weightedNormSum (L := C)
          (Algebra.TensorProduct.includeRight : E →ₐ[M] C ⊗[M] E).toRingHom x) :
    milnorKRingMap (algebraMap M p.asIdeal.ResidueField) (milnorKNormRing M E x) =
      weightedNormSum (L := p.asIdeal.ResidueField)
        ((Algebra.TensorProduct.includeRight :
          (A ⊗[M] E) →ₐ[A] p.asIdeal.Fiber (A ⊗[M] E)).toRingHom.comp
            (Algebra.TensorProduct.includeRight : E →ₐ[M] A ⊗[M] E).toRingHom) x := by
  let C := p.asIdeal.ResidueField
  let B := A ⊗[M] E
  let H := p.asIdeal.Fiber B
  let j : E →ₐ[M] B := Algebra.TensorProduct.includeRight
  let i : B →ₐ[A] H := Algebra.TensorProduct.includeRight
  let f : H ≃ₐ[C] C ⊗[M] E := Algebra.TensorProduct.cancelBaseChange M A C C E
  let g : E →+* H := i.toRingHom.comp j.toRingHom
  let g' : E →+* C ⊗[M] E :=
    (Algebra.TensorProduct.includeRight : E →ₐ[M] C ⊗[M] E).toRingHom
  have hf : f.toRingHom.comp g = g' := by
    apply RingHom.ext
    intro a
    change f ((1 : C) ⊗ₜ[A] ((1 : A) ⊗ₜ[M] a)) = (1 : C) ⊗ₜ[M] a
    simpa only [one_smul] using
      Algebra.TensorProduct.cancelBaseChange_tmul (R := M) (S := A) (T := C)
        (A := C) (B := E) (1 : C) (1 : A) a
  have he := weightedNormSum_algEquiv f g x
  rw [hf] at he
  exact (h C).trans he.symm

private theorem weightedNormSum_tensorFibers {L M E A : Type u} [Field L] [Field M]
    [Field E] [CommRing A] [Algebra L A] [Algebra M A] [Algebra M E]
    [Module.Finite L A] [FiniteDimensional M E] (x : MilnorKRing E)
    (h : ∀ (C : Type u) [Field C] [Algebra M C],
      milnorKRingMap (algebraMap M C) (milnorKNormRing M E x) =
        weightedNormSum (L := C)
          (Algebra.TensorProduct.includeRight : E →ₐ[M] C ⊗[M] E).toRingHom x) :
    letI : Module.Finite L (A ⊗[M] E) := Module.Finite.trans A _
    weightedNormSum (L := L) (algebraMap M A) (milnorKNormRing M E x) =
      weightedNormSum (L := L)
        (Algebra.TensorProduct.includeRight : E →ₐ[M] A ⊗[M] E).toRingHom x := by
  let B := A ⊗[M] E
  let : Module.Finite L B := Module.Finite.trans A B
  let j : E →+* B := (Algebra.TensorProduct.includeRight : E →ₐ[M] B).toRingHom
  change weightedNormSum (L := L) (algebraMap M A) (milnorKNormRing M E x) =
    weightedNormSum (L := L) j x
  refine Eq.trans ?_ (weightedNormSum_fibers (L := L) (A := A) (B := B) j x).symm
  rw [weightedNormSum]
  refine finsum_congr fun p => ?_
  let C := p.asIdeal.ResidueField
  have hm : (algebraMap A C).comp (algebraMap M A) = algebraMap M C :=
    (IsScalarTower.algebraMap_eq M A C).symm
  rw [hm]
  exact congrArg (fun z : MilnorKRing C => (artinLocalLength p : ℤ) • milnorKNormRing L C z)
    (weightedNormSum_tensorFiber p x h)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private def tensorTowerAlgEquiv (k L M E : Type u) [Field k] [Field L] [Field M] [Field E]
    [Algebra k L] [Algebra k M] [Algebra M E] [Algebra k E] [IsScalarTower k M E] :
    (L ⊗[k] M) ⊗[M] E ≃ₐ[L] L ⊗[k] E where
  toRingEquiv := tensorTowerRingEquiv k L M E
  commutes' a := by
    change tensorTowerRingEquiv k L M E ((a ⊗ₜ[k] (1 : M)) ⊗ₜ[M] (1 : E)) =
      a ⊗ₜ[k] 1
    exact tensorTowerRingEquiv_tmul_one k L M E a 1

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem tensorTowerAlgEquiv_includeRight (k L M E : Type u)
    [Field k] [Field L] [Field M] [Field E] [Algebra k L] [Algebra k M] [Algebra M E]
    [Algebra k E] [IsScalarTower k M E] :
    (tensorTowerAlgEquiv k L M E).toRingHom.comp
      (Algebra.TensorProduct.includeRight : E →ₐ[M] (L ⊗[k] M) ⊗[M] E).toRingHom =
        (Algebra.TensorProduct.includeRight : E →ₐ[k] L ⊗[k] E).toRingHom := by
  apply RingHom.ext
  intro a
  change tensorTowerRingEquiv k L M E (((1 : L) ⊗ₜ[k] (1 : M)) ⊗ₜ[M] a) =
    (1 : L) ⊗ₜ[k] a
  exact tensorTowerRingEquiv_tmul_one k L M E 1 a

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem weightedNormSum_tensorTower {k L M E : Type u} [Field k] [Field L]
    [Field M] [Field E] [Algebra k L] [Algebra k M] [Algebra M E] [Algebra k E]
    [IsScalarTower k M E] [FiniteDimensional k M] [FiniteDimensional M E]
    [FiniteDimensional k E] (x : MilnorKRing E)
    (h : ∀ (C : Type u) [Field C] [Algebra M C],
      milnorKRingMap (algebraMap M C) (milnorKNormRing M E x) =
        weightedNormSum (L := C)
          (Algebra.TensorProduct.includeRight : E →ₐ[M] C ⊗[M] E).toRingHom x) :
    weightedNormSum (L := L)
        (Algebra.TensorProduct.includeRight : M →ₐ[k] L ⊗[k] M).toRingHom
        (milnorKNormRing M E x) =
      weightedNormSum (L := L)
        (Algebra.TensorProduct.includeRight : E →ₐ[k] L ⊗[k] E).toRingHom x := by
  let A := L ⊗[k] M
  let B := A ⊗[M] E
  let : Module.Finite L B := Module.Finite.trans A B
  let j : E →+* B := (Algebra.TensorProduct.includeRight : E →ₐ[M] B).toRingHom
  let e : B ≃ₐ[L] L ⊗[k] E := tensorTowerAlgEquiv k L M E
  have he := weightedNormSum_algEquiv e j x
  have hcomp : e.toRingHom.comp j =
      (Algebra.TensorProduct.includeRight : E →ₐ[k] L ⊗[k] E).toRingHom :=
    tensorTowerAlgEquiv_includeRight k L M E
  rw [hcomp] at he
  exact (weightedNormSum_tensorFibers (L := L) (A := A) x h).trans he

private theorem weightedNormSum_tensor_aux :
    ∀ d : ℕ, ∀ (k L E : Type u) [Field k] [Field L] [Field E]
      [Algebra k L] [Algebra k E] [FiniteDimensional k E],
      Module.finrank k E = d → ∀ x : MilnorKRing E,
        milnorKRingMap (algebraMap k L) (milnorKNormRing k E x) =
          weightedNormSum (L := L)
            (Algebra.TensorProduct.includeRight : E →ₐ[k] L ⊗[k] E).toRingHom x := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro k L E _ _ _ _ _ _ hd x
    classical
    by_cases h : ∃ a : E, a ∉ Set.range (algebraMap k E)
    · let a := h.choose
      let M := k⟮a⟯
      let ha : IsIntegral k a := Algebra.IsIntegral.isIntegral a
      let p := minpolyOfDegree k ha
      let ε : M ≃ₐ[k] AdjoinRoot (poly p) := adjoinSimpleEquivQuot k ha
      let : FiniteDimensional k M := FiniteDimensional.left k M E
      let : FiniteDimensional M E := FiniteDimensional.right k M E
      have hlt : Module.finrank M E < d := hd ▸ finrank_adjoin_simple_lt h.choose_spec
      rw [← milnorKNormRing_tower_of_finite (K := k) (M := M) (L := E) x]
      refine (weightedNormSum_of_presentation (L := L) p ε _).trans ?_
      apply weightedNormSum_tensorTower (M := M)
      intro C _ _
      exact ih _ hlt M C E rfl x
    · have hb := bijective_algebraMap_of_forall h
      let : Algebra.IsSeparable k E := ⟨fun y => by
        obtain ⟨a, rfl⟩ := hb.surjective y
        exact isSeparable_algebraMap a⟩
      obtain ⟨_, p, ⟨ε⟩⟩ := exists_monicIrreducible_presentation k E
      exact weightedNormSum_of_presentation p ε x


/-- The Milnor norm of a finite extension commutes with arbitrary scalar
extension after summing the actual Artinian branches with their local weights. -/
theorem milnorKNormRing_map_eq_weightedNormSum_tensorProduct_of_finite
    {k L E : Type u} [Field k] [Field L] [Field E] [Algebra k L] [Algebra k E]
    [FiniteDimensional k E] (x : MilnorKRing E) :
    milnorKRingMap (algebraMap k L) (milnorKNormRing k E x) =
      weightedNormSum (L := L)
        (Algebra.TensorProduct.includeRight : E →ₐ[k] L ⊗[k] E).toRingHom x :=
  weightedNormSum_tensor_aux _ k L E rfl x

end Stacks.Chow

end
