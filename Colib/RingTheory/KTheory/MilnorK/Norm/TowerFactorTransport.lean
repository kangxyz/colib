/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TowerFactorAssoc
public import Colib.RingTheory.KTheory.MilnorK.Norm.SimpleTowerDegreeOne

/-!
# Literal coefficient transport for native simple-norm towers

For a three-level tower, the exact mapped-polynomial equality transports the
iterated inner simple norm to the direct selected factor. The original quotient
map square gives the corresponding whole-ring Milnor map square. Neither
argument uses presentation independence or a norm tower premise.
-/

@[expose] public noncomputable section

open Polynomial

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

local instance towerTransport_nativeIrreducible {F : Type u} [Field F]
    {d : ℕ} (p : MonicIrreducibleOfDegree F d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

/-- Apply native Milnor functoriality to a proved three-map ring-hom equation. -/
private theorem map_three_comp_of_eq
    {F₀ F₁ F₂ F₃ : Type u} [Field F₀] [Field F₁] [Field F₂] [Field F₃]
    (m₀ : F₀ →+* F₁) (m₁ : F₁ →+* F₂) (m₂ : F₂ →+* F₃) (m : F₀ →+* F₃)
    (hc : m₂.comp (m₁.comp m₀) = m) (x : MilnorKRing F₀) :
    milnorKRingMap m₂ (milnorKRingMap m₁ (milnorKRingMap m₀ x)) = milnorKRingMap m x :=
  (congrArg (milnorKRingMap m₂) (milnorKRingMap_comp_apply m₀ m₁ x)).trans
    ((milnorKRingMap_comp_apply (m₁.comp m₀) m₂ x).trans
      (congrArg (fun ψ : F₀ →+* F₃ => milnorKRingMap ψ x) hc))

variable {k : Type u} [Field k] {d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

section ThreeLevels

variable {c : ℕ} (a : MonicIrreducibleOfDegree k c)
  (g : AdjoinRoot (poly a) →ₐ[k] AdjoinRoot (poly p))

local notation "A" => AdjoinRoot (poly a)

/-- Exact polynomial transport compares the actual iterated and direct inner norms.
The actual native factors and maps are named once, retaining all coefficient fields. -/
theorem simpleMilnorNorm_towerFactorAssoc_map :
    let qP : {q : Σ n : ℕ, MonicIrreducibleOfDegree A n //
        poly q.2 ∣ (poly p).map (algebraMap k A)} :=
      AdjoinRoot.towerFactor (poly a) (poly p) g
    let qH : {q : Σ n : ℕ, MonicIrreducibleOfDegree A n //
        poly q.2 ∣ (poly h).map (algebraMap k A)} :=
      AdjoinRoot.towerFactor (poly a) (poly h) (f.comp g)
    let hP : Fact (Irreducible (poly qP.1.2)) := ⟨irreducible qP.1.2⟩
    let hH : Fact (Irreducible (poly qH.1.2)) := ⟨irreducible qH.1.2⟩
    let fA : AdjoinRoot (poly qP.1.2) →ₐ[A] AdjoinRoot (poly qH.1.2) :=
      AdjoinRoot.towerFactorEmbeddingAlgHom (poly a) (poly p) (poly h) g f
    let qR : {q : Σ n : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly qP.1.2)) n //
        poly q.2 ∣ (poly qH.1.2).map (algebraMap A (AdjoinRoot (poly qP.1.2)))} :=
      @AdjoinRoot.towerFactor A (AdjoinRoot.instField (f := poly a))
        (poly qP.1.2) (poly qH.1.2) hP hH fA
    let qD : {q : Σ n : ℕ, MonicIrreducibleOfDegree E n //
        poly q.2 ∣ (poly h).map (algebraMap k E)} :=
      AdjoinRoot.towerFactor (poly p) (poly h) f
    let eP : AdjoinRoot (poly qP.1.2) →+* E :=
      (AdjoinRoot.towerFactorRingEquiv (poly a) (poly p) g).toRingHom
    let t : ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2}) →+*
        (E[X] ⧸ Ideal.span {poly qD.1.2}) :=
      (AdjoinRoot.towerFactorAssocRingEquiv (poly a) (poly p) (poly h) g f).toRingHom
    ∀ z : @MilnorKRing
      ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2})
      (Ideal.Quotient.field (Ideal.span {poly qR.1.2})),
      let lhs : @MilnorKRing E (AdjoinRoot.instField (f := poly p)) :=
        @milnorKRingMap (AdjoinRoot (poly qP.1.2)) E
        (AdjoinRoot.instField (f := poly qP.1.2)) (AdjoinRoot.instField (f := poly p)) eP
        (@simpleMilnorNorm (AdjoinRoot (poly qP.1.2))
          (AdjoinRoot.instField (f := poly qP.1.2)) qR.1.1 qR.1.2 z)
      let rhs : @MilnorKRing E (AdjoinRoot.instField (f := poly p)) :=
        @simpleMilnorNorm E (AdjoinRoot.instField (f := poly p)) qD.1.1 qD.1.2
        (@milnorKRingMap
          ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2})
          (E[X] ⧸ Ideal.span {poly qD.1.2})
          (Ideal.Quotient.field (Ideal.span {poly qR.1.2}))
          (Ideal.Quotient.field (Ideal.span {poly qD.1.2})) t z)
      lhs = rhs := by
  intro qP qH hP hH fA qR qD eP t z lhs rhs
  have hc : poly qD.1.2 = (poly qR.1.2).map eP :=
    (AdjoinRoot.towerFactorAssoc_poly_map (poly a) (poly p) (poly h) g f).symm
  let m : ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2}) →+*
      (E[X] ⧸ Ideal.span {poly qD.1.2}) :=
    AdjoinRoot.map eP (poly qR.1.2) (poly qD.1.2) (hc ▸ dvd_rfl)
  let Φ : (((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2}) →+*
      (E[X] ⧸ Ideal.span {poly qD.1.2})) →
      @MilnorKRing E (AdjoinRoot.instField (f := poly p)) := fun φ =>
    @simpleMilnorNorm E (AdjoinRoot.instField (f := poly p)) qD.1.1 qD.1.2
      (@milnorKRingMap
        ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2})
        (E[X] ⧸ Ideal.span {poly qD.1.2})
        (Ideal.Quotient.field (Ideal.span {poly qR.1.2}))
        (Ideal.Quotient.field (Ideal.span {poly qD.1.2})) φ z)
  have h₀ : @Eq (@MilnorKRing E (AdjoinRoot.instField (f := poly p))) lhs (Φ m) :=
    @simpleMilnorNorm_map_of_poly_eq_map (AdjoinRoot (poly qP.1.2)) E
      (AdjoinRoot.instField (f := poly qP.1.2)) (AdjoinRoot.instField (f := poly p))
      eP qR.1.1 qD.1.1 qR.1.2 qD.1.2 hc z
  have ht : @Eq (((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2}) →+*
      (E[X] ⧸ Ideal.span {poly qD.1.2})) t m :=
    AdjoinRoot.towerFactorAssocRingEquiv_toRingHom (poly a) (poly p) (poly h) g f
  have h₁ : @Eq (@MilnorKRing E (AdjoinRoot.instField (f := poly p))) (Φ m) rhs :=
    @congrArg
      (((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2}) →+*
        (E[X] ⧸ Ideal.span {poly qD.1.2}))
      (@MilnorKRing E (AdjoinRoot.instField (f := poly p))) m t Φ
      (@Eq.symm
        (((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2}) →+*
          (E[X] ⧸ Ideal.span {poly qD.1.2})) t m ht)
  exact @Eq.trans (@MilnorKRing E (AdjoinRoot.instField (f := poly p)))
    lhs (Φ m) rhs h₀ h₁

/-- The three-level quotient square retains both literal coefficient-factor maps. -/
theorem milnorKRingMap_towerFactorAssoc_map_map :
    let qP : {q : Σ n : ℕ, MonicIrreducibleOfDegree A n //
        poly q.2 ∣ (poly p).map (algebraMap k A)} :=
      AdjoinRoot.towerFactor (poly a) (poly p) g
    let qH : {q : Σ n : ℕ, MonicIrreducibleOfDegree A n //
        poly q.2 ∣ (poly h).map (algebraMap k A)} :=
      AdjoinRoot.towerFactor (poly a) (poly h) (f.comp g)
    let hP : Fact (Irreducible (poly qP.1.2)) := ⟨irreducible qP.1.2⟩
    let hH : Fact (Irreducible (poly qH.1.2)) := ⟨irreducible qH.1.2⟩
    let fA : AdjoinRoot (poly qP.1.2) →ₐ[A] AdjoinRoot (poly qH.1.2) :=
      AdjoinRoot.towerFactorEmbeddingAlgHom (poly a) (poly p) (poly h) g f
    let qR : {q : Σ n : ℕ, MonicIrreducibleOfDegree (AdjoinRoot (poly qP.1.2)) n //
        poly q.2 ∣ (poly qH.1.2).map (algebraMap A (AdjoinRoot (poly qP.1.2)))} :=
      @AdjoinRoot.towerFactor A (AdjoinRoot.instField (f := poly a))
        (poly qP.1.2) (poly qH.1.2) hP hH fA
    let qD : {q : Σ n : ℕ, MonicIrreducibleOfDegree E n //
        poly q.2 ∣ (poly h).map (algebraMap k E)} :=
      AdjoinRoot.towerFactor (poly p) (poly h) f
    let mH : H →+* (A[X] ⧸ Ideal.span {poly qH.1.2}) :=
      AdjoinRoot.map (algebraMap k A) (poly h) (poly qH.1.2) qH.2
    let mR : (A[X] ⧸ Ideal.span {poly qH.1.2}) →+*
        ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2}) :=
      AdjoinRoot.map (algebraMap A (AdjoinRoot (poly qP.1.2)))
        (poly qH.1.2) (poly qR.1.2) qR.2
    let t : ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2}) →+*
        (E[X] ⧸ Ideal.span {poly qD.1.2}) :=
      (AdjoinRoot.towerFactorAssocRingEquiv (poly a) (poly p) (poly h) g f).toRingHom
    let mD : H →+* (E[X] ⧸ Ideal.span {poly qD.1.2}) :=
      AdjoinRoot.map (algebraMap k E) (poly h) (poly qD.1.2) qD.2
    ∀ x : MilnorKRing H,
      let lhs := @milnorKRingMap
        ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2})
        (E[X] ⧸ Ideal.span {poly qD.1.2})
        (Ideal.Quotient.field (Ideal.span {poly qR.1.2}))
        (Ideal.Quotient.field (Ideal.span {poly qD.1.2})) t
        (@milnorKRingMap
          (A[X] ⧸ Ideal.span {poly qH.1.2})
          ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2})
          (Ideal.Quotient.field (Ideal.span {poly qH.1.2}))
          (Ideal.Quotient.field (Ideal.span {poly qR.1.2})) mR
          (@milnorKRingMap H (A[X] ⧸ Ideal.span {poly qH.1.2})
            (AdjoinRoot.instField (f := poly h))
            (Ideal.Quotient.field (Ideal.span {poly qH.1.2})) mH x))
      let rhs := @milnorKRingMap H (E[X] ⧸ Ideal.span {poly qD.1.2})
        (AdjoinRoot.instField (f := poly h))
        (Ideal.Quotient.field (Ideal.span {poly qD.1.2})) mD x
      lhs = rhs := by
  intro qP qH hP hH fA qR qD mH mR t mD x lhs rhs
  exact @map_three_comp_of_eq H
    (A[X] ⧸ Ideal.span {poly qH.1.2})
    ((AdjoinRoot (poly qP.1.2))[X] ⧸ Ideal.span {poly qR.1.2})
    (E[X] ⧸ Ideal.span {poly qD.1.2})
    (AdjoinRoot.instField (f := poly h))
    (Ideal.Quotient.field (Ideal.span {poly qH.1.2}))
    (Ideal.Quotient.field (Ideal.span {poly qR.1.2}))
    (Ideal.Quotient.field (Ideal.span {poly qD.1.2})) mH mR t mD
    (AdjoinRoot.towerFactorAssocRingEquiv_comp_adjoinRootMap_comp_adjoinRootMap
      (poly a) (poly p) (poly h) g f) x

end ThreeLevels

end Stacks.Chow

end
