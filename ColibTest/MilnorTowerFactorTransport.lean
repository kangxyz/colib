module

import Colib.RingTheory.KTheory.MilnorK.Norm.TowerFactorTransport

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

attribute [local instance] Stacks.Chow.towerTransport_nativeIrreducible

variable {k : Type u} [Field k] {c d e : ℕ}
  (p : MonicIrreducibleOfDegree k d) (h : MonicIrreducibleOfDegree k e)
  (f : AdjoinRoot (poly p) →ₐ[k] AdjoinRoot (poly h))

local notation "E" => AdjoinRoot (poly p)
local notation "H" => AdjoinRoot (poly h)

variable (a : MonicIrreducibleOfDegree k c)
  (g : AdjoinRoot (poly a) →ₐ[k] AdjoinRoot (poly p))

local notation "A" => AdjoinRoot (poly a)

/-- The actual norm transport retains the explicit native quotient-domain statement. -/
example :
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
  have ht := simpleMilnorNorm_towerFactorAssoc_map (k := k) (d := d) (e := e)
    p h f (c := c) a g
  exact ht

/-- The actual map square has exactly the original coefficient-factor maps. -/
example :
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
  have ht := milnorKRingMap_towerFactorAssoc_map_map (k := k) (d := d) (e := e)
    p h f (c := c) a g
  exact ht

end
