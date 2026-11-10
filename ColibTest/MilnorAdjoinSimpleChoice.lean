module

import Colib.RingTheory.KTheory.MilnorK.Norm.AdjoinSimpleChoice

noncomputable section

open Polynomial IntermediateField Stacks.Chow

universe u

example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    {a : L} (h : IsIntegral K a) [FiniteDimensional K K⟮a⟯]
    (x : MilnorKRing K⟮a⟯) :
    milnorKNormRing K K⟮a⟯ x = milnorKNormAdjoinSimple K h x :=
  milnorKNormRing_adjoinSimple_apply h x

example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    {a : L} (h : IsIntegral K a) [FiniteDimensional K K⟮a⟯] :
    milnorKNormRing K K⟮a⟯ = milnorKNormAdjoinSimple K h :=
  milnorKNormRing_adjoinSimple h

example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a : L) (x : MilnorKRing L) :
    milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)
        (milnorKNormRing K⟮a⟯ L x) = milnorKNormRing K L x :=
  milnorKNormRing_adjoinSimple_step_apply a x

example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a : L) :
    (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)).comp
      (milnorKNormRing K⟮a⟯ L) = milnorKNormRing K L :=
  milnorKNormRing_adjoinSimple_step a

example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a b : L) (x : MilnorKRing L) :
    milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)
        (milnorKNormRing K⟮a⟯ L x) =
      milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) b)
        (milnorKNormRing K⟮b⟯ L x) :=
  milnorKNormRing_adjoinSimple_choice_apply a b x

example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a b : L) :
    (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)).comp
        (milnorKNormRing K⟮a⟯ L) =
      (milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) b)).comp
        (milnorKNormRing K⟮b⟯ L) :=
  milnorKNormRing_adjoinSimple_choice a b

example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (a : L) (n : ℕ) (x : MilnorKTheory L n) :
    milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) a)
        (milnorKNorm K⟮a⟯ L n x : MilnorKRing K⟮a⟯) =
      (milnorKNorm K L n x : MilnorKRing K) :=
  coe_milnorKNorm_adjoinSimple_step a n x

-- A base-field element is permitted; the first step need not decrease the degree.
example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    [FiniteDimensional K L] (c : K) (b : L) (x : MilnorKRing L) :
    milnorKNormAdjoinSimple K
        (Algebra.IsIntegral.isIntegral (R := K) (algebraMap K L c))
        (milnorKNormRing K⟮algebraMap K L c⟯ L x) =
      milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) b)
        (milnorKNormRing K⟮b⟯ L x) :=
  milnorKNormRing_adjoinSimple_choice_apply (algebraMap K L c) b x

-- The lower comparison needs only integrality, even in an infinite ambient field.
example
    {K L : Type u} [Field K] [Field L] [Algebra K L] [CharZero K]
    {a : L} (h : IsIntegral K a) (x : MilnorKRing K⟮a⟯) :
    let _ : FiniteDimensional K K⟮a⟯ := IntermediateField.adjoin.finiteDimensional h
    milnorKNormRing K K⟮a⟯ x = milnorKNormAdjoinSimple K h x := by
  intro hFinite
  exact milnorKNormRing_adjoinSimple_apply h x

end
