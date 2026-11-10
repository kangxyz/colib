module

import Colib.RingTheory.KTheory.MilnorK.Norm.ChosenRecursion

noncomputable section

open Module IntermediateField Stacks.Chow

universe u

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] (h : ∃ a : L, a ∉ Set.range (algebraMap K L))

/-- The actual native additive norm uses the same literal selected witness. -/
example :
    milnorKNormRing K L =
      (milnorKNormAdjoinSimple K
        (Algebra.IsIntegral.isIntegral (R := K) h.choose)).comp
          (milnorKNormRing K⟮h.choose⟯ L) :=
  milnorKNormRing_eq_selected_step h

/-- The same recursion holds pointwise, without a tower-independence hypothesis. -/
example (x : MilnorKRing L) :
    milnorKNormRing K L x =
      milnorKNormAdjoinSimple K (Algebra.IsIntegral.isIntegral (R := K) h.choose)
        (milnorKNormRing K⟮h.choose⟯ L x) :=
  milnorKNormRing_selected_step_apply h x

end
