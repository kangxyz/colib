module

import Colib.AlgebraicGeometry.EtaleCohomology.ClosedCurveDivisorRoot

open CategoryTheory AlgebraicGeometry Stacks.Divisors Stacks.Kummer

universe u

variable {k : Type u} [Field k] [IsSepClosed k] {X : Scheme.{u}}
  (q : X ⟶ Spec (.of k)) [IsCurve k q] [Smooth q] [IsProper q]

-- The degree formula keeps the whole finite scheme, with no reducedness assumption.
example (D E : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    [IsEffectiveCartierDivisor E] (hdim : topologicalKrullDim X ≤ 1) :
    picardDegree k q hdim
      (Stacks.GluePicard.picardModelAddEquiv X.toRingedSpace
        (X.picardClass (differenceSheaf D E) (isInvertible_differenceSheaf D E))) =
      (lengthOver q D : ℤ) - (lengthOver q E : ℤ) :=
  picardDegree_differenceSheaf D E q hdim

-- Composite exponent and arbitrary equal rank, without a degree-zero certificate.
example (D E : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    [IsEffectiveCartierDivisor E] (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ q) d]
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (E.subschemeι ≫ q) d]
    (hn : IsUnit (6 : k)) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (6 : ℤ) ≅
        differenceSheaf D E) :=
  exists_schemeTensorPower_iso_differenceSheaf_of_rank_eq q D E d hn

-- The section endpoint asks for neither Cartier nor degree nor rank certificates.
example [SmoothOfRelativeDimension 1 q]
    (s t : Spec (.of k) ⟶ X) (hs : s ≫ q = 𝟙 _) (ht : t ≫ q = 𝟙 _) :
    ∃ (M : X.Modules) (hM : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf M),
      Nonempty (Stacks.SheafOfModules.schemeTensorPower X M hM (1 : ℤ) ≅
        differenceSheaf s.ker t.ker) :=
  exists_schemeTensorPower_iso_sectionKernel_differenceSheaf q s t hs ht (by simp)
