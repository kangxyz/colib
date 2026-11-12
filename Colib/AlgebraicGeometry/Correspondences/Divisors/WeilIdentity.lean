/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Divisors.FiniteFlat

/-!
# Transport of a literal Weil identity to native finite correspondences

The input is a literal equality in the original Weil group, not a graph-correspondence
certificate. The original four whole finite flat zero schemes define the native finite
correspondences. The correcting term is constructed as the native residue-weighted pushforward
of the actual principal cycle of the supplied rational unit. Its admissibility follows from
the literal identity. This is the additive transport step, not an identity producer, a
boundary-frame comparison, or the principal cylinder's graph-endpoint/Tor comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {C X Y S : Scheme.{u}} [IsNoetherian C] [IsIntegral C]
  (p : X ⟶ S) (t : Y ⟶ S) [IsSeparated t] [LocallyOfFiniteType t]
  (r : C ⟶ pullback p t) (I J A B : C.IdealSheafData)
  [IsFinite ((I.subschemeι ≫ r) ≫ pullback.fst p t)]
  [Flat ((I.subschemeι ≫ r) ≫ pullback.fst p t)]
  [IsFinite ((J.subschemeι ≫ r) ≫ pullback.fst p t)]
  [Flat ((J.subschemeι ≫ r) ≫ pullback.fst p t)]
  [IsFinite ((A.subschemeι ≫ r) ≫ pullback.fst p t)]
  [Flat ((A.subschemeι ≫ r) ≫ pullback.fst p t)]
  [IsFinite ((B.subschemeι ≫ r) ≫ pullback.fst p t)]
  [Flat ((B.subschemeι ≫ r) ≫ pullback.fst p t)]
  (hI : Stacks.Divisors.IsEffectiveCartierDivisor I)
  (hJ : Stacks.Divisors.IsEffectiveCartierDivisor J)
  (hA : Stacks.Divisors.IsEffectiveCartierDivisor A)
  (hB : Stacks.Divisors.IsEffectiveCartierDivisor B)
  (n : ℕ) (f : (rationalFunctions C)ˣ)
  (hWeil : effectiveCartierWeilDivisor I hI - effectiveCartierWeilDivisor J hJ =
    n • (effectiveCartierWeilDivisor A hA - effectiveCartierWeilDivisor B hB) +
      principalDivisor C f)

include hWeil in
/-- Additivity transports the literal Weil identity, preserving order, sign and exponent. -/
theorem finiteFlatDivisorCorrespondence_val_sub_eq_of_weilIdentity :
    (finiteFlatDivisorCorrespondence p t r I).val -
        (finiteFlatDivisorCorrespondence p t r J).val =
      n • ((finiteFlatDivisorCorrespondence p t r A).val -
        (finiteFlatDivisorCorrespondence p t r B).val) +
          AlgebraicGeometry.WeilDivisor.pushforwardCycle r (principalDivisor C f) := by
  have h := congrArg (AlgebraicGeometry.WeilDivisor.pushforwardCycle r) hWeil
  simpa only [map_sub, map_add, map_nsmul,
    pushforwardCycle_effectiveCartierWeilDivisor p t r I hI,
    pushforwardCycle_effectiveCartierWeilDivisor p t r J hJ,
    pushforwardCycle_effectiveCartierWeilDivisor p t r A hA,
    pushforwardCycle_effectiveCartierWeilDivisor p t r B hB] using h

include hWeil in
/-- The actual mapped principal cycle is admissible, as a consequence of the lower literal
identity and the four geometrically constructed whole finite flat correspondences. -/
theorem principalCyclePushforward_mem_finiteCorrespondences_of_weilIdentity :
    AlgebraicGeometry.WeilDivisor.pushforwardCycle r (principalDivisor C f) ∈
      finiteCorrespondences p t := by
  have h := finiteFlatDivisorCorrespondence_val_sub_eq_of_weilIdentity
    p t r I J A B hI hJ hA hB n f hWeil
  have hk : AlgebraicGeometry.WeilDivisor.pushforwardCycle r (principalDivisor C f) =
      (finiteFlatDivisorCorrespondence p t r I).val -
        (finiteFlatDivisorCorrespondence p t r J).val -
          n • ((finiteFlatDivisorCorrespondence p t r A).val -
            (finiteFlatDivisorCorrespondence p t r B).val) := by
    rw [h]
    abel
  rw [hk]
  exact (finiteCorrespondences p t).sub_mem
    ((finiteCorrespondences p t).sub_mem
      (finiteFlatDivisorCorrespondence p t r I).property
      (finiteFlatDivisorCorrespondence p t r J).property)
    ((finiteCorrespondences p t).nsmul_mem
      ((finiteCorrespondences p t).sub_mem
        (finiteFlatDivisorCorrespondence p t r A).property
        (finiteFlatDivisorCorrespondence p t r B).property) n)

/-- The correcting correspondence has the actual mapped principal cycle as its value;
the supplied lower Weil identity is used only to prove admissibility. -/
def principalCorrespondenceOfWeilIdentity : finiteCorrespondences p t :=
  ⟨AlgebraicGeometry.WeilDivisor.pushforwardCycle r (principalDivisor C f),
    principalCyclePushforward_mem_finiteCorrespondences_of_weilIdentity
      p t r I J A B hI hJ hA hB n f hWeil⟩

/-- The principal term is literally the native map of the native principal cycle of `f`. -/
theorem principalCorrespondenceOfWeilIdentity_val :
    (principalCorrespondenceOfWeilIdentity p t r I J A B hI hJ hA hB n f hWeil).val =
      noetherianCyclePushforward r
        (principalCycle C ((rationalFunctionsEquivFunctionField C).val f)) := by
  change noetherianCyclePushforward r
    (AlgebraicGeometry.WeilDivisor.toAlgebraicCycle (principalDivisor C f)) = _
  rw [AlgebraicGeometry.WeilDivisor.toAlgebraicCycle_principalDivisor]

/-- A previously proved literal Weil identity gives an equality in the unchanged native
finite-correspondence group. All four terms come from their whole original zero schemes. -/
@[colib_tag "COL-1051"]
theorem finiteFlatDivisorCorrespondence_sub_eq_of_weilIdentity :
    finiteFlatDivisorCorrespondence p t r I - finiteFlatDivisorCorrespondence p t r J =
      n • (finiteFlatDivisorCorrespondence p t r A - finiteFlatDivisorCorrespondence p t r B) +
        principalCorrespondenceOfWeilIdentity p t r I J A B hI hJ hA hB n f hWeil := by
  apply Subtype.ext
  exact finiteFlatDivisorCorrespondence_val_sub_eq_of_weilIdentity
    p t r I J A B hI hJ hA hB n f hWeil

end Stacks.Chow
