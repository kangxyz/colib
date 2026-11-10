/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalOriginResidue
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalTranslation
public import Colib.RingTheory.KTheory.MilnorK.Residue.LinearPlaceTranslation

/-!
# The original normal-prime rational norm and every linear finite place

Actual native Taylor translation moves a linear place to the origin, preserving
its real local and residue maps. The proved translation square for the original
chosen norm and the proved origin square therefore give the finite linear square.
The statements retain the native polynomial residue and literal original point.
No finite-place sum, branch reindexing, or norm tower law is assumed here.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

local instance rationalLinearResidue_isMaximal_span_X_sub_C
    {K : Type u} [Field K] (b : K) :
    (Ideal.span ({X - C b} : Set K[X])).IsMaximal :=
  Stacks.Chow.isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C b)

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] [CharZero k] {d : ℕ}
  (p : MonicIrreducibleOfDegree k d) (a : k)

local instance rationalLinearResidue_factIrreducible : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance rationalLinearResidue_finiteRoot : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance rationalLinearResidue_finiteRatFuncRoot :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable [Normal k (AdjoinRoot (poly p))]

/-- On every homogeneous class, the original finite linear-place residue of the
chosen rational norm is the original coefficient-field norm of the upper residue.
Both residues are the native polynomial residues, evaluated by the native linear
quotient equivalences; no alternate residue or rational norm is introduced. -/
theorem monicIrreducibleResidue_X_sub_C_milnorKNorm_ratFunc (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) (n + 1)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a,
            natDegree_X_sub_C a⟩ : MonicIrreducibleOfDegree k 1)
          (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
            (n + 1) x : MilnorKRing (RatFunc k))) =
      milnorKNormRing k (AdjoinRoot (poly p))
        (milnorKRingMap
          (quotientSpanXSubCAlgEquiv (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom
          (monicIrreducibleResidue
            (⟨X - C (algebraMap k (AdjoinRoot (poly p)) a),
              monic_X_sub_C _, irreducible_X_sub_C _, natDegree_X_sub_C _⟩ :
                MonicIrreducibleOfDegree (AdjoinRoot (poly p)) 1)
            (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))))) := by
  calc
    _ = (milnorKTheoryMap (residueFieldAtOriginEquiv k).symm.toRingHom n
        (dvrMilnorTameSymbol' (localRingAtOrigin k) (RatFunc k) n
          (milnorKTheoryMap (RatFunc.laurent a).toRingHom (n + 1)
            (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
              (n + 1) x))) : MilnorKRing k) :=
      monicIrreducibleResidue_X_sub_C_coe_eq_origin a n _
    _ = (milnorKNorm k (AdjoinRoot (poly p)) n
        (milnorKTheoryMap
          (residueFieldAtOriginEquiv (AdjoinRoot (poly p))).symm.toRingHom n
          (dvrMilnorTameSymbol' (localRingAtOrigin (AdjoinRoot (poly p)))
            (RatFunc (AdjoinRoot (poly p))) n
            (milnorKTheoryMap
              (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom
              (n + 1) x))) : MilnorKRing k) := by
      rw [← milnorKNorm_ratFunc_map_laurent p a hp (n + 1) x]
      exact congrArg (fun y : MilnorKTheory k n => (y : MilnorKRing k))
        (dvrMilnorTameSymbol'_milnorKNorm_ratFunc_origin p hp n
          (milnorKTheoryMap
            (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom (n + 1) x))
    _ = _ := congrArg (milnorKNormRing k (AdjoinRoot (poly p)))
      (monicIrreducibleResidue_X_sub_C_coe_eq_origin
        (algebraMap k (AdjoinRoot (poly p)) a) n x).symm

end Stacks.Chow
