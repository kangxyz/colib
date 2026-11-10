/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRoot.RationalCoefficient
public import Colib.FieldTheory.AdjoinRoot.NormalScalar
public import Colib.RingTheory.KTheory.MilnorK.Norm.NormalPrimeChosenComparison

/-!
# The native chosen norm in the actual rational constant presentation

For a normal prime-degree root field in characteristic zero, identify its
native chosen rational-function norm with the native simple norm at the literal
constant polynomial. No rational-function norm or transfer is defined here.

The actual root-field equivalence, normality after coefficient extension, and
the rational extension degree are proved from the original polynomial, rather
than assumed as comparison data. The result is the next input for the finite
linear and infinity residue squares, not yet either residue square or a tower law.
-/

@[expose] public noncomputable section

open Polynomial
open scoped RatFunc
attribute [local instance] Polynomial.algebra

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] {d : ℕ}

/-- The literal constant polynomial, as the existing native closed point of the
same degree. This is not a new residue-field or norm construction. -/
def MonicIrreducibleOfDegree.ratFunc (p : MonicIrreducibleOfDegree k d) :
    MonicIrreducibleOfDegree (RatFunc k) d :=
  ⟨(poly p).map RatFunc.C, (monic p).map _,
    (monic p).irreducible_map_ratFunc_C (irreducible p),
    (Polynomial.natDegree_map _).trans (natDegree_eq p)⟩

local instance (p : MonicIrreducibleOfDegree k d) : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance (p : MonicIrreducibleOfDegree k d) :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable [CharZero k] (p : MonicIrreducibleOfDegree k d)
  [Normal k (AdjoinRoot (poly p))]

/-- In normal prime degree the native chosen norm on the actual rational field
is the simple norm in its proved literal constant-polynomial presentation. -/
theorem milnorKNormRing_ratFunc_eq_simpleMilnorNorm (hp : d.Prime)
    (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x =
      simpleMilnorNorm p.ratFunc
        (milnorKRingMap
          (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom x) := by
  let : Fact (Irreducible ((poly p).map (RatFunc.C : k →+* RatFunc k))) :=
    ⟨(monic p).irreducible_map_ratFunc_C (irreducible p)⟩
  let : IsSplittingField (RatFunc k)
      (AdjoinRoot ((poly p).map (RatFunc.C : k →+* RatFunc k)))
      ((poly p).map (RatFunc.C : k →+* RatFunc k)) :=
    AdjoinRoot.isSplittingField_of_dvd_map (monic p) dvd_rfl
  let : Normal (RatFunc k)
      (AdjoinRoot ((poly p).map (RatFunc.C : k →+* RatFunc k))) :=
    Normal.of_isSplittingField ((poly p).map (RatFunc.C : k →+* RatFunc k))
  let : Normal (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
    Normal.of_algEquiv (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p))
  have hprime : Nat.Prime
      (Module.finrank (RatFunc k) (RatFunc (AdjoinRoot (poly p)))) := by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot, natDegree_eq]
    exact hp
  exact milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime hprime p.ratFunc
    (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm x

/-- The actual chosen normal-prime norm commutes with adjoining the rational
coordinate on every original Milnor class. Both sides use native chosen norms. -/
theorem milnorKNormRing_ratFunc_map_C (hp : d.Prime)
    (x : MilnorKRing (AdjoinRoot (poly p))) :
    milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
        (milnorKRingMap (RatFunc.C : AdjoinRoot (poly p) →+*
          RatFunc (AdjoinRoot (poly p))) x) =
      milnorKRingMap (RatFunc.C : k →+* RatFunc k)
        (milnorKNormRing k (AdjoinRoot (poly p)) x) := by
  let : Fact (Irreducible ((poly p).map (RatFunc.C : k →+* RatFunc k))) :=
    ⟨(monic p).irreducible_map_ratFunc_C (irreducible p)⟩
  have hcomp : (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom.comp
      (RatFunc.C : AdjoinRoot (poly p) →+* RatFunc (AdjoinRoot (poly p))) =
      AdjoinRoot.map (RatFunc.C : k →+* RatFunc k)
        (poly p) ((poly p).map RatFunc.C) dvd_rfl := by
    apply RingHom.ext
    intro z
    exact AdjoinRoot.rationalCoefficientAlgEquiv_symm_C (poly p) (monic p) z
  have hmap : milnorKRingMap
      (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom
      (milnorKRingMap (RatFunc.C : AdjoinRoot (poly p) →+*
        RatFunc (AdjoinRoot (poly p))) x) =
      milnorKRingMap (AdjoinRoot.map (RatFunc.C : k →+* RatFunc k)
        (poly p) ((poly p).map RatFunc.C) dvd_rfl) x := by
    calc
      _ = milnorKRingMap
          ((AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom.comp
            (RatFunc.C : AdjoinRoot (poly p) →+* RatFunc (AdjoinRoot (poly p)))) x :=
        milnorKRingMap_comp_apply RatFunc.C
          (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom x
      _ = _ := congrArg (fun f : AdjoinRoot (poly p) →+*
          AdjoinRoot ((poly p).map (RatFunc.C : k →+* RatFunc k)) =>
          milnorKRingMap f x) hcomp
  have hprime : Nat.Prime (Module.finrank k (AdjoinRoot (poly p))) := by
    rw [(AdjoinRoot.powerBasis (ne_zero p)).finrank, AdjoinRoot.powerBasis_dim,
      natDegree_eq]
    exact hp
  let e : AdjoinRoot (poly p) ≃ₐ[k] (k[X] ⧸ Ideal.span {poly p}) :=
    { toRingEquiv := RingEquiv.refl _
      commutes' := fun _ => rfl }
  have hchosen : milnorKNormRing k (AdjoinRoot (poly p)) x = simpleMilnorNorm p x := by
    calc
      _ = simpleMilnorNorm p (milnorKRingMap e.toRingHom x) :=
        milnorKNormRing_eq_simpleMilnorNorm_of_algEquiv_of_normal_prime hprime p e x
      _ = _ := congrArg (simpleMilnorNorm p) (show milnorKRingMap e.toRingHom x = x from
        milnorKRingMap_id_apply x)
  calc
    _ = simpleMilnorNorm p.ratFunc
        (milnorKRingMap
          (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom
          (milnorKRingMap RatFunc.C x)) :=
      milnorKNormRing_ratFunc_eq_simpleMilnorNorm p hp _
    _ = simpleMilnorNorm p.ratFunc
        (milnorKRingMap (AdjoinRoot.map (RatFunc.C : k →+* RatFunc k)
          (poly p) ((poly p).map RatFunc.C) dvd_rfl) x) :=
      congrArg (simpleMilnorNorm p.ratFunc) hmap
    _ = milnorKRingMap (RatFunc.C : k →+* RatFunc k) (simpleMilnorNorm p x) :=
      (simpleMilnorNorm_map_of_poly_eq_map
        (RatFunc.C : k →+* RatFunc k) p p.ratFunc rfl x).symm
    _ = _ := congrArg (milnorKRingMap (RatFunc.C : k →+* RatFunc k))
      hchosen.symm

end Stacks.Chow
