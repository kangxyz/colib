/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalConstantSeparable
public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalTranslation

/-!
# The original normal-prime rational norm commutes with native translation

The constant root-field presentation intertwines the existing rational Taylor
maps. Its actual coefficient square proves translation equivariance of the
original chosen norm for normal prime-degree root extensions in characteristic
zero. No alternative rational field, residue, or norm is introduced. This is
an input to the finite linear residue square, not yet the full finite-place sum.
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
  (p : MonicIrreducibleOfDegree k d) (hsep : (poly p).Separable) (a : k)

local instance rationalTranslation_factIrreducibleSeparable :
    Fact (Irreducible (poly p)) := ⟨irreducible p⟩

local instance rationalTranslation_finiteRootSeparable : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance rationalTranslation_finiteRatFuncRootSeparable :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable [Normal k (AdjoinRoot (poly p))]

include hsep

/-- The native chosen rational norm commutes with the original rational translation,
for every whole-ring class in normal prime degree and a separable defining polynomial. -/
theorem milnorKNormRing_ratFunc_map_laurent_of_separable (hp : d.Prime)
    (x : MilnorKRing (RatFunc (AdjoinRoot (poly p)))) :
    milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p)))
        (milnorKRingMap (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom x) =
      milnorKRingMap (RatFunc.laurent a).toRingHom
        (milnorKNormRing (RatFunc k) (RatFunc (AdjoinRoot (poly p))) x) := by
  let : Fact (Irreducible ((poly p).map (RatFunc.C : k →+* RatFunc k))) :=
    ⟨(monic p).irreducible_map_ratFunc_C (irreducible p)⟩
  have hcomp : (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom.comp
      (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom =
      (AdjoinRoot.map (RatFunc.laurent a).toRingHom
        ((poly p).map RatFunc.C) ((poly p).map RatFunc.C)
        (by rw [RatFunc.map_C_laurent a])).comp
        (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom := by
    apply RingHom.ext
    intro z
    exact AdjoinRoot.rationalCoefficientAlgEquiv_symm_laurent a (poly p) (monic p) z
  have hmap : milnorKRingMap
      (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom
      (milnorKRingMap (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom x) =
      milnorKRingMap
        (AdjoinRoot.map (RatFunc.laurent a).toRingHom
          ((poly p).map RatFunc.C) ((poly p).map RatFunc.C)
          (by rw [RatFunc.map_C_laurent a]))
        (milnorKRingMap
          (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom x) := by
    calc
      _ = milnorKRingMap
          ((AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom.comp
            (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom) x :=
        milnorKRingMap_comp_apply _ _ x
      _ = milnorKRingMap
          ((AdjoinRoot.map (RatFunc.laurent a).toRingHom
            ((poly p).map RatFunc.C) ((poly p).map RatFunc.C)
            (by rw [RatFunc.map_C_laurent a])).comp
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom) x :=
        congrArg (fun f : RatFunc (AdjoinRoot (poly p)) →+*
          AdjoinRoot ((poly p).map (RatFunc.C : k →+* RatFunc k)) =>
          milnorKRingMap f x) hcomp
      _ = _ := (milnorKRingMap_comp_apply _ _ x).symm
  calc
    _ = simpleMilnorNorm p.ratFunc
        (milnorKRingMap
          (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom
          (milnorKRingMap (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom x)) :=
      milnorKNormRing_ratFunc_eq_simpleMilnorNorm_of_separable p hsep hp _
    _ = simpleMilnorNorm p.ratFunc
        (milnorKRingMap
          (AdjoinRoot.map (RatFunc.laurent a).toRingHom
            ((poly p).map RatFunc.C) ((poly p).map RatFunc.C)
            (by rw [RatFunc.map_C_laurent a]))
          (milnorKRingMap
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom x)) :=
      congrArg (simpleMilnorNorm p.ratFunc) hmap
    _ = milnorKRingMap (RatFunc.laurent a).toRingHom
        (simpleMilnorNorm p.ratFunc
          (milnorKRingMap
            (AdjoinRoot.rationalCoefficientAlgEquiv (poly p) (monic p)).symm.toRingHom x)) :=
      (simpleMilnorNorm_map_of_poly_eq_map
        (RatFunc.laurent a).toRingHom p.ratFunc p.ratFunc
        (RatFunc.map_C_laurent a (poly p)).symm _).symm
    _ = _ := congrArg (milnorKRingMap (RatFunc.laurent a).toRingHom)
      (milnorKNormRing_ratFunc_eq_simpleMilnorNorm_of_separable p hsep hp x).symm


/-- The same original norm square in every homogeneous degree. -/
theorem milnorKNorm_ratFunc_map_laurent_of_separable (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) n) :
    milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n
        (milnorKTheoryMap
          (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom n x) =
      milnorKTheoryMap (RatFunc.laurent a).toRingHom n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n x) := by
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_ratFunc_map_laurent_of_separable p hsep a hp (x : MilnorKRing _)

end Stacks.Chow
