/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.RationalConstant
public import Colib.FieldTheory.RatFunc.LaurentMap

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

namespace AdjoinRoot

variable {k : Type*} [Field k] (a : k) (p : k[X]) [Fact (Irreducible p)]

/-- The original root-field comparison intertwines the actual coefficient
quotient map and the native translation of the rational coordinate. -/
theorem rationalCoefficientAlgEquiv_map_laurent (hp : p.Monic)
    (x : AdjoinRoot (p.map (RatFunc.C : k →+* RatFunc k))) :
    AdjoinRoot.rationalCoefficientAlgEquiv p hp
      (AdjoinRoot.map (RatFunc.laurent a).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C)
        (by rw [RatFunc.map_C_laurent a]) x) =
      RatFunc.laurent (algebraMap k (AdjoinRoot p) a)
        (AdjoinRoot.rationalCoefficientAlgEquiv p hp x) := by
  have h : (AdjoinRoot.rationalCoefficientAlgEquiv p hp).toRingHom.comp
      (AdjoinRoot.map (RatFunc.laurent a).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C)
        (by rw [RatFunc.map_C_laurent a])) =
      (RatFunc.laurent (algebraMap k (AdjoinRoot p) a)).toRingHom.comp
        (AdjoinRoot.rationalCoefficientAlgEquiv p hp).toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · apply RingHom.ext
      intro r
      change AdjoinRoot.rationalCoefficientAlgEquiv p hp
        (AdjoinRoot.map _ _ _ _ (AdjoinRoot.of _ r)) =
        RatFunc.laurent (algebraMap k (AdjoinRoot p) a)
          (AdjoinRoot.rationalCoefficientAlgEquiv p hp (AdjoinRoot.of _ r))
      rw [AdjoinRoot.map_of]
      change AdjoinRoot.rationalCoefficientAlgEquiv p hp
        (algebraMap (RatFunc k) _ (RatFunc.laurent a r)) =
        RatFunc.laurent (algebraMap k (AdjoinRoot p) a)
          (AdjoinRoot.rationalCoefficientAlgEquiv p hp (algebraMap (RatFunc k) _ r))
      rw [AlgEquiv.commutes, AlgEquiv.commutes, RatFunc.algebraMap_eq_mapRingHom]
      exact (RatFunc.laurent_mapRingHom (algebraMap k (AdjoinRoot p)) a r).symm
    · change AdjoinRoot.rationalCoefficientAlgEquiv p hp
        (AdjoinRoot.map _ _ _ _ (AdjoinRoot.root _)) =
        RatFunc.laurent (algebraMap k (AdjoinRoot p) a)
          (AdjoinRoot.rationalCoefficientAlgEquiv p hp (AdjoinRoot.root _))
      simp only [AdjoinRoot.map_root, AdjoinRoot.rationalCoefficientAlgEquiv_root]
      exact (RatFunc.laurent_C (algebraMap k (AdjoinRoot p) a) (AdjoinRoot.root p)).symm
  exact RingHom.congr_fun h x

/-- The inverse comparison carries native rational translation to the
original coefficient map on the mapped polynomial quotient. -/
theorem rationalCoefficientAlgEquiv_symm_laurent (hp : p.Monic)
    (x : RatFunc (AdjoinRoot p)) :
    (AdjoinRoot.rationalCoefficientAlgEquiv p hp).symm
      (RatFunc.laurent (algebraMap k (AdjoinRoot p) a) x) =
      AdjoinRoot.map (RatFunc.laurent a).toRingHom
        (p.map RatFunc.C) (p.map RatFunc.C)
        (by rw [RatFunc.map_C_laurent a])
        ((AdjoinRoot.rationalCoefficientAlgEquiv p hp).symm x) := by
  apply (AdjoinRoot.rationalCoefficientAlgEquiv p hp).injective
  rw [AlgEquiv.apply_symm_apply, rationalCoefficientAlgEquiv_map_laurent,
    AlgEquiv.apply_symm_apply]

end AdjoinRoot

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] [CharZero k] {d : ℕ}
  (p : MonicIrreducibleOfDegree k d) (a : k)

local instance rationalTranslation_factIrreducible : Fact (Irreducible (poly p)) := ⟨irreducible p⟩

local instance rationalTranslation_finiteRoot : Module.Finite k (AdjoinRoot (poly p)) :=
  (AdjoinRoot.powerBasis (ne_zero p)).finite

local instance rationalTranslation_finiteRatFuncRoot :
    Module.Finite (RatFunc k) (RatFunc (AdjoinRoot (poly p))) :=
  FiniteDimensional.of_finrank_pos (by
    rw [AdjoinRoot.finrank_ratFunc_adjoinRoot]
    exact (irreducible p).natDegree_pos)

variable [Normal k (AdjoinRoot (poly p))]

/-- The native chosen rational norm commutes with the original rational translation,
for every whole-ring class in normal prime degree and characteristic zero. -/
theorem milnorKNormRing_ratFunc_map_laurent (hp : d.Prime)
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
      milnorKNormRing_ratFunc_eq_simpleMilnorNorm p hp _
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
      (milnorKNormRing_ratFunc_eq_simpleMilnorNorm p hp x).symm


/-- The same original norm square in every homogeneous degree. -/
theorem milnorKNorm_ratFunc_map_laurent (hp : d.Prime) (n : ℕ)
    (x : MilnorKTheory (RatFunc (AdjoinRoot (poly p))) n) :
    milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n
        (milnorKTheoryMap
          (RatFunc.laurent (algebraMap k (AdjoinRoot (poly p)) a)).toRingHom n x) =
      milnorKTheoryMap (RatFunc.laurent a).toRingHom n
        (milnorKNorm (RatFunc k) (RatFunc (AdjoinRoot (poly p))) n x) := by
  simp only [milnorKTheoryMap_eq_transport]
  apply Subtype.ext
  exact milnorKNormRing_ratFunc_map_laurent p a hp (x : MilnorKRing _)

end Stacks.Chow
