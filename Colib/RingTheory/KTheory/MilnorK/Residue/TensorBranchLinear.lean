/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.AdjoinRoot.TensorFactorMaps
public import Colib.RingTheory.KTheory.MilnorK.Norm.PolynomialResidueMap
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The native linear residue on the opposite tensor branch

Let `q` be an actual native monic irreducible factor of `h` over `AdjoinRoot p`.
The complete tensor-factor bijection determines the opposite factor, its actual
coefficient map, and its actual quotient equivalence. Evaluation at the original
root of `h` identifies the linear residue after that coefficient restriction with
the original residue at `q`, transported through that quotient equivalence.

The weighted formula holds in arbitrary characteristic. Separability of the
original polynomial `h` proves that its actual linear-factor multiplicity is one;
the characteristic-zero endpoint derives separability from original irreducibility.
No linear point, field, coefficient map, residue, or norm is replaced by a model.

The original native finite residue is also recovered by coefficient restriction
to its own root field and evaluation of the linear residue there. Its actual
quotient-evaluation composite is proved to be the identity.

The inputs are the native declarations in `AdjoinRoot/TensorFactorMaps`,
`Norm/PolynomialResidueMap`, Mathlib's `AdjoinRoot.ringHom_ext`, and
`Polynomial.quotientSpanXSubCAlgEquiv`. This is the single-branch restriction
ingredient, not a finite-place norm sum, norm comparison, diamond, or tower law.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

universe u

local instance tensorBranchLinear_isMaximal_span_X_sub_C
    {K : Type u} [Field K] (b : K) :
    (Ideal.span ({X - C b} : Set K[X])).IsMaximal :=
  Stacks.Chow.isMaximal_span_singleton_of_irreducible_polynomial (irreducible_X_sub_C b)

attribute [local instance] Ideal.Quotient.field

variable {k : Type u} [Field k] (p h : k[X])
  [Fact (Irreducible p)] [Fact (Irreducible h)]

local notation "E" => AdjoinRoot p
local notation "H" => AdjoinRoot h

variable (q : {q : Σ d : ℕ, MonicIrreducibleOfDegree (AdjoinRoot p) d //
  poly q.2 ∣ h.map (algebraMap k (AdjoinRoot p))})

local instance tensorBranchLinear_factIrreducible_factor :
    Fact (Irreducible (poly q.1.2)) :=
  ⟨irreducible q.1.2⟩

local instance tensorBranchLinear_factIrreducible_opposite :
    Fact (Irreducible (poly (AdjoinRoot.tensorSwapFactorIndexEquiv p h q).1.2)) :=
  ⟨irreducible (AdjoinRoot.tensorSwapFactorIndexEquiv p h q).1.2⟩

local notation "r" => AdjoinRoot.tensorSwapFactorIndexEquiv p h q
local notation "F" => AdjoinRoot (poly r.1.2)
local notation "φ" =>
  (AdjoinRoot.map (algebraMap k H) p (poly r.1.2) r.2 : E →+* F)
local notation "a" => algebraMap H F (AdjoinRoot.root h)

namespace AdjoinRoot

/-- The native quotient evaluation after the actual opposite coefficient-factor
map is precisely the actual tensor-factor quotient equivalence. -/
theorem quotientSpanXSubCAlgEquiv_comp_tensorSwapFactor_map :
    (quotientSpanXSubCAlgEquiv a).toRingHom.comp
        (AdjoinRoot.map φ (poly q.1.2) (X - C a)
          (tensorSwapFactor_linear_dvd p h q)) =
      (tensorSwapFactorQuotientEquiv p h q).toRingHom := by
  let hdiv : (X - C a : F[X]) ∣ (poly q.1.2).map φ :=
    tensorSwapFactor_linear_dvd p h q
  let f : (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
      (F[X] ⧸ Ideal.span {(X - C a : F[X])}) :=
    AdjoinRoot.map φ (poly q.1.2) (X - C a : F[X]) hdiv
  let g : (F[X] ⧸ Ideal.span {(X - C a : F[X])}) →+* F :=
    (quotientSpanXSubCAlgEquiv a).toRingHom
  let e : (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F :=
    (tensorSwapFactorQuotientEquiv p h q).toRingHom
  change g.comp f = e
  apply AdjoinRoot.ringHom_ext (p := poly q.1.2)
  · apply RingHom.ext
    intro c
    change g (f (AdjoinRoot.of (poly q.1.2) c)) = e (AdjoinRoot.of (poly q.1.2) c)
    have hf : f (AdjoinRoot.of (poly q.1.2) c) =
        algebraMap F (F[X] ⧸ Ideal.span {(X - C a : F[X])}) (φ c) :=
      AdjoinRoot.map_of φ (poly q.1.2) (X - C a : F[X]) hdiv c
    have hg : g (algebraMap F (F[X] ⧸ Ideal.span {(X - C a : F[X])}) (φ c)) = φ c :=
      (quotientSpanXSubCAlgEquiv a).commutes (φ c)
    have he : e (AdjoinRoot.of (poly q.1.2) c) = φ c :=
      tensorSwapFactorQuotientEquiv_algebraMap p h q c
    exact (congrArg g hf).trans (hg.trans he.symm)
  · change g (f (AdjoinRoot.root (poly q.1.2))) = e (AdjoinRoot.root (poly q.1.2))
    have hf : f (AdjoinRoot.root (poly q.1.2)) =
        AdjoinRoot.root (X - C a : F[X]) :=
      AdjoinRoot.map_root φ (poly q.1.2) (X - C a : F[X]) hdiv
    have hg : g (AdjoinRoot.root (X - C a : F[X])) = a := by
      change quotientSpanXSubCAlgEquiv a (Ideal.Quotient.mk _ (X : F[X])) = a
      rw [quotientSpanXSubCAlgEquiv_mk, eval_X]
    have he : e (AdjoinRoot.root (poly q.1.2)) = a :=
      tensorSwapFactorQuotientEquiv_root p h q
    exact (congrArg g hf).trans (hg.trans he.symm)

/-- Separability of the original lower polynomial makes the actual opposite
linear branch simple. Separability is inherited by the original factor `q`. -/
theorem tensorSwapFactor_linear_multiplicity_of_separable (hh : h.Separable) :
    multiplicity (X - C a) ((poly q.1.2).map φ) = 1 := by
  have hqsep : (poly q.1.2).Separable :=
    (hh.map (f := algebraMap k E)).of_dvd q.2
  have hsep : ((poly q.1.2).map φ).Separable := hqsep.map
  have hdiv : (X - C a : F[X]) ∣ (poly q.1.2).map φ :=
    tensorSwapFactor_linear_dvd p h q
  apply Nat.le_antisymm
  · apply multiplicity_le_of_emultiplicity_le
    exact emultiplicity_le_one_of_separable (not_isUnit_X_sub_C a) hsep
  · exact Nat.succ_le_of_lt
      (multiplicity_pos_of_dvd hdiv
        (FiniteMultiplicity.of_not_isUnit (not_isUnit_X_sub_C a)
          (Polynomial.map_ne_zero (ne_zero q.1.2))))

/-- In characteristic zero, original irreducibility proves that the actual
opposite linear factor has multiplicity one. -/
theorem tensorSwapFactor_linear_multiplicity [CharZero k] :
    multiplicity (X - C a) ((poly q.1.2).map φ) = 1 :=
  tensorSwapFactor_linear_multiplicity_of_separable p h q
    (Fact.out : Irreducible h).separable

end AdjoinRoot

namespace Stacks.Chow

/-- Evaluating the native linear residue on the actual opposite tensor branch
gives the original residue transported through the actual quotient equivalence,
with its actual multiplicity retained in arbitrary characteristic. -/
theorem monicIrreducibleResidue_tensorSwapFactor_linear_weighted
    (x : MilnorKRing (RatFunc E)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree F 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) x)) =
      (multiplicity (X - C a) ((poly q.1.2).map φ) : ℤ) •
        milnorKRingMap
          ((AdjoinRoot.tensorSwapFactorQuotientEquiv p h q).toRingHom :
            (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F)
          (monicIrreducibleResidue q.1.2 x) := by
  let l : MonicIrreducibleOfDegree F 1 :=
    ⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩
  let hdiv : poly l ∣ (poly q.1.2).map φ :=
    AdjoinRoot.tensorSwapFactor_linear_dvd p h q
  let f : (E[X] ⧸ Ideal.span {poly q.1.2}) →+*
      (F[X] ⧸ Ideal.span {poly l}) :=
    AdjoinRoot.map φ (poly q.1.2) (poly l) hdiv
  let g : (F[X] ⧸ Ideal.span {poly l}) →+* F :=
    (quotientSpanXSubCAlgEquiv a).toRingHom
  let e : (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F :=
    (AdjoinRoot.tensorSwapFactorQuotientEquiv p h q).toRingHom
  let z : MilnorKRing (E[X] ⧸ Ideal.span {poly q.1.2}) :=
    monicIrreducibleResidue q.1.2 x
  let m : ℤ := multiplicity (X - C a) ((poly q.1.2).map φ)
  have hsquare : g.comp f = e :=
    AdjoinRoot.quotientSpanXSubCAlgEquiv_comp_tensorSwapFactor_map p h q
  have hleft : milnorKRingMap g (milnorKRingMap f z) =
      milnorKRingMap (g.comp f) z :=
    milnorKRingMap_comp_apply f g z
  have hright : milnorKRingMap (g.comp f) z = milnorKRingMap e z :=
    congrArg (fun j : (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F =>
      milnorKRingMap j z) hsquare
  have hres : monicIrreducibleResidue l
      (milnorKRingMap
        (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) x) =
        m • milnorKRingMap f z :=
    monicIrreducibleResidue_mapRingHom φ q.1.2 l hdiv x
  calc
    _ = milnorKRingMap g (m • milnorKRingMap f z) :=
      congrArg (milnorKRingMap g) hres
    _ = m • milnorKRingMap g (milnorKRingMap f z) :=
      map_zsmul (milnorKRingMap g) _ _
    _ = m • milnorKRingMap e z :=
      congrArg (fun y : MilnorKRing F => m • y) (hleft.trans hright)

/-- For separable original `h`, the evaluated native linear residue is exactly
the original upper residue transported by the actual tensor quotient equivalence. -/
theorem monicIrreducibleResidue_tensorSwapFactor_linear_of_separable
    (hh : h.Separable) (x : MilnorKRing (RatFunc E)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree F 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) x)) =
      milnorKRingMap
          ((AdjoinRoot.tensorSwapFactorQuotientEquiv p h q).toRingHom :
            (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F)
        (monicIrreducibleResidue q.1.2 x) := by
  have hres := monicIrreducibleResidue_tensorSwapFactor_linear_weighted p h q x
  have hmult := AdjoinRoot.tensorSwapFactor_linear_multiplicity_of_separable p h q hh
  simpa only [hmult, Nat.cast_one, one_zsmul] using hres

/-- Characteristic-zero tensor-branch residue restriction, with the actual
linear multiplicity and actual quotient square proved rather than assumed. -/
theorem monicIrreducibleResidue_tensorSwapFactor_linear [CharZero k]
    (x : MilnorKRing (RatFunc E)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree F 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) x)) =
      milnorKRingMap
          ((AdjoinRoot.tensorSwapFactorQuotientEquiv p h q).toRingHom :
            (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F)
        (monicIrreducibleResidue q.1.2 x) :=
  monicIrreducibleResidue_tensorSwapFactor_linear_of_separable p h q
    (Fact.out : Irreducible h).separable x

end Stacks.Chow

namespace AdjoinRoot

/-- The original root gives a literal linear factor after the original
coefficient extension, without replacing the original polynomial quotient. -/
theorem X_sub_C_root_dvd_map (s : k[X]) :
    X - C (root s) ∣ s.map (algebraMap k (AdjoinRoot s)) := by
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot, Polynomial.eval_map,
    AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.eval₂_root s

/-- Evaluating the coefficient-factor map at the original root is the identity
on the original quotient. Both coefficients and the original root are retained. -/
theorem quotientSpanXSubCAlgEquiv_comp_map_root (s : k[X]) :
    (quotientSpanXSubCAlgEquiv (root s)).toRingHom.comp
        (AdjoinRoot.map (algebraMap k (AdjoinRoot s)) s (X - C (root s))
          (X_sub_C_root_dvd_map s)) =
      RingHom.id (AdjoinRoot s) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro c
    change quotientSpanXSubCAlgEquiv (root s)
        (AdjoinRoot.map (algebraMap k (AdjoinRoot s)) s (X - C (root s))
          (X_sub_C_root_dvd_map s) (AdjoinRoot.of s c)) = AdjoinRoot.of s c
    rw [AdjoinRoot.map_of]
    exact (quotientSpanXSubCAlgEquiv (root s)).commutes
      (algebraMap k (AdjoinRoot s) c)
  · change quotientSpanXSubCAlgEquiv (root s)
        (AdjoinRoot.map (algebraMap k (AdjoinRoot s)) s (X - C (root s))
          (X_sub_C_root_dvd_map s) (root s)) = root s
    rw [AdjoinRoot.map_root]
    change quotientSpanXSubCAlgEquiv (root s)
      (Ideal.Quotient.mk _ (X : (AdjoinRoot s)[X])) = root s
    rw [quotientSpanXSubCAlgEquiv_mk, eval_X]

end AdjoinRoot

namespace Stacks.Chow

section OriginalPlace

variable {d : ℕ} (s : MonicIrreducibleOfDegree k d)

local instance tensorBranchLinear_factIrreducible_original :
    Fact (Irreducible (poly s)) :=
  ⟨irreducible s⟩

local notation "L" => (k[X] ⧸ Ideal.span {poly s})
local notation "b" => (AdjoinRoot.root (poly s) : L)

/-- The original native residue is the evaluated linear residue after the actual
coefficient restriction to its own residue field. Separability proves simplicity;
the actual quotient-evaluation composite is proved to be the identity. -/
theorem monicIrreducibleResidue_eq_linearResidue_mapRingHom_of_separable
    (hs : (poly s).Separable) (x : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue s x =
      milnorKRingMap (quotientSpanXSubCAlgEquiv b).toRingHom
        (monicIrreducibleResidue
          (⟨X - C b, monic_X_sub_C b, irreducible_X_sub_C b, natDegree_X_sub_C b⟩ :
            MonicIrreducibleOfDegree L 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k L))
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom (algebraMap k L))) x)) := by
  let l : MonicIrreducibleOfDegree L 1 :=
    ⟨X - C b, monic_X_sub_C b, irreducible_X_sub_C b, natDegree_X_sub_C b⟩
  let hdiv : poly l ∣ (poly s).map (algebraMap k L) :=
    AdjoinRoot.X_sub_C_root_dvd_map (poly s)
  have hmult : multiplicity (poly l) ((poly s).map (algebraMap k L)) = 1 := by
    apply Nat.le_antisymm
    · apply multiplicity_le_of_emultiplicity_le
      exact emultiplicity_le_one_of_separable (irreducible l).not_isUnit hs.map
    · exact Nat.succ_le_of_lt
        (multiplicity_pos_of_dvd hdiv
          (FiniteMultiplicity.of_not_isUnit (irreducible l).not_isUnit
            (Polynomial.map_ne_zero (ne_zero s))))
  let f : (k[X] ⧸ Ideal.span {poly s}) →+* (L[X] ⧸ Ideal.span {poly l}) :=
    AdjoinRoot.map (algebraMap k L) (poly s) (poly l) hdiv
  let g : (L[X] ⧸ Ideal.span {poly l}) →+* (k[X] ⧸ Ideal.span {poly s}) :=
    (quotientSpanXSubCAlgEquiv b).toRingHom
  let z : MilnorKRing (k[X] ⧸ Ideal.span {poly s}) := monicIrreducibleResidue s x
  have hsquare : g.comp f = RingHom.id (k[X] ⧸ Ideal.span {poly s}) :=
    AdjoinRoot.quotientSpanXSubCAlgEquiv_comp_map_root (poly s)
  have hleft : milnorKRingMap g (milnorKRingMap f z) =
      milnorKRingMap (g.comp f) z :=
    milnorKRingMap_comp_apply f g z
  have hmiddle : milnorKRingMap (g.comp f) z =
      milnorKRingMap (RingHom.id (k[X] ⧸ Ideal.span {poly s})) z :=
    congrArg (fun j : (k[X] ⧸ Ideal.span {poly s}) →+*
        (k[X] ⧸ Ideal.span {poly s}) => milnorKRingMap j z) hsquare
  have hright : milnorKRingMap (RingHom.id (k[X] ⧸ Ideal.span {poly s})) z = z :=
    milnorKRingMap_id_apply z
  have hres : monicIrreducibleResidue l
      (milnorKRingMap
        (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k L))
          (Polynomial.nonZeroDivisors_le_comap_mapRingHom (algebraMap k L))) x) =
        milnorKRingMap f z := by
    have hraw := monicIrreducibleResidue_mapRingHom (algebraMap k L) s l hdiv x
    simpa only [hmult, Nat.cast_one, one_zsmul] using hraw
  exact ((congrArg (milnorKRingMap g) hres).trans
    (hleft.trans (hmiddle.trans hright))).symm

/-- Characteristic-zero self-evaluation of the original native finite residue.
There is no supplied residue square, multiplicity, or restriction-injectivity premise. -/
theorem monicIrreducibleResidue_eq_linearResidue_mapRingHom [CharZero k]
    (x : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue s x =
      milnorKRingMap (quotientSpanXSubCAlgEquiv b).toRingHom
        (monicIrreducibleResidue
          (⟨X - C b, monic_X_sub_C b, irreducible_X_sub_C b, natDegree_X_sub_C b⟩ :
            MonicIrreducibleOfDegree L 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k L))
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom (algebraMap k L))) x)) :=
  monicIrreducibleResidue_eq_linearResidue_mapRingHom_of_separable s
    (irreducible s).separable x

end OriginalPlace

end Stacks.Chow

end
