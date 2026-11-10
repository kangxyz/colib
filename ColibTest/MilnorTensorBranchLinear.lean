module

import Colib.RingTheory.KTheory.MilnorK.Residue.TensorBranchLinear

noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree AdjoinRoot

universe u

local instance testTensorBranchLinear_isMaximal_span_X_sub_C
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

local instance testTensorBranchLinear_factIrreducible_factor :
    Fact (Irreducible (poly q.1.2)) :=
  ⟨irreducible q.1.2⟩

local instance testTensorBranchLinear_factIrreducible_opposite :
    Fact (Irreducible (poly (AdjoinRoot.tensorSwapFactorIndexEquiv p h q).1.2)) :=
  ⟨irreducible (AdjoinRoot.tensorSwapFactorIndexEquiv p h q).1.2⟩

local notation "r" => tensorSwapFactorIndexEquiv p h q
local notation "F" => AdjoinRoot (poly r.1.2)
local notation "φ" =>
  (AdjoinRoot.map (algebraMap k H) p (poly r.1.2) r.2 : E →+* F)
local notation "a" => algebraMap H F (AdjoinRoot.root h)

example :
    (quotientSpanXSubCAlgEquiv a).toRingHom.comp
        (AdjoinRoot.map φ (poly q.1.2) (X - C a)
          (tensorSwapFactor_linear_dvd p h q)) =
      (tensorSwapFactorQuotientEquiv p h q).toRingHom :=
  quotientSpanXSubCAlgEquiv_comp_tensorSwapFactor_map p h q

example (hh : h.Separable) :
    multiplicity (X - C a) ((poly q.1.2).map φ) = 1 :=
  tensorSwapFactor_linear_multiplicity_of_separable p h q hh

example [CharZero k] :
    multiplicity (X - C a) ((poly q.1.2).map φ) = 1 :=
  tensorSwapFactor_linear_multiplicity p h q

example (x : MilnorKRing (RatFunc E)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree F 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) x)) =
      (multiplicity (X - C a) ((poly q.1.2).map φ) : ℤ) •
        milnorKRingMap
          ((tensorSwapFactorQuotientEquiv p h q).toRingHom :
            (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F)
          (monicIrreducibleResidue q.1.2 x) :=
  monicIrreducibleResidue_tensorSwapFactor_linear_weighted p h q x

example (hh : h.Separable) (x : MilnorKRing (RatFunc E)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree F 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) x)) =
      milnorKRingMap
          ((tensorSwapFactorQuotientEquiv p h q).toRingHom :
            (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F)
        (monicIrreducibleResidue q.1.2 x) :=
  monicIrreducibleResidue_tensorSwapFactor_linear_of_separable p h q hh x

example [CharZero k] (x : MilnorKRing (RatFunc E)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree F 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ)) x)) =
      milnorKRingMap
          ((tensorSwapFactorQuotientEquiv p h q).toRingHom :
            (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F)
        (monicIrreducibleResidue q.1.2 x) :=
  monicIrreducibleResidue_tensorSwapFactor_linear p h q x

example [CharZero k] (n : ℕ) (x : MilnorKTheory (RatFunc E) (n + 1)) :
    milnorKRingMap (quotientSpanXSubCAlgEquiv a).toRingHom
        (monicIrreducibleResidue
          (⟨X - C a, monic_X_sub_C a, irreducible_X_sub_C a, natDegree_X_sub_C a⟩ :
            MonicIrreducibleOfDegree F 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom φ)
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom φ))
            (x : MilnorKRing (RatFunc E)))) =
      milnorKRingMap
          ((tensorSwapFactorQuotientEquiv p h q).toRingHom :
            (E[X] ⧸ Ideal.span {poly q.1.2}) →+* F)
        (monicIrreducibleResidue q.1.2 (x : MilnorKRing (RatFunc E))) :=
  monicIrreducibleResidue_tensorSwapFactor_linear p h q x

example (s : k[X]) :
    X - C (root s) ∣ s.map (algebraMap k (AdjoinRoot s)) :=
  X_sub_C_root_dvd_map s

example (s : k[X]) :
    (quotientSpanXSubCAlgEquiv (root s)).toRingHom.comp
        (AdjoinRoot.map (algebraMap k (AdjoinRoot s)) s (X - C (root s))
          (X_sub_C_root_dvd_map s)) =
      RingHom.id (AdjoinRoot s) :=
  quotientSpanXSubCAlgEquiv_comp_map_root s

variable {d : ℕ} (s : MonicIrreducibleOfDegree k d)

local instance testTensorBranchLinear_factIrreducible_original :
    Fact (Irreducible (poly s)) :=
  ⟨irreducible s⟩

local notation "L" => (k[X] ⧸ Ideal.span {poly s})
local notation "b" => (AdjoinRoot.root (poly s) : L)

example (hs : (poly s).Separable) (x : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue s x =
      milnorKRingMap (quotientSpanXSubCAlgEquiv b).toRingHom
        (monicIrreducibleResidue
          (⟨X - C b, monic_X_sub_C b, irreducible_X_sub_C b, natDegree_X_sub_C b⟩ :
            MonicIrreducibleOfDegree L 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k L))
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom (algebraMap k L))) x)) :=
  monicIrreducibleResidue_eq_linearResidue_mapRingHom_of_separable s hs x

example [CharZero k] (x : MilnorKRing (RatFunc k)) :
    monicIrreducibleResidue s x =
      milnorKRingMap (quotientSpanXSubCAlgEquiv b).toRingHom
        (monicIrreducibleResidue
          (⟨X - C b, monic_X_sub_C b, irreducible_X_sub_C b, natDegree_X_sub_C b⟩ :
            MonicIrreducibleOfDegree L 1)
          (milnorKRingMap
            (RatFunc.mapRingHom (Polynomial.mapRingHom (algebraMap k L))
              (Polynomial.nonZeroDivisors_le_comap_mapRingHom (algebraMap k L))) x)) :=
  monicIrreducibleResidue_eq_linearResidue_mapRingHom s x
