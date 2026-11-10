/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.MilnorK.Norm.DVRConstantPrimeSeparable
public import Colib.RingTheory.AdjoinRoot.ResidueField
public import StacksFrontier.RingTheory.DiscreteValuationRing.MonicResidueIrreducible
public import StacksFrontier.RingTheory.AdjoinRoot.FractionRing

/-!
# The actual inert constant root algebra over a Japanese DVR

An irreducible residue polynomial constructs the finite local source DVR and
its original fraction-field map. Separability of the original constant
polynomial proves separability of the actual residue extension. The general
Japanese-DVR all-symbol theorem therefore gives the chosen norm-residue square
on these literal root algebras, without an assumed finite-local source model.

There is no assumption that the residue field of the base is separable over the
original constant field. The irreducibility hypothesis is the actual inert-case
condition, not a norm-square or residue-compatibility hypothesis.
-/

@[expose] public noncomputable section

open Polynomial IsLocalRing

universe u

namespace Stacks.Chow

open MonicIrreducibleOfDegree

attribute [local instance] Ideal.Quotient.field

variable (k R F : Type u) [Field k]
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra k R]
  [Field F] [Algebra R F] [IsFractionRing R F]
  [Algebra k F] [IsScalarTower k R F]
  {d : ℕ} (p : MonicIrreducibleOfDegree k d)
  [hred : Fact (Irreducible (((poly p).map (algebraMap k R)).map (residue R)))]

local notation "S" => AdjoinRoot (Polynomial.map (algebraMap k R) (poly p))
local notation "E" => AdjoinRoot (Polynomial.map (algebraMap k F) (poly p))

local instance inertConstant_nativeIrreducible : Fact (Irreducible (poly p)) :=
  ⟨irreducible p⟩

include hred in
/-- The actual generic polynomial is irreducible by reduction over the specified DVR.
The DVR is supplied explicitly because it cannot be inferred from the conclusion. -/
theorem inertConstant_genericIrreducible :
    Fact (Irreducible ((poly p).map (algebraMap k F))) := by
  constructor
  have h := AdjoinRoot.irreducible_map_algebraMap_of_irreducible_map_residue
    (K := F) ((monic p).map (algebraMap k R)) hred.out
  simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq k R F] using h

local instance inertConstant_isDomain : IsDomain S :=
  AdjoinRoot.isDomain_of_irreducible_map_residue ((monic p).map _) hred.out

local instance inertConstant_isLocalRing : IsLocalRing S :=
  AdjoinRoot.isLocalRing_of_irreducible_map_residue ((monic p).map _) hred.out

local instance inertConstant_isDiscreteValuationRing : IsDiscreteValuationRing S := by
  apply AdjoinRoot.isDiscreteValuationRing ((monic p).map _) hred.out
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance inertConstant_finite : Module.Finite R S :=
  ((monic p).map _).finite_adjoinRoot

local instance inertConstant_torsionFree : Module.IsTorsionFree R S := by
  apply AdjoinRoot.isTorsionFree_of_prime_of_degree_ne_zero
    (AdjoinRoot.prime_of_irreducible_map_residue ((monic p).map _) hred.out)
  apply ne_of_gt
  apply natDegree_pos_iff_degree_pos.mp
  rw [(monic p).natDegree_map]
  exact (irreducible p).natDegree_pos

local instance inertConstant_isLocalHom : IsLocalHom (algebraMap R S) := by
  rw [AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.isLocalHom_of_monic ((monic p).map _)

/-- The algebra structure induced by the canonical map between the two root quotients. -/
local instance inertConstantFractionAlgebra : Algebra S E :=
  (Stacks.AdjoinRootFraction.toMapAdjoinRoot F
    (p := (poly p).map (algebraMap k R))
    (q := (poly p).map (algebraMap k F))
    (by rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq k R F])).toAlgebra

local instance inertConstant_fractionTower : IsScalarTower R S E := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  exact (Stacks.AdjoinRootFraction.toMapAdjoinRoot_of F
    (p := (poly p).map (algebraMap k R))
    (q := (poly p).map (algebraMap k F))
    (by rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq k R F]) a).symm

local instance inertConstant_isFractionRing : IsFractionRing S E := by
  let : Fact (Irreducible ((poly p).map (algebraMap k F))) :=
    inertConstant_genericIrreducible k R F p
  exact Stacks.AdjoinRootFraction.isFractionRing_adjoinRoot F
    (p := (poly p).map (algebraMap k R))
    (q := (poly p).map (algebraMap k F))
    (by rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq k R F])
    (RingEquiv.refl _) ((monic p).map _) (by ext <;> rfl)

local instance inertConstant_finiteGeneric : Module.Finite F E :=
  ((monic p).map _).finite_adjoinRoot

/-- The actual inert root algebra has a separable residue extension because the
original constant polynomial is separable, regardless of the base residue field. -/
theorem isSeparable_residueField_inert_constant (hsep : (poly p).Separable) :
    Algebra.IsSeparable (ResidueField R) (ResidueField S) := by
  let q := ((poly p).map (algebraMap k R)).map (residue R)
  let : Fact (Irreducible q) := ⟨hred.out⟩
  let : Algebra.IsSeparable (ResidueField R) (AdjoinRoot q) :=
    AdjoinRoot.isSeparable_of_polynomial_separable _ hsep.map.map
  apply (Algebra.IsSeparable.iff_of_equiv_equiv (RingEquiv.refl (ResidueField R))
    (AdjoinRoot.residueFieldEquivAdjoinRoot ((poly p).map (algebraMap k R)) hred.out) ?_).mpr
      inferInstance
  ext a
  obtain ⟨b, rfl⟩ := residue_surjective a
  change AdjoinRoot.of q (residue R b) =
    AdjoinRoot.residueFieldEquivAdjoinRoot ((poly p).map (algebraMap k R)) hred.out
      (residue S (AdjoinRoot.of ((poly p).map (algebraMap k R)) b))
  exact (AdjoinRoot.residueFieldEquivAdjoinRoot_residue_of _ hred.out b).symm

variable [Normal k (AdjoinRoot (poly p))]

/-- The all-symbol norm-residue square on the literal inert constant root DVR.
Its local, finite, fraction-field, and residue-separability data are all proved. -/
theorem dvrMilnorTameSymbol'_milnorKNorm_inert_constant_of_separable
    (hR : IsJapaneseRing R) (hsep : (poly p).Separable) (hp : d.Prime) :
    letI : Fact (Irreducible ((poly p).map (algebraMap k F))) :=
      inertConstant_genericIrreducible k R F p
    ∀ (n : ℕ) (x : MilnorKTheory E (n + 1)),
      dvrMilnorTameSymbol' R F n (milnorKNorm F E (n + 1) x) =
        milnorKNorm (ResidueField R) (ResidueField S) n
          (dvrMilnorTameSymbol' S E n x) := by
  let : Fact (Irreducible ((poly p).map (algebraMap k F))) :=
    inertConstant_genericIrreducible k R F p
  intro n x
  let : Algebra.IsSeparable (ResidueField R) (ResidueField S) :=
    isSeparable_residueField_inert_constant k R p hsep
  exact dvrMilnorTameSymbol'_milnorKNorm_of_japanese_separable_constant_cover
    k R S F p hR hsep hp n x

end Stacks.Chow

end
