/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.FieldTheory.AdjoinRoot.MinpolyDegree
public import Colib.RingTheory.AdjoinRoot.FactorIndexEquiv

/-!
# Literal minimal-polynomial residue branches

Adapted from `Aglib/FieldTheory/ResidueMinpolyBranch.lean` at revision
`4f65be4eafa8964bd1f7a83682e99aa8165bd418`, lines 30–126.
The branch is the existing native sigma of monic irreducible polynomials with
its actual divisibility proof. The lift is evaluation at the original generator
image; its composite with the original quotient map is the entire embedding.
-/

@[expose] public noncomputable section

open Polynomial Stacks.Chow Stacks.Chow.MonicIrreducibleOfDegree

namespace AdjoinRoot

variable {k A M V : Type*} [Field k] [Field A] [Field M] [Field V]
  [Algebra k A] [Algebra k M] [Algebra M V] [Algebra k V]
  [IsScalarTower k M V] [FiniteDimensional M V]

/-- Present the original field by the minimal polynomial of its supplied power basis. -/
def powerBasisMinpolyEquiv (B : PowerBasis k A) :
    AdjoinRoot (minpoly k B.gen) ≃ₐ[k] A :=
  equiv' (minpoly k B.gen) B
    (by rw [aeval_eq, mk_self]) (minpoly.aeval k B.gen)

/-- The original primitive generator is the image of the quotient root. -/
@[simp]
theorem powerBasisMinpolyEquiv_root (B : PowerBasis k A) :
    powerBasisMinpolyEquiv B (root (minpoly k B.gen)) = B.gen := by
  change liftAlgHom (minpoly k B.gen) (Algebra.ofId k A) B.gen
    (minpoly.aeval k B.gen) (root (minpoly k B.gen)) = B.gen
  exact liftAlgHom_root _ _ _ _

/-- The branch selected by an actual residue embedding, in the existing native index. -/
def minpolyScalarBranch (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    {r : Σ d : ℕ, MonicIrreducibleOfDegree M d //
      poly r.2 ∣ (minpoly k B.gen).map (algebraMap k M)} := by
  refine ⟨⟨(minpoly M (φ B.gen)).natDegree,
    ⟨minpoly M (φ B.gen), minpoly.monic (Algebra.IsIntegral.isIntegral _),
      minpoly.irreducible (Algebra.IsIntegral.isIntegral _), rfl⟩⟩, ?_⟩
  apply minpoly.dvd M (φ B.gen)
  rw [Polynomial.aeval_map_algebraMap M, Polynomial.aeval_algHom_apply,
    minpoly.aeval, map_zero]

/-- The chosen polynomial is literally the minimal polynomial of the residue image. -/
@[simp]
theorem minpolyScalarBranch_poly (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    poly (minpolyScalarBranch (M := M) B φ).1.2 = minpoly M (φ B.gen) := rfl

/-- Evaluate the actual branch quotient at the image of the original generator. -/
def minpolyScalarBranchLift (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    AdjoinRoot (poly (minpolyScalarBranch (M := M) B φ).1.2) →ₐ[M] V :=
  liftAlgHom _ (Algebra.ofId M V) (φ B.gen) (minpoly.aeval M (φ B.gen))

/-- The branch root evaluates to the original residue image. -/
theorem minpolyScalarBranchLift_root (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    minpolyScalarBranchLift (M := M) B φ
      (root (poly (minpolyScalarBranch (M := M) B φ).1.2)) = φ B.gen :=
  liftAlgHom_root _ _ _ _

/-- The original primitive presentation is irreducible. -/
instance powerBasisMinpolyFact (B : PowerBasis k A) : Fact (Irreducible (minpoly k B.gen)) :=
  ⟨minpoly.irreducible B.isIntegral_gen⟩

/-- The actual root lift and scalar quotient map recover the original embedding
after primitive presentation, as an equality of whole ring maps. -/
theorem minpolyScalarBranchLift_comp_map
    (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    (minpolyScalarBranchLift (M := M) B φ).toRingHom.comp
      (AdjoinRoot.map (algebraMap k M) (minpoly k B.gen)
        (poly (minpolyScalarBranch (M := M) B φ).1.2)
        (minpolyScalarBranch (M := M) B φ).2) =
      φ.toRingHom.comp (powerBasisMinpolyEquiv B).toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change minpolyScalarBranchLift (M := M) B φ
      (AdjoinRoot.map (algebraMap k M) (minpoly k B.gen)
        (poly (minpolyScalarBranch (M := M) B φ).1.2)
        (minpolyScalarBranch (M := M) B φ).2 (of (minpoly k B.gen) a)) =
      φ (powerBasisMinpolyEquiv B (algebraMap k (AdjoinRoot (minpoly k B.gen)) a))
    rw [AdjoinRoot.map_of]
    change minpolyScalarBranchLift (M := M) B φ
      (algebraMap M _ (algebraMap k M a)) = _
    rw [AlgHom.commutes, AlgEquiv.commutes, φ.commutes,
      ← IsScalarTower.algebraMap_apply k M V]
  · change minpolyScalarBranchLift (M := M) B φ
      (AdjoinRoot.map (algebraMap k M) (minpoly k B.gen)
        (poly (minpolyScalarBranch (M := M) B φ).1.2)
        (minpolyScalarBranch (M := M) B φ).2 (root (minpoly k B.gen))) =
      φ (powerBasisMinpolyEquiv B (root (minpoly k B.gen)))
    rw [AdjoinRoot.map_root, minpolyScalarBranchLift_root, powerBasisMinpolyEquiv_root]

/-- The composite retains the entire original residue embedding on the original field. -/
theorem minpolyScalarBranchLift_comp_presentation_symm
    (B : PowerBasis k A) (φ : A →ₐ[k] V) :
    ((minpolyScalarBranchLift (M := M) B φ).toRingHom.comp
      (AdjoinRoot.map (algebraMap k M) (minpoly k B.gen)
        (poly (minpolyScalarBranch (M := M) B φ).1.2)
        (minpolyScalarBranch (M := M) B φ).2)).comp
      (powerBasisMinpolyEquiv B).symm.toRingHom = φ.toRingHom := by
  rw [minpolyScalarBranchLift_comp_map]
  ext a
  exact congrArg φ ((powerBasisMinpolyEquiv B).apply_symm_apply a)

/-- The relative degree agrees for the existing root action, not a replacement action. -/
theorem minpolyScalarBranch_finrank
    (B : PowerBasis k A) (φ : A →ₐ[k] V)
    [Algebra (AdjoinRoot (poly (minpolyScalarBranch (M := M) B φ).1.2)) V]
    [IsScalarTower M (AdjoinRoot (poly (minpolyScalarBranch (M := M) B φ).1.2)) V]
    (hroot : algebraMap (AdjoinRoot (poly (minpolyScalarBranch (M := M) B φ).1.2)) V
      (root (poly (minpolyScalarBranch (M := M) B φ).1.2)) = φ B.gen) :
    Module.finrank (IntermediateField.adjoin M {φ B.gen}) V =
      Module.finrank (AdjoinRoot (poly (minpolyScalarBranch (M := M) B φ).1.2)) V :=
  finrank_adjoin_eq_of_minpoly_eq (φ B.gen) rfl hroot

end AdjoinRoot

end
