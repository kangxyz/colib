/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Util.References

public import Colib.KTheory.Quillen.LowDegreeScalarAction.ScalarUnit
public import Colib.KTheory.Quillen.LowDegreeScalarAction.IdentityAutomorphismZero

/-!
# Degree-zero scalar-unit operations with their original chosen-model maps

The genuine degree-zero identity-automorphism operation gives a homomorphism
in both variables. Chosen small models use the actual lifted automorphism and
need no additional linear structure.

Implementation provenance: `Quillen/KTheory/LowDegreeScalarAction/ScalarUnit.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
open Topology CategoryTheory CategoryTheory.Limits CategoryTheory.Linear
universe w u v s
namespace CategoryTheory.ExactCategory.ScalarUnit
section Operations
variable {C : Type (max u v)} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (R : Type w) [Ring R] (E : ExactStructure C)
/-- The original K-zero operation for an actual multiplicative family of unit automorphisms. -/
def kZeroActionOf (a : Rˣ →* Aut (𝟭 C)) : Rˣ →* (E.K 0 →* E.K 1) where
  toFun r := IdentityAutomorphism.kZeroActionHom E (a r).asIso
  map_one' := by
    ext x
    change IdentityAutomorphism.kZeroNatAut E x (a 1) = 1
    simp only [map_one]
  map_mul' r t := by
    ext x
    change IdentityAutomorphism.kZeroNatAut E x (a (r * t)) =
      IdentityAutomorphism.kZeroNatAut E x (a r) * IdentityAutomorphism.kZeroNatAut E x (a t)
    simp only [map_mul]


variable [Linear R C]
/-- The original scalar operation is multiplicative in both original variables. -/
def kZeroAction : Rˣ →* (E.K 0 →* E.K 1) := kZeroActionOf R E (scalarNatAut R C)

/-- The operation retains the canonical scalar automorphism and the original track. -/
@[simp] theorem kZeroAction_apply (r : Rˣ) (a : E.K 0) :
    kZeroAction R E r a = IdentityAutomorphism.kZeroAction E (scalarNatAut R C r).asIso a := rfl

/-- The source group law uses genuine Q-space loop-action triviality. -/
theorem kZeroAction_source_mul (r : Rˣ) (a b : E.K 0) :
    kZeroAction R E r (a * b) = kZeroAction R E r a * kZeroAction R E r b :=
  (kZeroAction R E r).map_mul a b

/-- Multiplication of scalar units preserves the original composition convention. -/
theorem kZeroAction_unit_mul (r t : Rˣ) (a : E.K 0) :
    kZeroAction R E (r * t) a = kZeroAction R E r a * kZeroAction R E t a :=
  DFunLike.congr_fun ((kZeroAction R E).map_mul r t) a

variable {E} {D : Type (max u v)} [Category.{v} D] [Preadditive D]
  [HasFiniteBiproducts D] [Linear R D] {ED : ExactStructure D}

/-- Ordinary linearity gives the square of the unchanged exact-functor K-maps. -/
theorem kZeroAction_natural (F : ExactFunctor E ED) [F.toFunctor.Linear R]
    (r : Rˣ) (a : E.K 0) :
    F.KMap 1 (kZeroAction R E r a) = kZeroAction R ED r (F.KMap 0 a) :=
  IdentityAutomorphism.kZeroAction_natural F (scalarNatAut R C r).asIso
    (scalarNatAut R D r).asIso (scalarNatAut_map R F.toFunctor r) a
end Operations

section SmallModelOperations
variable (R : Type w) [Ring R] {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C] [Linear R C] [EssentiallySmall.{s} C] (E : ExactStructure C)

/-- The actual chosen-model degree-zero operation with its lifted scalar automorphism. -/
def smallModelKZeroAction : Rˣ →* (E.SmallK.{s} 0 →* E.SmallK.{s} 1) :=
  kZeroActionOf R E.smallModel.{s} (smallModelScalarNatAut R C)

/-- The actual small-model comparison keeps the same whole scalar track. -/
@[simp] theorem smallModelKZeroAction_apply (r : Rˣ) (a : E.SmallK.{s} 0) :
    smallModelKZeroAction R E r a =
      IdentityAutomorphism.kZeroAction E.smallModel (smallModelScalarNatAut R C r).asIso a := rfl
end SmallModelOperations
end CategoryTheory.ExactCategory.ScalarUnit

attribute [colib_ref "quillen"
  "Quillen/KTheory/LowDegreeScalarAction/ScalarUnit.lean:83-94,111-204,220-231"
  "adaptation" "Original maps, whole tracks, native model comparisons and signs"]
  CategoryTheory.ExactCategory.ScalarUnit.kZeroActionOf
  CategoryTheory.ExactCategory.ScalarUnit.kZeroAction
  CategoryTheory.ExactCategory.ScalarUnit.kZeroAction_apply
  CategoryTheory.ExactCategory.ScalarUnit.kZeroAction_source_mul
  CategoryTheory.ExactCategory.ScalarUnit.kZeroAction_unit_mul
  CategoryTheory.ExactCategory.ScalarUnit.kZeroAction_natural
  CategoryTheory.ExactCategory.ScalarUnit.smallModelKZeroAction
  CategoryTheory.ExactCategory.ScalarUnit.smallModelKZeroAction_apply
