/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.LocalCoefficients.DoubleCylinderHomology
public import Colib.Topology.HomotopyCofiber.ReducedMappingConeFiberReduction

/-! # Positive homology vanishing for the literal unreduced cone of an original chain
quasi-isomorphism -/
@[expose] public section

open TopCat.DoubleCylinder
open FundamentalGroupoid.LocalCoefficients

noncomputable section
open CategoryTheory Limits
open scoped Topology unitInterval
universe u
namespace Topology.ReducedMappingCone
open FundamentalGroupoid.LocalCoefficients TopCat.DoubleCylinder
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (V : ModuleCat.{u} ℤ)

/-- Every positive homology group of the original cone vanishes when the original map
is a constant-chain quasi-isomorphism. The proof uses its actual two collar opens. -/
theorem unreducedCone_positive_homology_isZero_of_quasiIso
    (hf : QuasiIso (pushforwardChainMap f (constant Y V))) (n : ℕ) :
    IsZero (homology (constant (UnreducedSpace f) V) (n + 1)) := by
  have hP : IsZero (homology (constant PUnit.{u + 1} V) (n + 1)) :=
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{u} ℤ) (n + 1) V (TopCat.of PUnit.{u + 1}) (Nat.succ_ne_zero n)).of_iso
        (constantHomologyIso V (n + 1))
  exact doubleCylinder_homology_isZero_of_quasiIso (TopCat.ofHom f)
    (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))
    (unreducedSquare f) 0 1 (bandMidpoint 0 1 zero_lt_one) V hf (n + 1) hP

/-- The conclusion uses mathlib's genuine ordinary singular homology through the original
constant-chain comparison. -/
theorem unreducedCone_positive_singularHomology_isZero_of_quasiIso
    (hf : QuasiIso (pushforwardChainMap f (constant Y V))) (n : ℕ) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ)
      (n + 1)).obj V).obj (UnreducedSpace f)) :=
  (unreducedCone_positive_homology_isZero_of_quasiIso f V hf n).of_iso
    (constantHomologyIso V (n + 1)).symm

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyCofiber/UnreducedConeHomology.lean:32-41"
  "adaptation" "Original attaching map and actual collar-relative chain complexes"]
  unreducedCone_positive_homology_isZero_of_quasiIso

attribute [colib_ref "quillen"
  "Quillen/Topology/HomotopyCofiber/UnreducedConeHomology.lean:45-50"
  "adaptation" "Original attaching map and actual collar-relative chain complexes"]
  unreducedCone_positive_singularHomology_isZero_of_quasiIso

attribute [colib_tag "COL-0524"]
  unreducedCone_positive_homology_isZero_of_quasiIso

end Topology.ReducedMappingCone
