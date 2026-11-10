/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.LocalCoefficients.PointRelativeEvaluation
public import Colib.Topology.Homotopy.HomotopyGroup.SphericalFaces
public import Colib.Analysis.Convex.StdSimplex.FaceCharts

/-!
# A genuine spherical simplex gives a point-relative integral cycle

The generator is not declared an absolute cycle in unnormalized singular
chains. Instead every boundary face is a basepoint-constant simplex and dies
under the original point-relative quotient. The original coefficient is the
lifted integer one.
-/

@[expose] public section
noncomputable section

open CategoryTheory Limits Convexity Topology
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {z : X}

/-- The original point-relative quotient kills every basepoint-constant generator. -/
@[reassoc]
theorem chainInclusion_const_pointRelativeQuotient (z : X) (n : ℕ) :
    chainInclusion (constant X integralCoefficients.{u}) (ContinuousMap.const _ z) ≫
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
        (constant X integralCoefficients.{u}))).f n = 0 := by
  let I := pushforwardChainMap (subspaceInclusion {z}) (constant X integralCoefficients.{u})
  let q := cokernel.π I
  let τ : SingularSimplex ({z} : Set X) ⦋n⦌ := ContinuousMap.const _ ⟨z, rfl⟩
  have hiq : I.f n ≫ q.f n = 0 := by
    exact congrArg (fun f ↦ f.f n) (cokernel.condition I)
  have hι : chainInclusion (constant X integralCoefficients.{u})
      (ContinuousMap.const _ z) =
      chainInclusion (constant ({z} : Set X) integralCoefficients.{u}) τ ≫ I.f n := by
    exact (chainInclusion_pushforwardModuleMap (subspaceInclusion {z})
      (constant X integralCoefficients.{u}) τ).symm
  exact (congrArg (fun k ↦ k ≫ q.f n) hι).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun k ↦ chainInclusion (constant ({z} : Set X)
        integralCoefficients.{u}) τ ≫ k) hiq).trans (comp_zero)))

/-- Every positive-dimensional spherical simplex has constant standard faces. -/
theorem spherical_restrictSimplex_eq_const {n : ℕ}
    (f₀ : SphericalSimplex X z (n + 1)) (i : Fin (n + 2)) :
    restrictSimplex f₀.val (SimplexCategory.δ i) = ContinuousMap.const _ z := by
  ext x
  change f₀ (x.map i.succAbove) = z
  exact f₀.boundary _ ⟨i, StdSimplex.map_succAbove_self i x⟩

/-- The actual spherical generator is killed by the relative differential. -/
theorem spherical_pointRelative_d_zero {n : ℕ}
    (f₀ : SphericalSimplex X z (n + 1)) :
    chainInclusion (constant X integralCoefficients.{u}) f₀.val ≫
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
        (constant X integralCoefficients.{u}))).f (n + 1) ≫
      (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).d
        (n + 1) n = 0 := by
  let q := cokernel.π (pushforwardChainMap (subspaceInclusion {z})
    (constant X integralCoefficients.{u}))
  let σ : SingularSimplex X ⦋n + 1⦌ := f₀.val
  let ι : integralCoefficients.{u} ⟶
      (singularChainComplex (constant X integralCoefficients.{u})).X (n + 1) :=
    chainInclusion (constant X integralCoefficients.{u}) σ
  have hq := q.comm (n + 1) n
  change ι ≫ q.f (n + 1) ≫ _ = 0
  refine (congrArg (fun k ↦ ι ≫ k) hq).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k ↦ k ≫ q.f n)
    (chainInclusion_d (constant X integralCoefficients.{u}) σ)).trans ?_
  simp only [integralRestrictionTransport]
  refine (Preadditive.sum_comp Finset.univ _ (q.f n)).trans ?_
  apply Finset.sum_eq_zero
  intro i _
  have hfacezero : chainInclusion (constant X integralCoefficients.{u})
      (restrictSimplex σ (SimplexCategory.δ i)) ≫ q.f n = 0 :=
    (congrArg (fun ρ : SingularSimplex X ⦋n⦌ ↦
      chainInclusion (constant X integralCoefficients.{u}) ρ ≫ q.f n)
        (spherical_restrictSimplex_eq_const f₀ i)).trans
      (chainInclusion_const_pointRelativeQuotient z n)
  have hid : 𝟙 integralCoefficients.{u} ≫
      chainInclusion (constant X integralCoefficients.{u})
        (restrictSimplex σ (SimplexCategory.δ i)) ≫ q.f n = 0 :=
    (Category.id_comp _).trans hfacezero
  have hz : (-1 : ℤ) ^ i.val •
      (0 : integralCoefficients.{u} ⟶
        (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).X n) = 0 := by
    ext v
    change (-1 : ℤ) ^ i.val •
      (0 : (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).X n) = 0
    exact zsmul_zero _
  exact (Preadditive.zsmul_comp _ _ _).trans
    ((congrArg (fun f : integralCoefficients.{u} ⟶
      (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).X n ↦
        (-1 : ℤ) ^ i.val • f)
      ((Category.assoc _ _ _).trans hid)).trans hz)

/-- The original relative-chain representative, with coefficient exactly one. -/
def sphericalRelativeChain {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).X (n + 1) :=
  (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
    (constant X integralCoefficients.{u}))).f (n + 1)
      (chainInclusion (constant X integralCoefficients.{u}) f₀.val (ULift.up 1))

/-- The actual relative chain is a cycle, including when its absolute boundary is nonzero. -/
theorem sphericalRelativeChain_cycle {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).d
      (n + 1) n (sphericalRelativeChain f₀) = 0 :=
  ConcreteCategory.congr_hom (spherical_pointRelative_d_zero f₀) (ULift.up 1)

/-- The cycle equation in the exact short-complex indexing used by the cycle object. -/
theorem sphericalRelativeChain_sc_cycle {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    ((forget₂ (ModuleCat.{u} ℤ) Ab).map
      ((relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).sc
        (n + 1)).g) (sphericalRelativeChain f₀) = 0 := by
  change (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).d
    (n + 1) ((ComplexShape.down ℕ).next (n + 1)) (sphericalRelativeChain f₀) = 0
  rw [ChainComplex.next_nat_succ]
  exact sphericalRelativeChain_cycle f₀

/-- The spherical representative as an element of the genuine relative cycle object. -/
def sphericalRelativeCycle {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).cycles (n + 1) :=
  ((relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).sc
    (n + 1)).cyclesMk (sphericalRelativeChain f₀) (sphericalRelativeChain_sc_cycle f₀)

/-- Taking the underlying chain returns exactly the original quotient generator. -/
theorem iCycles_sphericalRelativeCycle {n : ℕ} (f₀ : SphericalSimplex X z (n + 1)) :
    (relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).iCycles
      (n + 1) (sphericalRelativeCycle f₀) = sphericalRelativeChain f₀ :=
  ((relativeSingularChainComplex {z} (constant X integralCoefficients.{u})).sc
    (n + 1)).i_cyclesMk (sphericalRelativeChain f₀) (sphericalRelativeChain_sc_cycle f₀)

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/SphericalRelativeCycle.lean:38-54"
  "adaptation" "Actual point quotient and original finite singular chains"]
  chainInclusion_const_pointRelativeQuotient

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/SphericalRelativeCycle.lean:55-62"
  "adaptation" "Actual point quotient and original finite singular chains"]
  spherical_restrictSimplex_eq_const

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/SphericalRelativeCycle.lean:63-95"
  "adaptation" "Actual point quotient and original finite singular chains"]
  spherical_pointRelative_d_zero

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/SphericalRelativeCycle.lean:96-102"
  "adaptation" "Actual point quotient and original finite singular chains"]
  sphericalRelativeChain

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/SphericalRelativeCycle.lean:103-108"
  "adaptation" "Actual point quotient and original finite singular chains"]
  sphericalRelativeChain_cycle

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/SphericalRelativeCycle.lean:109-118"
  "adaptation" "Actual point quotient and original finite singular chains"]
  sphericalRelativeChain_sc_cycle

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/SphericalRelativeCycle.lean:119-124"
  "adaptation" "Actual point quotient and original finite singular chains"]
  sphericalRelativeCycle

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/SphericalRelativeCycle.lean:125-130"
  "adaptation" "Actual point quotient and original finite singular chains"]
  iCycles_sphericalRelativeCycle

attribute [colib_tag "COL-0526"]
  sphericalRelativeCycle

end FundamentalGroupoid.LocalCoefficients
