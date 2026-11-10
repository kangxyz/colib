/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.Topology.LocalCoefficients.ConstantChainMaps
public import Colib.Topology.LocalCoefficients.SmallChainExcision

/-! # Positive homology of the genuine point-relative constant-coefficient complex -/
@[expose] public section
noncomputable section
open CategoryTheory Limits
universe u
namespace FundamentalGroupoid.LocalCoefficients
variable {X : Type u} [TopologicalSpace X] (x : X) (V : ModuleCat.{u} ℤ)

/-- The short exact sequence of actual singular complexes for the singleton subspace. -/
def pointRelativeSequence : ShortComplex (ChainComplex (ModuleCat.{u} ℤ) ℕ) :=
  ShortComplex.mk (pushforwardChainMap (subspaceInclusion {x}) (constant X V))
    (cokernel.π _) (cokernel.condition _)

/-- The singleton is an actual subspace, so its singular inclusion is monic. -/
theorem pointRelativeSequence_shortExact : (pointRelativeSequence x V).ShortExact := by
  unfold pointRelativeSequence
  exact { exact := ShortComplex.exact_cokernel _ }

/-- The point inclusion is monic on all constant-coefficient homology, including degree zero. -/
theorem pointInclusion_homology_mono (n : ℕ) :
    Mono (pushforwardHomologyMap (subspaceInclusion {x}) (constant X V) n) := by
  let r : C(X, ({x} : Set X)) := ContinuousMap.const X ⟨x, rfl⟩
  have hr : r.comp (subspaceInclusion {x}) = ContinuousMap.id ({x} : Set X) := by
    apply ContinuousMap.ext
    intro z
    exact Subsingleton.elim _ _
  have hcomp : pushforwardHomologyMap (subspaceInclusion {x}) (constant X V) n ≫
      pushforwardHomologyMap r (constant ({x} : Set X) V) n = 𝟙 _ := by
    rw [← constant_pushforwardHomologyMap_comp, hr, constant_pushforwardHomologyMap_id]
    rfl
  apply (ModuleCat.mono_iff_injective _).mpr
  intro a b hab
  have ha := ConcreteCategory.congr_hom hcomp a
  have hb := ConcreteCategory.congr_hom hcomp b
  change pushforwardHomologyMap r (constant ({x} : Set X) V) n
    (pushforwardHomologyMap (subspaceInclusion {x}) (constant X V) n a) = a at ha
  change pushforwardHomologyMap r (constant ({x} : Set X) V) n
    (pushforwardHomologyMap (subspaceInclusion {x}) (constant X V) n b) = b at hb
  exact ha.symm.trans ((congrArg
    (pushforwardHomologyMap r (constant ({x} : Set X) V) n) hab).trans hb)

/-- This is the actual positive-degree point calculation, via the genuine constant-chain
comparison. -/
theorem point_constant_homology_isZero (n : ℕ) :
    IsZero (homology (pullback (subspaceInclusion {x}) (constant X V)) (n + 1)) := by
  change IsZero (homology (constant ({x} : Set X) V) (n + 1))
  exact (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
    (ModuleCat.{u} ℤ) (n + 1) V (TopCat.of ({x} : Set X)) (Nat.succ_ne_zero n)).of_iso
      (constantHomologyIso V (n + 1))

/-- The actual quotient induces an isomorphism in every positive degree.
Degree one uses the split point inclusion on H₀ rather than pretending H₀(point) vanishes. -/
theorem pointRelativeQuotient_homology_isIso (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (pointRelativeSequence x V).g (n + 1)) := by
  let hS := pointRelativeSequence_shortExact x V
  have : Mono (HomologicalComplex.homologyMap (pointRelativeSequence x V).g (n + 1)) :=
    (hS.homology_exact₂ (n + 1)).mono_g ((point_constant_homology_isZero x V n).eq_of_src _ _)
  have hi : Mono (HomologicalComplex.homologyMap (pointRelativeSequence x V).f n) :=
    pointInclusion_homology_mono x V n
  have hδ : hS.δ (n + 1) n rfl = 0 := by
    apply (cancel_mono (HomologicalComplex.homologyMap (pointRelativeSequence x V).f n)).mp
    rw [zero_comp]
    exact hS.δ_comp (n + 1) n rfl
  have : Epi (HomologicalComplex.homologyMap (pointRelativeSequence x V).g (n + 1)) :=
    (hS.homology_exact₃ (n + 1) n rfl).epi_f hδ
  exact isIso_of_mono_of_epi _

/-- Absolute positive constant homology is the genuine homology relative to the given point. -/
def pointRelativeHomologyIso (n : ℕ) :
    homology (constant X V) (n + 1) ≅
      (relativeSingularChainComplex {x} (constant X V)).homology (n + 1) := by
  exact @asIso _ _ _ _
    (HomologicalComplex.homologyMap (pointRelativeSequence x V).g (n + 1))
    (pointRelativeQuotient_homology_isIso x V n)

/-- The forward isomorphism is precisely the original quotient homology map. -/
@[simp]
theorem pointRelativeHomologyIso_hom (n : ℕ) :
    (pointRelativeHomologyIso x V n).hom =
      HomologicalComplex.homologyMap
        (cokernel.π (pushforwardChainMap (subspaceInclusion {x}) (constant X V))) (n + 1) := rfl

/-- The same comparison starts at mathlib's original singular homology, retaining the
constant-chain isomorphism. -/
def singularPointRelativeHomologyIso (n : ℕ) :
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ) (n + 1)).obj V).obj
      (TopCat.of X) ≅
        (relativeSingularChainComplex {x} (constant X V)).homology (n + 1) :=
  (constantHomologyIso V (n + 1)).symm ≪≫ pointRelativeHomologyIso x V n

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/PointRelativeHomology.lean:23-27"
  "adaptation" "Actual point quotient and original finite singular chains"]
  pointRelativeSequence

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/PointRelativeHomology.lean:28-32"
  "adaptation" "Actual point quotient and original finite singular chains"]
  pointRelativeSequence_shortExact

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/PointRelativeHomology.lean:33-53"
  "adaptation" "Actual point quotient and original finite singular chains"]
  pointInclusion_homology_mono

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/PointRelativeHomology.lean:54-62"
  "adaptation" "Actual point quotient and original finite singular chains"]
  point_constant_homology_isZero

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/PointRelativeHomology.lean:63-77"
  "adaptation" "Actual point quotient and original finite singular chains"]
  pointRelativeQuotient_homology_isIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/PointRelativeHomology.lean:78-85"
  "adaptation" "Actual point quotient and original finite singular chains"]
  pointRelativeHomologyIso

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/PointRelativeHomology.lean:86-92"
  "adaptation" "Actual point quotient and original finite singular chains"]
  pointRelativeHomologyIso_hom

attribute [colib_ref "quillen"
  "Quillen/Topology/LocalCoefficients/PointRelativeHomology.lean:93-98"
  "adaptation" "Actual point quotient and original finite singular chains"]
  singularPointRelativeHomologyIso

attribute [colib_tag "COL-0526"]
  pointRelativeHomologyIso

end FundamentalGroupoid.LocalCoefficients
