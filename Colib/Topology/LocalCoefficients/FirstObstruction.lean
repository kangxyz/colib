/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.LocalCoefficients.SphericalRelativeCycle
public import Colib.Topology.LocalCoefficients.RelativeFiniteBoundary
public import Colib.Topology.Homotopy.HomotopyGroup.SphericalHomotopyAddition
public import Colib.Topology.Realization.RelativeSphericalStraightening

/-!
# The absolute first homotopy obstruction from integral homology

In degree `m + 2`, genuine vanishing of all lower positive original homotopy
sets and of actual integral homology forces the original homotopy group to be
trivial. The proof retains the finite original chain coefficients and the
stationary spherical input through face-compatible straightening. The genuine
signed spherical-face addition theorem kills the evaluation of every top
simplex boundary. Equality in the original point-relative quotient can then
be evaluated because the selected basepoint-constant simplex has value zero.

Adapted from `Quillen/Topology/LocalCoefficients/FirstObstruction.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd` using the native ordered cubical
quotient directly.

No addition hypothesis or transported-coefficient chain-homotopy certificate
is assumed. Degree one is deliberately excluded: its nonabelian group cannot
be substituted into the finite additive evaluation argument.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity Topology StdSimplex
open scoped Simplicial

universe u

namespace FundamentalGroupoid.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]
variable {m N : ℕ} {z : X} {S F : FiniteSimplexFamily X} {hS : S.FaceClosed}

/-- The actual controlled cubical class of each selected spherical endpoint,
extended by zero off the finite selected set. This definition has no H3 input. -/
private def finiteStickValue
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N)
    (τ : SingularSimplex X ⦋m + 2⦌) : Additive (HomotopyGroup.Pi (m + 2) X z) := by
  classical
  exact if hτ : τ ∈ S (m + 2) then
    Additive.ofMul (P.sphericalEndpoint hn ⟨τ, hτ⟩).homotopyClassStick else 0

private theorem finiteStickValue_selected
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N)
    (τ : SingularSimplex X ⦋m + 2⦌) (hτ : τ ∈ S (m + 2)) :
    finiteStickValue P hn τ =
      Additive.ofMul (P.sphericalEndpoint hn ⟨τ, hτ⟩).homotopyClassStick := by
  classical
  simp [finiteStickValue, hτ]

private theorem finiteStickValue_fixed
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N)
    (f₀ : SphericalSimplex X z (m + 2)) (h₀ : f₀.val ∈ S (m + 2))
    (hF : f₀.val ∈ F (m + 2)) :
    finiteStickValue P hn f₀.val = Additive.ofMul f₀.homotopyClassStick := by
  rw [finiteStickValue_selected P hn f₀.val h₀]
  have h : P.sphericalEndpoint hn ⟨f₀.val, h₀⟩ = f₀ := by
    apply SphericalSimplex.ext
    intro x
    exact P.stationary (m + 2) _ hF x 1
  rw [h]

private theorem finiteStickValue_const
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N)
    (h₀ : ContinuousMap.const _ z ∈ S (m + 2))
    (hF : ContinuousMap.const _ z ∈ F (m + 2)) :
    finiteStickValue P hn (ContinuousMap.const _ z) = 0 := by
  exact (finiteStickValue_fixed P hn SphericalSimplex.const h₀ hF).trans
    (congrArg Additive.ofMul SphericalSimplex.homotopyClassStick_const)

/-- Genuine signed spherical-face addition kills the evaluation of one actual
selected top generator with its original lifted integer coefficient. -/
private theorem topGenerator_evaluation_zero
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 3 < N)
    (τ : {τ // τ ∈ S (m + 3)}) (a : ULift.{u} ℤ) :
    integralChainEvaluation (m + 2) (finiteStickValue P (by omega))
      ((singularChainComplex (constant X integralCoefficients.{u})).d (m + 3) (m + 2)
        (chainInclusion (constant X integralCoefficients.{u}) τ.val a)) = 0 := by
  rw [integralChainEvaluation_boundary]
  have hface (i : Fin (m + 4)) :
      finiteStickValue P (by omega) (restrictSimplex τ.val (SimplexCategory.δ i)) =
        Additive.ofMul (sphericalFace (P.endpoint (m + 3) τ)
          (P.endpoint_skeleton (m + 3) hn τ) i).homotopyClassStick := by
    change finiteStickValue P (by omega) (hS.face τ i).val = _
    rw [finiteStickValue_selected P (by omega) _ (hS.face τ i).property]
    exact congrArg (fun f : SphericalSimplex X z (m + 2) ↦
      Additive.ofMul f.homotopyClassStick) (P.sphericalFace_endpoint hn τ i).symm
  calc
    _ = ∑ i : Fin (m + 4), a.down • ((-1 : ℤ) ^ i.val •
        Additive.ofMul (sphericalFace (P.endpoint (m + 3) τ)
          (P.endpoint_skeleton (m + 3) hn τ) i).homotopyClassStick) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hface i]
      exact smul_comm _ _ _
    _ = a.down • (∑ i : Fin (m + 4), (-1 : ℤ) ^ i.val •
        Additive.ofMul (sphericalFace (P.endpoint (m + 3) τ)
          (P.endpoint_skeleton (m + 3) hn τ) i).homotopyClassStick) :=
      (Finset.smul_sum ..).symm
    _ = 0 := by
      rw [spherical_signed_homotopy_addition (P.endpoint (m + 3) τ)
        (P.endpoint_skeleton (m + 3) hn τ), smul_zero]

private theorem finiteBoundary_evaluation_zero
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 3 < N)
    (b : Finset (SingularSimplex X ⦋m + 3⦌)) (a : ∀ _τ, ULift.{u} ℤ)
    (hb : ∀ τ ∈ b, τ ∈ S (m + 3)) :
    integralChainEvaluation (m + 2) (finiteStickValue P (by omega))
      ((singularChainComplex (constant X integralCoefficients.{u})).d (m + 3) (m + 2)
        (∑ τ ∈ b, chainInclusion (constant X integralCoefficients.{u}) τ (a τ))) = 0 := by
  simp only [map_sum]
  apply Finset.sum_eq_zero
  intro τ hτ
  exact topGenerator_evaluation_zero P hn ⟨τ, hb τ hτ⟩ (a τ)

/-- An arbitrary actual spherical simplex represents the unit in the original
homotopy group when all lower positive homotopy and this homology group vanish. -/
@[colib_ref "quillen" "Quillen/Topology/LocalCoefficients/FirstObstruction.lean:129-181"
  "adaptation" "Actual point-relative cycle and finite boundary evaluation"]
theorem spherical_class_one_of_homology_isZero [PathConnectedSpace X]
    (m : ℕ) (z : X) (f₀ : SphericalSimplex X z (m + 2))
    (hs : ∀ x : X, ∀ k : ℕ, 0 < k → k < m + 2 →
      Subsingleton (HomotopyGroup.Pi k X x))
    (hH : IsZero (homology (constant X integralCoefficients.{u}) (m + 2))) :
    f₀.homotopyClassStick = 1 := by
  let A := constant X integralCoefficients.{u}
  let Q := relativeSingularChainComplex {z} A
  let q := cokernel.π (pushforwardChainMap (subspaceInclusion {z}) A)
  have hr : IsZero (Q.homology (m + 2)) :=
    hH.of_iso (pointRelativeHomologyIso z integralCoefficients.{u} (m + 1)).symm
  have hπ : Q.homologyπ (m + 2) = 0 := hr.eq_of_tgt _ _
  have hc : Q.homologyπ (m + 2) (sphericalRelativeCycle f₀) = 0 := by
    rw [hπ]
    rfl
  obtain ⟨b, a, hb⟩ := relativeCycle_exists_finite_boundary {z} A (m + 2)
    (sphericalRelativeCycle f₀) hc
  obtain ⟨P⟩ := exists_relative_spherical_straightening (m + 2) z f₀ b hs
  let v := finiteStickValue P (by omega)
  let B := ∑ τ ∈ b, chainInclusion A τ (a τ)
  let c := chainInclusion A f₀.val (ULift.up 1)
  have hb' : Q.d (m + 3) (m + 2) (q.f (m + 3) B) = q.f (m + 2) c :=
    hb.trans (iCycles_sphericalRelativeCycle f₀)
  have hcomm : Q.d (m + 3) (m + 2) (q.f (m + 3) B) =
      q.f (m + 2) ((singularChainComplex A).d (m + 3) (m + 2) B) :=
    ConcreteCategory.congr_hom (q.comm (m + 3) (m + 2)) B
  have hq : q.f (m + 2) ((singularChainComplex A).d (m + 3) (m + 2) B) =
      q.f (m + 2) c := hcomm.symm.trans hb'
  have hconstF := mem_sphericalStraighteningFixedFamily_const f₀ (d := m + 2) (by omega)
  have hconstS := sphericalStraighteningFixedFamily_subset f₀ b (m + 2) hconstF
  have hv : v (ContinuousMap.const _ z) = 0 :=
    finiteStickValue_const P (by omega) hconstS hconstF
  have heval := integralChainEvaluation_eq_of_pointRelative_eq z (m + 2) v hv
    ((singularChainComplex A).d (m + 3) (m + 2) B) c hq
  have hleft : integralChainEvaluation (m + 2) v
      ((singularChainComplex A).d (m + 3) (m + 2) B) = 0 :=
    finiteBoundary_evaluation_zero P (by omega) b a
      (fun τ hτ ↦ mem_sphericalStraighteningFamily_support f₀ b hτ)
  have hfF := mem_sphericalStraighteningFixedFamily_input f₀
  have hfS := sphericalStraighteningFixedFamily_subset f₀ b (m + 2) hfF
  have hright : integralChainEvaluation (m + 2) v c =
      Additive.ofMul f₀.homotopyClassStick := by
    change integralChainEvaluation (m + 2) v
      (chainInclusion (constant X integralCoefficients.{u}) f₀.val (ULift.up 1)) = _
    rw [integralChainEvaluation_inclusion]
    change (1 : ℤ) • finiteStickValue P (by omega) f₀.val = _
    rw [one_smul]
    exact finiteStickValue_fixed P (by omega) f₀ hfS hfF
  have hclass : Additive.ofMul f₀.homotopyClassStick =
      (0 : Additive (HomotopyGroup.Pi (m + 2) X z)) :=
    hright.symm.trans (heval.symm.trans hleft)
  exact hclass

/-- The absolute first-obstruction theorem in the original cubical homotopy
group. All hypotheses concern actual path connectedness, lower homotopy, and
integral homology; the signed addition theorem is proved, not assumed. -/
@[colib_ref "quillen" "Quillen/Topology/LocalCoefficients/FirstObstruction.lean:186-195"
  "adaptation" "Actual cubical quotient with its ordered simplex representatives"]
theorem subsingleton_pi_of_homology_isZero [PathConnectedSpace X]
    (m : ℕ) (z : X)
    (hs : ∀ x : X, ∀ k : ℕ, 0 < k → k < m + 2 →
      Subsingleton (HomotopyGroup.Pi k X x))
    (hH : IsZero (homology (constant X integralCoefficients.{u}) (m + 2))) :
    Subsingleton (HomotopyGroup.Pi (m + 2) X z) := by
  have hunit (a : HomotopyGroup.Pi (m + 2) X z) : a = 1 := by
    obtain ⟨f₀, rfl⟩ := SphericalSimplex.homotopyClassStick_surjective a
    exact spherical_class_one_of_homology_isZero m z f₀ hs hH
  exact ⟨fun a b ↦ (hunit a).trans (hunit b).symm⟩

/-- The same absolute first-obstruction theorem starts from mathlib's original
singular homology, using the genuine constant-chain comparison isomorphism. -/
@[colib_ref "quillen" "Quillen/Topology/LocalCoefficients/FirstObstruction.lean:199-207"
  "adaptation" "Mathlib singular homology via original constant-chain comparison"]
theorem subsingleton_pi_of_singularHomology_isZero [PathConnectedSpace X]
    (m : ℕ) (z : X)
    (hs : ∀ x : X, ∀ k : ℕ, 0 < k → k < m + 2 →
      Subsingleton (HomotopyGroup.Pi k X x))
    (hH : IsZero (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} ℤ)
      (m + 2)).obj integralCoefficients.{u}).obj (TopCat.of X))) :
    Subsingleton (HomotopyGroup.Pi (m + 2) X z) :=
  subsingleton_pi_of_homology_isZero m z hs
    (hH.of_iso (constantHomologyIso integralCoefficients.{u} (m + 2)))

/-- The first-obstruction conclusion retains a genuine homotopy fixed on the
entire boundary of any displayed original spherical singular simplex. -/
@[colib_ref "quillen" "Quillen/Topology/LocalCoefficients/FirstObstruction.lean:211-219"
  "adaptation" "Nullhomotopy fixed on the entire original geometric boundary"]
theorem spherical_nullhomotopic_of_homology_isZero [PathConnectedSpace X]
    (m : ℕ) (z : X) (f₀ : SphericalSimplex X z (m + 2))
    (hs : ∀ x : X, ∀ k : ℕ, 0 < k → k < m + 2 →
      Subsingleton (HomotopyGroup.Pi k X x))
    (hH : IsZero (homology (constant X integralCoefficients.{u}) (m + 2))) :
    f₀.val.HomotopicRel (ContinuousMap.const _ z) (StdSimplex.boundary (m + 2)) :=
  f₀.homotopyClassStick_eq_one_iff.mp (spherical_class_one_of_homology_isZero m z f₀ hs hH)

end FundamentalGroupoid.LocalCoefficients
