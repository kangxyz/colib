/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Cancellation.ReparametrizedPowerPrime
public import Colib.AlgebraicGeometry.Correspondences.Cancellation.PowerCutParameter.AmbientPrime
import Colib.AlgebraicGeometry.Correspondences.Exterior.Additive
import Colib.AlgebraicGeometry.Correspondences.Additive.Ext

/-!
# Exact reparametrization of signed finite correspondences

The closed graph acts on the subgroup whose retained cycles are finite
correspondences. This action preserves all signed prime coefficients
and commutes with precomposition by any finite correspondence extended
by the torus identity.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow
open Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

open _root_.AlgebraicGeometry.Scheme SmoothSite

variable (k : Type u) [Field k] (X Y : SmoothSite (Spec (.of k)))

local notation "Sₖ" => Spec (CommRingCat.of k)
local notation "T" => multiplicativeGroupObject Sₖ
local notation "G(" X ")" => product X T
local notation "V(" Y ")" => torusPowerCutRetainedTarget k Y

variable (n : ℕ)
  (u₀ : (Γ((product Y (multiplicativeGroupObject (Spec (.of k)))).left, ⊤))ˣ)

set_option quotPrecheck false in
local notation "g" => (G(X)).hom
set_option quotPrecheck false in
local notation "h" => (G(Y)).hom
set_option quotPrecheck false in
local notation "h'" => (V(Y)).hom
local notation "J" => torusPowerParameterAmbientGraph k (X := X) n u₀

/-- The domain of the actual graph pushforward, using the native subgroup. -/
@[expose]
def torusPowerParameterGraphDomain : AddSubgroup (finiteCorrespondences g h) :=
  (finiteCorrespondences g h').comap
    ((finiteCyclePushforward J).comp (finiteCorrespondences g h).subtype)

local notation "D" => torusPowerParameterGraphDomain k X Y n u₀

/-- The domain condition checks the actual images of the signed support points. -/
theorem mem_torusPowerParameterGraphDomain_iff (a : finiteCorrespondences g h) :
    a ∈ D ↔ ∀ w, a.val w ≠ 0 → IsFiniteCorrespondencePoint g h' (J w) := by
  change finiteCyclePushforward J a.val ∈ finiteCorrespondences g h' ↔ _
  constructor
  · intro ha w hw
    apply ha.2
    rw [finiteCyclePushforward_apply_of_isClosedImmersion]
    exact hw
  · intro ha
    refine ⟨finiteCyclePushforward_finite_support J a.val a.property.1, ?_⟩
    intro y hy
    obtain ⟨w, hw, hwy⟩ := finiteCyclePushforward_support_subset J a.val hy
    exact hwy ▸ ha w hw

/-- The graph pushforward on the actual domain of finite correspondences. -/
@[expose]
def torusPowerParameterGraph : D →+ finiteCorrespondences g h' where
  toFun a := ⟨finiteCyclePushforward J a.val.val, a.property⟩
  map_zero' := by
    apply Subtype.ext
    exact map_zero (finiteCyclePushforward J)
  map_add' a b := by
    apply Subtype.ext
    exact map_add (finiteCyclePushforward J) a.val.val b.val.val

@[simp]
theorem torusPowerParameterGraph_val (a : D) :
    (torusPowerParameterGraph k X Y n u₀ a).val = finiteCyclePushforward J a.val.val :=
  rfl

/-- A signed prime with admissible graph image belongs to the domain. -/
theorem single_mem_torusPowerParameterGraphDomain
    (w : pullback (C := Scheme) g h) (hw : IsFiniteCorrespondencePoint g h w)
    (hw' : IsFiniteCorrespondencePoint g h' (J w)) (m : ℤ) :
    singleFiniteCorrespondence g h w hw m ∈ D := by
  classical
  change finiteCyclePushforward J (single w m) ∈ finiteCorrespondences g h'
  rw [finiteCyclePushforward_single_of_isClosedImmersion]
  exact (singleFiniteCorrespondence g h' (J w) hw' m).property

/-- A signed prime retains its coefficient under the closed graph. -/
theorem torusPowerParameterGraph_single
    (w : pullback (C := Scheme) g h) (hw : IsFiniteCorrespondencePoint g h w)
    (hw' : IsFiniteCorrespondencePoint g h' (J w)) (m : ℤ) :
    torusPowerParameterGraph k X Y n u₀
      ⟨singleFiniteCorrespondence g h w hw m,
        single_mem_torusPowerParameterGraphDomain k X Y n u₀ w hw hw' m⟩ =
      singleFiniteCorrespondence g h' (J w) hw' m := by
  classical
  apply Subtype.ext
  exact finiteCyclePushforward_single_of_isClosedImmersion J w m

include u₀ in
/-- Every finite correspondence lies in the domain for all large power
exponents. The bound is common to its actual signed support. -/
theorem eventually_mem_torusPowerParameterGraphDomain (a : finiteCorrespondences g h) :
    ∃ N : ℕ, ∀ m : ℕ, N ≤ m → a ∈ torusPowerParameterGraphDomain k X Y m u₀ := by
  classical
  let I := a.property.1.toFinset
  have hne (w : I) : a.val w.val ≠ 0 := a.property.1.mem_toFinset.mp w.property
  choose L hL using fun w : I =>
    exists_isFiniteCorrespondencePoint_torusPowerParameterAmbientGraph k X Y w.val
      (a.property.2 w.val (hne w)) u₀
  refine ⟨Finset.univ.sup L, fun m hm =>
    (mem_torusPowerParameterGraphDomain_iff k X Y m u₀ a).mpr ?_⟩
  intro w hw
  let w' : I := ⟨w, a.property.1.mem_toFinset.mpr hw⟩
  exact hL w' m ((Finset.le_sup (Finset.mem_univ w')).trans hm)

variable (U : SmoothSite (Spec (.of k)))

set_option quotPrecheck false in
local notation "f" => (G(U)).hom
local notation "J'" => torusPowerParameterAmbientGraph k (X := U) n u₀

/-- The exact finite graph pushforward commutes with native composition
by the exterior of any finite correspondence and the torus identity. -/
theorem torusPowerParameterGraph_comp_val
    (W : finiteCorrespondences U.hom X.hom) (a : D) :
    finiteCyclePushforward J'
      (incidenceTorPairing f g h (nativeExterior U X T W) a.val).val =
      (incidenceTorPairing f g h' (nativeExterior U X T W)
        (torusPowerParameterGraph k X Y n u₀ a)).val := by
  classical
  let L : finiteCorrespondences U.hom X.hom →+ AlgebraicCycle (pullback (C := Scheme) f h') ℤ :=
    (finiteCyclePushforward J').comp ((finiteCorrespondences f h).subtype.comp
      (((incidenceTorPairing f g h).flip a.val).comp (nativeExterior U X T)))
  let R : finiteCorrespondences U.hom X.hom →+ AlgebraicCycle (pullback (C := Scheme) f h') ℤ :=
    (finiteCorrespondences f h').subtype.comp
      (((incidenceTorPairing f g h').flip (torusPowerParameterGraph k X Y n u₀ a)).comp
        (nativeExterior U X T))
  change L W = R W
  have he : L = R := by
    apply finiteCorrespondences.addHom_ext U.hom X.hom
    intro z hz m
    let b := nativeExterior U X T (singleFiniteCorrespondence U.hom X.hom z hz m)
    let L' : D →+ AlgebraicCycle (pullback (C := Scheme) f h') ℤ :=
      (finiteCyclePushforward J').comp ((finiteCorrespondences f h).subtype.comp
        ((incidenceTorPairing f g h b).comp (D).subtype))
    let R' : D →+ AlgebraicCycle (pullback (C := Scheme) f h') ℤ :=
      (finiteCorrespondences f h').subtype.comp
        ((incidenceTorPairing f g h' b).comp (torusPowerParameterGraph k X Y n u₀))
    change L' a = R' a
    let S := a.val.property.1.toFinset
    let hne (w : S) : a.val.val w.val ≠ 0 := by
      simpa only [S, Set.Finite.mem_toFinset, support, Function.mem_support] using w.property
    let hw (w : S) := a.val.property.2 w.val (hne w)
    let hw' (w : S) := (mem_torusPowerParameterGraphDomain_iff k X Y n u₀ a.val).mp
      a.property w.val (hne w)
    let d (w : S) : D :=
      ⟨singleFiniteCorrespondence g h w.val (hw w) (a.val.val w.val),
        single_mem_torusPowerParameterGraphDomain k X Y n u₀ w.val (hw w) (hw' w) _⟩
    have ha : a = ∑ w : S, d w := by
      apply Subtype.ext
      change a.val = (D).subtype (∑ w : S, d w)
      rw [map_sum]
      exact finiteCorrespondence_eq_sum_signedSingles g h a.val
    rw [ha, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro w _
    change finiteCyclePushforward J'
        (incidenceTorPairing f g h b
          (singleFiniteCorrespondence g h w.val (hw w) (a.val.val w.val))).val =
      (incidenceTorPairing f g h' b (torusPowerParameterGraph k X Y n u₀ (d w))).val
    rw [show torusPowerParameterGraph k X Y n u₀ (d w) =
        singleFiniteCorrespondence g h' (J w.val) (hw' w) (a.val.val w.val) from
      torusPowerParameterGraph_single k X Y n u₀ w.val (hw w) (hw' w) _]
    simp only [b, nativeExterior_single, nativeExteriorPrime_eq_single,
      ← singleFiniteCorrespondence_eq_zsmul, incidenceTorPairing_single]
    change finiteCyclePushforward J' ((m * a.val.val w.val) • _ : AlgebraicCycle _ ℤ) =
      (m * a.val.val w.val) • _
    rw [map_zsmul, torusPowerParameter_primeComposition_val U X Y z hz w.val
      (hw w) n u₀ (hw' w)]
  exact DFunLike.congr_fun he W

/-- Composition with any exterior transfer preserves the domain and gives
the actual reparametrized composition. -/
theorem torusPowerParameterGraph_comp
    (W : finiteCorrespondences U.hom X.hom) (a : D) :
    ∃ hmem : incidenceTorPairing f g h (nativeExterior U X T W) a.val ∈
        torusPowerParameterGraphDomain k U Y n u₀,
      torusPowerParameterGraph k U Y n u₀
        ⟨incidenceTorPairing f g h (nativeExterior U X T W) a.val, hmem⟩ =
        incidenceTorPairing f g h' (nativeExterior U X T W)
          (torusPowerParameterGraph k X Y n u₀ a) := by
  let b := incidenceTorPairing f g h' (nativeExterior U X T W)
    (torusPowerParameterGraph k X Y n u₀ a)
  have hv := torusPowerParameterGraph_comp_val k X Y n u₀ U W a
  have hm : incidenceTorPairing f g h (nativeExterior U X T W) a.val ∈
      torusPowerParameterGraphDomain k U Y n u₀ := by
    change finiteCyclePushforward J'
      (incidenceTorPairing f g h (nativeExterior U X T W) a.val).val ∈ finiteCorrespondences f h'
    rw [hv]
    exact b.property
  exact ⟨hm, Subtype.ext hv⟩

end AlgebraicGeometry.Cor
