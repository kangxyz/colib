/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.GenericTorLength
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Order.Interval.Finset.Nat
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.RingTheory.RegularLocalRing.GlobalDimension
public import StacksFrontier.RingTheory.Tor.ProjectiveDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.Data.ENat.WithBotNatCast

/-!
# Genuine finite alternating Tor coefficients on the incidence

For smooth factors over an arbitrary field, with separated middle structure map,
the actual four-factor ambient is smooth and all its local rings are regular.
Native regular-local-ring Tor vanishing bounds all degrees by the dimension of
the particular ambient local ring. Combined with `GenericTorLength`, this gives
a genuine finite alternating integer coefficient at each actual generic point.

The definition uses native `finsum`, native `Module.length`, and native categorical
`Tor`. Finiteness of each length and of the support in degree are proved, not
assumed. The coefficient is independent of a chosen cutoff, and the full finite
formula includes all degrees from zero through the ambient local dimension.
Neither integral supports nor their product is required to be flat or reduced.
Disconnected and empty factors require no exceptions. Quasi-compactness and
separatedness of the outer factors are unnecessary, so the native `SmoothSite`
objects are in particular covered.

Original implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/Tor.lean`.
This source is a new native stalk/regular-ambient specialization, not the original
general-base regular-diagonal proof. Native `Stacks.Intersection.torEulerCharacteristic`
was inspected: it is rational-valued and uses a topological `tsum`; it is not an
integer supplier. No second Tor, local-ring, or cycle model is introduced here.

Native mathematical inputs: Stacks 056S (smooth schemes over any field are regular),
02IT (regular local rings of a regular scheme), 00OC (regular local global
dimension), and native Tor vanishing above projective dimension. The finite-length inputs are
recorded in `GenericTorLength`.
Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped BigOperators

universe u

namespace Stacks.Chow

variable (k : Type u) [Field k] {X Y Z : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The literal four-factor ambient structure morphism, with its rightmost base map. -/
abbrev correspondenceIntersectionAmbientToField :
    correspondenceIntersectionAmbient f g h ⟶ Spec (.of k) :=
  pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ≫ pullback.fst g h ≫ g

instance smooth_correspondenceIntersectionAmbientToField
    [Smooth f] [Smooth g] [Smooth h] :
    Smooth (correspondenceIntersectionAmbientToField k f g h) := by
  dsimp only [correspondenceIntersectionAmbientToField]
  infer_instance

/-- Actual ambient stalks are regular over an arbitrary field, with no perfection hypothesis. -/
theorem isRegularLocalRing_correspondenceIntersectionAmbient_stalk
    [Smooth f] [Smooth g] [Smooth h] (p : correspondenceIntersectionAmbient f g h) :
    IsRegularLocalRing ((correspondenceIntersectionAmbient f g h).presheaf.stalk p) := by
  have hcriterion : IsRegular (correspondenceIntersectionAmbient f g h) ↔
      IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) ∧
        ∀ x : correspondenceIntersectionAmbient f g h,
          IsRegularLocalRing ((correspondenceIntersectionAmbient f g h).presheaf.stalk x) :=
    (isRegular_tfae (correspondenceIntersectionAmbient f g h)).out 1 2
  exact (hcriterion.mp
    (isRegular_of_smooth_over_field (correspondenceIntersectionAmbientToField k f g h))).2 p

/-- The natural-number dimension bound of the actual ambient local ring. -/
def correspondenceIncidenceTorDegreeBound (t : correspondenceIncidence f g h z w) : ℕ :=
  ((ringKrullDim ((correspondenceIntersectionAmbient f g h).presheaf.stalk
    (correspondenceIncidenceAmbientInclusion f g h z w t))).unbotD 0).toNat

/-- The bound is exactly the dimension of the actual ambient local ring. -/
theorem ringKrullDim_eq_correspondenceIncidenceTorDegreeBound
    [Smooth f] [Smooth g] [Smooth h] (t : correspondenceIncidence f g h z w) :
    ringKrullDim ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t)) =
      (correspondenceIncidenceTorDegreeBound k f g h z w t : WithBot ℕ∞) := by
  have := isRegularLocalRing_correspondenceIntersectionAmbient_stalk k f g h
    (correspondenceIncidenceAmbientInclusion f g h z w t)
  exact eq_natCast_unbotD_toNat ringKrullDim_ne_bot ringKrullDim_ne_top

/-- Actual categorical Tor vanishes above the ambient local dimension, at every incidence point. -/
theorem isZero_correspondenceIncidenceTor_of_lt [Smooth f] [Smooth g] [Smooth h]
    (t : correspondenceIncidence f g h z w) (n : ℕ)
    (hn : correspondenceIncidenceTorDegreeBound k f g h z w t < n) :
    IsZero (correspondenceIncidenceTor f g h z w t n) := by
  have := isRegularLocalRing_correspondenceIntersectionAmbient_stalk k f g h
    (correspondenceIncidenceAmbientInclusion f g h z w t)
  let A := (correspondenceIntersectionAmbient f g h).presheaf.stalk
    (correspondenceIncidenceAmbientInclusion f g h z w t)
  let M := correspondenceIncidenceSupportStalkModule f g h z w t
  have hcriterion : IsRegularLocalRing A ↔
      (⨆ K : ModuleCat.{u} A, projectiveDimension K) = ringKrullDim A :=
    (isRegularLocalRing_tfae (R := A)).out 3 4
  have hglobal : (⨆ K : ModuleCat.{u} A, projectiveDimension K) = ringKrullDim A :=
    hcriterion.mp (inferInstance : IsRegularLocalRing A)
  have hpd : HasProjectiveDimensionLE M
      (correspondenceIncidenceTorDegreeBound k f g h z w t) := by
    rw [← projectiveDimension_le_iff]
    calc
      projectiveDimension M ≤ ⨆ K : ModuleCat.{u} A, projectiveDimension K :=
        le_iSup (fun K : ModuleCat.{u} A ↦ projectiveDimension K) M
      _ = ringKrullDim A := hglobal
      _ = (correspondenceIncidenceTorDegreeBound k f g h z w t : WithBot ℕ∞) :=
        ringKrullDim_eq_correspondenceIncidenceTorDegreeBound k f g h z w t
  exact StacksDraft.ProjectiveDimension.isZero_Tor_of_hasProjectiveDimensionLE M
    (correspondenceIncidenceTripleStalkModule f g h z w t) _ n hpd hn

/-- The actual ambient Tor lengths vanish above that same local bound. -/
theorem length_correspondenceIncidenceTor_eq_zero_of_lt [Smooth f] [Smooth g] [Smooth h]
    (t : correspondenceIncidence f g h z w) (n : ℕ)
    (hn : correspondenceIncidenceTorDegreeBound k f g h z w t < n) :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t))
      (correspondenceIncidenceTor f g h z w t n) = 0 :=
  Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp
    (isZero_correspondenceIncidenceTor_of_lt k f g h z w t n hn))

/-- Nonzero actual Tor lengths occur in only finitely many homological degrees. -/
theorem finite_support_length_correspondenceIncidenceTor [Smooth f] [Smooth g] [Smooth h]
    (t : correspondenceIncidence f g h z w) :
    (Function.support fun n : ℕ ↦
      Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t))
        (correspondenceIncidenceTor f g h z w t n)).Finite := by
  refine (Set.finite_Iic (correspondenceIncidenceTorDegreeBound k f g h z w t)).subset ?_
  intro n hn
  exact le_of_not_gt fun hlt ↦
    hn (length_correspondenceIncidenceTor_eq_zero_of_lt k f g h z w t n hlt)

/-- The signed actual Tor length in one degree at a genuine generic incidence point. -/
def correspondenceIncidenceTorTerm
    [Smooth f] [Smooth g] [IsSeparated g] [Smooth h]
    (t : genericPoints (correspondenceIncidence f g h z w)) (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n *
    ((Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t.val))
      (correspondenceIncidenceTor f g h z w t.val n)).toNat : ℤ)

/-- No signed coefficient occurs above the actual local dimension. -/
theorem correspondenceIncidenceTorTerm_eq_zero_of_lt
    [Smooth f] [Smooth g] [IsSeparated g] [Smooth h]
    (t : genericPoints (correspondenceIncidence f g h z w)) (n : ℕ)
    (hn : correspondenceIncidenceTorDegreeBound k f g h z w t.val < n) :
    correspondenceIncidenceTorTerm k f g h z w t n = 0 := by
  unfold correspondenceIncidenceTorTerm
  rw [length_correspondenceIncidenceTor_eq_zero_of_lt k f g h z w t.val n hn]
  simp only [ENat.toNat_zero, Nat.cast_zero, mul_zero]

/-- The signed integer coefficients have genuinely finite degree support. -/
theorem finite_support_correspondenceIncidenceTorTerm
    [Smooth f] [Smooth g] [IsSeparated g] [Smooth h]
    (t : genericPoints (correspondenceIncidence f g h z w)) :
    (Function.support (correspondenceIncidenceTorTerm k f g h z w t)).Finite := by
  refine (Set.finite_Iic (correspondenceIncidenceTorDegreeBound k f g h z w t.val)).subset ?_
  intro n hn
  exact le_of_not_gt fun hlt ↦
    hn (correspondenceIncidenceTorTerm_eq_zero_of_lt k f g h z w t n hlt)

/-- The genuine finite alternating integer Tor coefficient at an actual generic incidence point.
Every length is finite by `correspondenceIncidenceTor_length_ne_top`; the degree
support is finite by `finite_support_correspondenceIncidenceTorTerm`. -/
@[stacks 0AZT "finite alternating integer multiplicity of the full support-product and \
triple-product local rings at a generic point of their actual intersection; this specializes \
the Tor formula using 056S and the generic-support finite-length criterion"]
def correspondenceIncidenceTorCoefficient
    [Smooth f] [Smooth g] [IsSeparated g] [Smooth h]
    (t : genericPoints (correspondenceIncidence f g h z w)) : ℤ :=
  ∑ᶠ n : ℕ, correspondenceIncidenceTorTerm k f g h z w t n

/-- Any cutoff at least the actual local dimension computes the same coefficient. -/
theorem correspondenceIncidenceTorCoefficient_eq_sum_range
    [Smooth f] [Smooth g] [IsSeparated g] [Smooth h]
    (t : genericPoints (correspondenceIncidence f g h z w)) (d : ℕ)
    (hd : correspondenceIncidenceTorDegreeBound k f g h z w t.val ≤ d) :
    correspondenceIncidenceTorCoefficient k f g h z w t =
      ∑ n ∈ Finset.range (d + 1), correspondenceIncidenceTorTerm k f g h z w t n := by
  unfold correspondenceIncidenceTorCoefficient
  apply finsum_eq_sum_of_support_subset
  intro n hn
  have hle : n ≤ correspondenceIncidenceTorDegreeBound k f g h z w t.val :=
    le_of_not_gt fun hlt ↦
      hn (correspondenceIncidenceTorTerm_eq_zero_of_lt k f g h z w t n hlt)
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (hle.trans hd))

/-- The coefficient is the literal finite alternating sum of all actual ambient Tor lengths. -/
theorem correspondenceIncidenceTorCoefficient_eq_sum
    [Smooth f] [Smooth g] [IsSeparated g] [Smooth h]
    (t : genericPoints (correspondenceIncidence f g h z w)) :
    correspondenceIncidenceTorCoefficient k f g h z w t =
      ∑ n ∈ Finset.range (correspondenceIncidenceTorDegreeBound k f g h z w t.val + 1),
        (-1 : ℤ) ^ n *
          ((Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
              (correspondenceIncidenceAmbientInclusion f g h z w t.val))
            (correspondenceIncidenceTor f g h z w t.val n)).toNat : ℤ) :=
  correspondenceIncidenceTorCoefficient_eq_sum_range k f g h z w t _ le_rfl

end Stacks.Chow
