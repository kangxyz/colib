/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.ModuleCat.Annihilator
public import Colib.AlgebraicGeometry.Correspondences.Composition.StalkModules
public import Colib.AlgebraicGeometry.Morphisms.ClosedImmersion.TransportedStalkSupport
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.Length
public import StacksFrontier.RingTheory.Support.Finite
public import StacksFrontier.RingTheory.Tor.AlmostFlatResolution
public import StacksFrontier.RingTheory.Tor.Finiteness
public import StacksFrontier.Topology.Sober.Generization

/-!
# Finite lengths of actual Tor at generic incidence points

The two literal closed-immersion stalk modules are finite over the Noetherian
ambient stalk, so their native categorical Tor modules are finite (Stacks 0AZ4).
Both actual stalk-map kernels annihilate Tor by native Tor annihilation and
symmetry (00M3). A prime in its support therefore maps into both closed images.
Their intersection is the actual incidence image, and genericity forces that
prime to be the ambient closed point. Native `isFiniteLength_of_support_subset`
(the zero-inclusive form of 00L5) supplies finite length.

Only local finite type over a locally Noetherian base and separatedness of the
middle map are needed. No smoothness, correspondence admissibility, nonemptiness,
connectedness, reduction of the product support, or comparison hypothesis is used.
This theorem does not assert eventual vanishing.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Composition/Incidence/Tor.lean` and `Aglib/AlgebraicGeometry/Intersection/GenericTor.lean`.
The original uses a regular diagonal kernel and coefficient Koszul homology.
This is a new actual-stalk support proof, not an exact recovery of that source.

Native mathematical inputs: 0AZ4 (finite Tor), 00M3 (Tor symmetry), 00L5
(finite length from support), 01J7 (generizations from the local spectrum),
and Mathlib's `Scheme.Pullback.range_map`. No Tor sheaf is imported.
Native leaf acceptance is recorded separately; no independent review is claimed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
variable (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)

/-- The incidence image is the intersection of the inverse images of the two supports. -/
theorem range_correspondenceIncidenceInclusion :
    Set.range (correspondenceIncidenceInclusion f g h z w) =
      pullback.fst (pullback.snd f g) (pullback.fst g h) ⁻¹'
        Set.range (integralComponentAt z).subschemeι ∩
      pullback.snd (pullback.snd f g) (pullback.fst g h) ⁻¹'
        Set.range (integralComponentAt w).subschemeι := by
  unfold correspondenceIncidenceInclusion
  apply Scheme.Pullback.range_map

/-- The support-product image is determined by both actual support coordinates. -/
theorem range_correspondenceSupportProductInclusion :
    Set.range (correspondenceSupportProductInclusion f g h z w) =
      pullback.fst (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ⁻¹'
        Set.range (integralComponentAt z).subschemeι ∩
      pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g) ⁻¹'
        Set.range (integralComponentAt w).subschemeι := by
  unfold correspondenceSupportProductInclusion
  apply Scheme.Pullback.range_map

/-- The actual incidence image is exactly the intersection of the two closed images.
This set-theoretic statement is used only to bound module support, not to replace
the incidence scheme or its nonreduced local rings. -/
theorem range_correspondenceIncidenceAmbientInclusion :
    Set.range (correspondenceIncidenceAmbientInclusion f g h z w) =
      Set.range (correspondenceSupportProductInclusion f g h z w) ∩
        Set.range (correspondenceTripleInclusion f g h) := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨correspondenceIncidenceToSupportProduct f g h z w t,
        (correspondenceIncidence_ambient_point_eq f g h z w t).symm⟩,
      ⟨correspondenceIncidenceInclusion f g h z w t, rfl⟩⟩
  · rintro ⟨hs, q, rfl⟩
    have hq : q ∈ Set.range (correspondenceIncidenceInclusion f g h z w) := by
      rw [range_correspondenceIncidenceInclusion]
      rw [range_correspondenceSupportProductInclusion] at hs
      simpa only [Set.mem_inter_iff, Set.mem_preimage, ← Scheme.Hom.comp_apply,
        correspondenceTripleInclusion_fst, correspondenceTripleInclusion_snd] using hs
    obtain ⟨t, ht⟩ := hq
    exact ⟨t, congrArg (correspondenceTripleInclusion f g h) ht⟩

/-- The literal four-factor ambient is locally Noetherian under local finite-type hypotheses. -/
theorem isLocallyNoetherian_correspondenceIntersectionAmbient [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h] :
    IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
  have : IsLocallyNoetherian (pullback g h) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd g h)
  exact LocallyOfFiniteType.isLocallyNoetherian
    (pullback.snd (pullback.snd f g ≫ g) (pullback.fst g h ≫ g))

/-- Native categorical Tor of the full support-product and triple-product stalks. -/
abbrev correspondenceIncidenceTor (t : correspondenceIncidence f g h z w) (n : ℕ) :=
  ((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t))) n).obj
    (correspondenceIncidenceSupportStalkModule f g h z w t)).obj
    (correspondenceIncidenceTripleStalkModule f g h z w t)

/-- Every actual generic-incidence categorical Tor module has finite ambient length. -/
@[stacks 0AZ4 "finite native Tor over a Noetherian ring, applied to the two full actual \
closed-immersion stalk modules", stacks 00L5 "the finite-length support criterion applied \
at an actual generic incidence point; the support argument includes zero Tor modules"]
theorem correspondenceIncidenceTor_length_ne_top [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [IsSeparated g] (t : genericPoints (correspondenceIncidence f g h z w)) (n : ℕ) :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t.val))
      (correspondenceIncidenceTor f g h z w t.val n) ≠ ⊤ := by
  have : IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) :=
    isLocallyNoetherian_correspondenceIntersectionAmbient f g h
  let P := correspondenceIntersectionAmbient f g h
  let j := correspondenceIncidenceAmbientInclusion f g h z w
  let p := j t.val
  let A := P.presheaf.stalk p
  let M := correspondenceIncidenceSupportStalkModule f g h z w t.val
  let N := correspondenceIncidenceTripleStalkModule f g h z w t.val
  let T := correspondenceIncidenceTor f g h z w t.val n
  let e := P.presheaf.stalkCongr
    (.of_eq (correspondenceIncidence_ambient_point_eq f g h z w t.val))
  let φ := (e.hom ≫ (correspondenceSupportProductInclusion f g h z w).stalkMap
    (correspondenceIncidenceToSupportProduct f g h z w t.val)).hom
  let ψ := ((correspondenceTripleInclusion f g h).stalkMap
    (correspondenceIncidenceInclusion f g h z w t.val)).hom
  have hφ : Function.Surjective φ :=
    (SurjectiveOnStalks.stalkMap_surjective
      (correspondenceSupportProductInclusion f g h z w) _).comp
        e.commRingCatIsoToRingEquiv.surjective
  have hψ : Function.Surjective ψ :=
    SurjectiveOnStalks.stalkMap_surjective (correspondenceTripleInclusion f g h) _
  have : Module.Finite A M := RingHom.Finite.of_surjective φ hφ
  have : Module.Finite A N := RingHom.Finite.of_surjective ψ hψ
  have : Module.Finite A T := tor_finite_of_noetherian A M N n
  apply Module.length_ne_top_iff.mpr
  apply isFiniteLength_of_support_subset (R := A) (M := T)
  intro q hq
  have hq' : Module.annihilator A T ≤ q.asIdeal :=
    Module.mem_support_iff_of_finite.mp hq
  have hφq : RingHom.ker φ ≤ q.asIdeal := by
    intro a ha
    apply hq'
    apply mem_annihilator_tor_of_mem_annihilator M N n
    exact ModuleCat.ker_le_annihilator_restrictScalars φ
      (ModuleCat.of
        ((correspondenceSupportProduct f g h z w).presheaf.stalk
          (correspondenceIncidenceToSupportProduct f g h z w t.val))
        ((correspondenceSupportProduct f g h z w).presheaf.stalk
          (correspondenceIncidenceToSupportProduct f g h z w t.val))) ha
  have hψq : RingHom.ker ψ ≤ q.asIdeal := by
    obtain ⟨eTor⟩ := tor_symm_canonically_iso A n
    let eSwap : T ≅ ((Tor (ModuleCat A) n).obj N).obj M := (eTor.app M).app N
    intro a ha
    apply hq'
    apply mem_annihilator_of_moduleCat_iso eSwap.symm
    apply mem_annihilator_tor_of_mem_annihilator N M n
    exact ModuleCat.ker_le_annihilator_restrictScalars ψ
      (ModuleCat.of
        ((correspondenceTripleProduct f g h).presheaf.stalk
          (correspondenceIncidenceInclusion f g h z w t.val))
        ((correspondenceTripleProduct f g h).presheaf.stalk
          (correspondenceIncidenceInclusion f g h z w t.val))) ha
  have himage : P.fromSpecStalk p q ∈ Set.range j := by
    rw [range_correspondenceIncidenceAmbientInclusion]
    constructor
    · exact Scheme.Hom.fromSpecStalk_mem_range_of_transported_stalkMap_ker_le
        (correspondenceSupportProductInclusion f g h z w)
        (correspondenceIncidenceToSupportProduct f g h z w t.val) p
        (correspondenceIncidence_ambient_point_eq f g h z w t.val) q hφq
    · exact (Scheme.Hom.ker_stalkMap_le_iff_of_isClosedImmersion
        (correspondenceTripleInclusion f g h)
        (correspondenceIncidenceInclusion f g h z w t.val) q).mp hψq
  obtain ⟨v, hv⟩ := himage
  have hspec : P.fromSpecStalk p q ⤳ p := by
    simpa only [Scheme.range_fromSpecStalk, Set.mem_ofPred_eq] using
      (Set.mem_range_self (f := P.fromSpecStalk p) q)
  have hvt : v ⤳ t.val :=
    j.isClosedEmbedding.isInducing.specializes_iff.mp (hv.symm ▸ hspec)
  have hveq : v = t.val :=
    TopologicalSpace.forall_specializes_eq_of_mem_genericPoints t.property v hvt
  apply Set.mem_singleton_iff.mpr
  apply (P.fromSpecStalk p).isEmbedding.injective
  rw [Scheme.fromSpecStalk_closedPoint]
  exact hv.symm.trans (congrArg j hveq)

/-- The integer conversion of a generic-incidence Tor length does not discard an infinite value. -/
theorem natCast_toNat_length_correspondenceIncidenceTor [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [IsSeparated g] (t : genericPoints (correspondenceIncidence f g h z w)) (n : ℕ) :
    ((Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t.val))
      (correspondenceIncidenceTor f g h z w t.val n)).toNat : ℕ∞) =
      Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t.val))
        (correspondenceIncidenceTor f g h z w t.val n) :=
  ENat.natCast_toNat (correspondenceIncidenceTor_length_ne_top f g h z w t n)

end Stacks.Chow
