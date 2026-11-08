/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.CoherentCycle.GenericSupportLength
public import Colib.AlgebraicGeometry.Correspondences.Composition.TorStalkComparison
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Finite lengths of actual Tor at generic incidence points

The native Tor sheaves of the two full structure sheaves are coherent. Their
support is contained in the intersection of the two actual closed images, which
is exactly the image of the actual incidence scheme. Consequently their stalks
at every generic incidence point have finite length. The proved structure-stalk
comparison transfers this statement to categorical Tor of the literal local
rings, with their original ambient actions.

Only local finite type over a locally Noetherian base and separatedness of the
middle map are needed. No smoothness, correspondence admissibility, nonemptiness,
connectedness, reduction of the product support, or comparison hypothesis is used.
This theorem does not assert eventual vanishing.

Implementation provenance: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Composition/Incidence/Tor.lean` and `Aglib/AlgebraicGeometry/Intersection/GenericTor.lean`.
The original proof uses a regular diagonal kernel and coefficient Koszul homology.
This reconstruction uses native sheaf coherence and support instead. It is new
source, not an exact recovery of that implementation.

Native mathematical inputs: Stacks 0AZS (coherence), 0AZT (support and stalk
clauses), 02QW (generic stalk length), and Mathlib's `Scheme.Pullback.range_map`.
Validation status: source-only candidate, never compiled in this recovery.
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
This set-theoretic statement is used only to bound a sheaf support, not to replace
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

/-- Native Tor sheaves of the full pushed-forward structure sheaves. -/
abbrev correspondenceIncidenceTorSheaf (n : ℕ) :=
  TorFormula.torSheaf (correspondenceIntersectionAmbient f g h)
    ((Scheme.Modules.pushforward (correspondenceSupportProductInclusion f g h z w)).obj
      (Ample.unitModule (correspondenceSupportProduct f g h z w)))
    ((Scheme.Modules.pushforward (correspondenceTripleInclusion f g h)).obj
      (Ample.unitModule (correspondenceTripleProduct f g h))) n

/-- Actual incidence contains the support of every Tor sheaf, including higher Tor. -/
theorem supp_correspondenceIncidenceTorSheaf_subset [IsSeparated g] (n : ℕ) :
    (SheafOfModules.supp (correspondenceIncidenceTorSheaf f g h z w n) :
        Set (correspondenceIntersectionAmbient f g h)) ⊆
      Set.range (correspondenceIncidenceAmbientInclusion f g h z w) := by
  rw [range_correspondenceIncidenceAmbientInclusion,
    ← supp_pushforwardStructureSheaf (correspondenceSupportProductInclusion f g h z w),
    ← supp_pushforwardStructureSheaf (correspondenceTripleInclusion f g h)]
  exact TorFormula.supp_torSheaf_subset_inter _ _ _ n

/-- Every actual generic-incidence categorical Tor module has finite ambient length. -/
@[stacks 0AZS "coherence input: Tor sheaves of two coherent modules on a locally Noetherian \
scheme are coherent", stacks 0AZT "support and stalk inputs only: Tor sheaves are supported \
on the intersection and their stalks are the Tor modules of the stalks; generic-point finite \
length is a further consequence using the native criterion of 02QW"]
theorem correspondenceIncidenceTor_length_ne_top [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType g] [LocallyOfFiniteType h]
    [IsSeparated g] (t : genericPoints (correspondenceIncidence f g h z w)) (n : ℕ) :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
        (correspondenceIncidenceAmbientInclusion f g h z w t.val))
      (correspondenceIncidenceTor f g h z w t.val n) ≠ ⊤ := by
  have : IsLocallyNoetherian (correspondenceIntersectionAmbient f g h) :=
    isLocallyNoetherian_correspondenceIntersectionAmbient f g h
  have : (correspondenceIncidenceTorSheaf f g h z w n).IsCoherent :=
    TorFormula.isCoherent_torSheaf _ _ _ inferInstance inferInstance n
  have hlength := length_stalk_ne_top_of_supp_subset_range_of_mem_genericPoints
    (correspondenceIncidenceTorSheaf f g h z w n)
    (correspondenceIncidenceAmbientInclusion f g h z w)
    (supp_correspondenceIncidenceTorSheaf_subset f g h z w n) t.val t.property
  rw [incidenceTorSheaf_length_eq_structureStalkTor f g h z w t.val n] at hlength
  exact hlength

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
