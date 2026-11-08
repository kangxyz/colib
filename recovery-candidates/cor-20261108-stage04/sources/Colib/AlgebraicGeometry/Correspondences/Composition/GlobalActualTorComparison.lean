/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.OpenTorComparison
public import Colib.AlgebraicGeometry.Correspondences.Composition.AffineActualTorComparison

/-!
# Global actual incidence Tor and actual pulled-support Tor

New recovery reconstruction, 2026-11-08. This is not the lost static candidate's
byte sequence and has not been compiled. Every prerequisite must be independently
restored and validated before this theorem is counted as established.

Over any field, the actual ambient incidence Tor length agrees in every degree
with the Tor length of the two original pulled ideal subschemes. All factor affine
neighborhoods, actual restricted integral supports, maps and point lifts are
constructed. The inverse-image ideal is identified exactly by the native generic
point inverse theorem, not by an equality of support sets. Neither the support
product nor the pulled schemes is replaced by its reduction.

The factor schemes need not be nonempty, integral, connected, smooth or separated.
No comparison or flat-support hypothesis is supplied. This endpoint does not by
itself construct finite Euler sums, cycles, units, or associativity.

Source: motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
Motivic/AlgebraicGeometry/Correspondences/Composition/Incidence/GlobalAmbientTorComparison.lean.
The original source uses arbitrary closed-support affine comparison. This proof
instead uses exact integral restrictions to consume the already existing affine
integral-support specialization. Stacks Project background: Tags 01J3, 0098,
0660 and 0B0T; finite-correspondence context: MVW2006, Lecture 1.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow

/-- The actual affine comparison for arbitrary structure maps out of three spectra.
Their algebra structures are derived from those exact maps. -/
theorem affineIncidenceTor_length_eq_pulledStalkTor_of_homs
    (k : Type u) [Field k] (A B C : CommRingCat.{u})
    (f : Spec A ⟶ Spec (.of k)) (g : Spec B ⟶ Spec (.of k))
    (h : Spec C ⟶ Spec (.of k))
    (z : pullback f g) (w : pullback g h)
    (t : correspondenceIncidence f g h z w) (n : ℕ) :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t))
      (((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t))) n).obj
        (correspondenceIncidenceSupportStalkModule f g h z w t)).obj
        (correspondenceIncidenceTripleStalkModule f g h z w t)) =
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z w t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z w t)) := by
  rcases A with ⟨A, hA⟩
  rcases B with ⟨B, hB⟩
  rcases C with ⟨C, hC⟩
  obtain ⟨f, rfl⟩ := Spec.map_surjective f
  obtain ⟨g, rfl⟩ := Spec.map_surjective g
  obtain ⟨h, rfl⟩ := Spec.map_surjective h
  rcases f with ⟨f⟩
  rcases g with ⟨g⟩
  rcases h with ⟨h⟩
  letI : Algebra k A := f.toAlgebra
  letI : Algebra k B := g.toAlgebra
  letI : Algebra k C := h.toAlgebra
  exact affineIncidenceTor_length_eq_pulledStalkTor k A B C z w t n

open CorrespondenceOpenNeighborhoods

/-- At every actual incidence point, ambient Tor and original pulled-support Tor have
identical extended-natural lengths in every degree over an arbitrary field. -/
theorem incidenceTor_length_eq_pulledStalkTor
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k)) (h : Z ⟶ Spec (.of k))
    (z : pullback f g) (w : pullback g h)
    (t : correspondenceIncidence f g h z w) (n : ℕ) :
    Module.length ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t))
      (((Tor (ModuleCat ((correspondenceIntersectionAmbient f g h).presheaf.stalk
      (correspondenceIncidenceAmbientInclusion f g h z w t))) n).obj
        (correspondenceIncidenceSupportStalkModule f g h z w t)).obj
        (correspondenceIncidenceTripleStalkModule f g h z w t)) =
    Module.length ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))
      (((Tor (ModuleCat ((correspondenceTripleProduct f g h).presheaf.stalk
      (correspondenceIncidenceInclusion f g h z w t))) n).obj
        (correspondenceIncidenceLeftPulledStalkModule f g h z w t)).obj
        (correspondenceIncidenceRightPulledStalkModule f g h z w t)) := by
  obtain ⟨A, B, C, uX, uY, uZ, huX, huY, huZ, q, hq⟩ :=
    exists_affineTripleNeighborhood f g h (correspondenceIncidenceInclusion f g h z w t)
  letI := huX
  letI := huY
  letI := huZ
  have hr : correspondenceIncidenceInclusion f g h z w t ∈
      Set.range (tripleMap f g h uX uY uZ) := ⟨q, hq⟩
  rw [range_tripleMap] at hr
  have hI : (integralComponentAt z).subschemeι (pullback.fst _ _ t) ∈
      Set.range (productMap f g uX uY) := by
    have hmem := hr.1
    change (correspondenceIncidenceInclusion f g h z w ≫
      pullback.fst (pullback.snd f g) (pullback.fst g h)) t ∈ _ at hmem
    rw [correspondenceIncidenceInclusion_fst] at hmem
    exact hmem
  have hJ : (integralComponentAt w).subschemeι (pullback.snd _ _ t) ∈
      Set.range (productMap g h uY uZ) := by
    have hmem := hr.2
    change (correspondenceIncidenceInclusion f g h z w ≫
      pullback.snd (pullback.snd f g) (pullback.fst g h)) t ∈ _ at hmem
    rw [correspondenceIncidenceInclusion_snd] at hmem
    exact hmem
  letI := isIntegral_integralComponentAt z
  letI := isIntegral_integralComponentAt w
  obtain ⟨z', hz', vI, hvI, hi, hrI, tI, htI⟩ :=
    exists_openIntegralComponentAt (integralComponentAt z) (productMap f g uX uY)
      (pullback.fst _ _ t) hI
  obtain ⟨w', hw', vJ, hvJ, hj, hrJ, tJ, htJ⟩ :=
    exists_openIntegralComponentAt (integralComponentAt w) (productMap g h uY uZ)
      (pullback.snd _ _ t) hJ
  letI := hvI
  letI := hvJ
  obtain ⟨t', ht'⟩ := exists_incidenceMap_point f g h uX uY uZ z w z' w'
    vI vJ hi hj t ⟨tI, htI⟩ ⟨tJ, htJ⟩
  have hAmbient := incidenceTor_length_eq_open f g h uX uY uZ z w z' w'
    vI vJ hi hj t' n
  have hPulled := pulledTor_length_eq_open f g h uX uY uZ z w z' w'
    vI vJ hi hj t' n
  rw [ht'] at hAmbient hPulled
  exact hAmbient.trans ((affineIncidenceTor_length_eq_pulledStalkTor_of_homs
    k A B C (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' t' n).trans hPulled.symm)

end Stacks.Chow
