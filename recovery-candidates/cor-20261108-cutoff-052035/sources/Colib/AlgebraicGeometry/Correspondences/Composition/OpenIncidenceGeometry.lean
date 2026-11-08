/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.OpenProductNeighborhoods
public import Colib.AlgebraicGeometry.Correspondences.Composition.OpenIntegralSupports

/-!
# Actual incidence and support-product maps on open neighborhoods

New recovery reconstruction, 2026-11-08, from the retained next-stage proof route.
Not compiled, not asserted byte-identical to the lost static draft. The morphisms
are native pullback maps between the existing actual incidence/support schemes.
The square hypotheses concern actual closed-scheme maps, not support-set equality.
Source background: motivic@a6805c4, Correspondences/Support/OpenNeighborhoods.lean.
Native construction and range theorem: Mathlib CategoryTheory.Limits.pullback.map
and AlgebraicGeometry.Scheme.Pullback.range_map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Chow.CorrespondenceOpenNeighborhoods

variable {S X Y Z X' Y' Z' : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  (uX : X' ⟶ X) (uY : Y' ⟶ Y) (uZ : Z' ⟶ Z)
  (z : pullback f g) (w : pullback g h)
  (z' : pullback (uX ≫ f) (uY ≫ g)) (w' : pullback (uY ≫ g) (uZ ≫ h))
  (vI : (integralComponentAt z').subscheme ⟶ (integralComponentAt z).subscheme)
  (vJ : (integralComponentAt w').subscheme ⟶ (integralComponentAt w).subscheme)
  (hi : vI ≫ (integralComponentAt z).subschemeι =
    (integralComponentAt z').subschemeι ≫ productMap f g uX uY)
  (hj : vJ ≫ (integralComponentAt w).subschemeι =
    (integralComponentAt w').subschemeι ≫ productMap g h uY uZ)

/-- The exact left support square preserves the middle coordinate. -/
theorem supportMap_snd :
    (integralComponentAt z').subschemeι ≫ pullback.snd (uX ≫ f) (uY ≫ g) ≫ uY =
      vI ≫ (integralComponentAt z).subschemeι ≫ pullback.snd f g := by
  simpa only [Category.assoc, productMap_snd] using
    congrArg (fun a => a ≫ pullback.snd f g) hi.symm

/-- The exact right support square preserves the middle coordinate. -/
theorem supportMap_fst :
    (integralComponentAt w').subschemeι ≫ pullback.fst (uY ≫ g) (uZ ≫ h) ≫ uY =
      vJ ≫ (integralComponentAt w).subschemeι ≫ pullback.fst g h := by
  simpa only [Category.assoc, productMap_fst] using
    congrArg (fun a => a ≫ pullback.fst g h) hj.symm

/-- The actual incidence map is base change in the same middle open coordinate. -/
def incidenceMap :
    correspondenceIncidence (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' ⟶
      correspondenceIncidence f g h z w :=
  pullback.map _ _ _ _ vI vJ uY
    (supportMap_snd f g uX uY z z' vI hi)
    (supportMap_fst g h uY uZ w w' vJ hj)

/-- The actual product support retains both full closed supports over the base. -/
def supportProductMap :
    correspondenceSupportProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' ⟶
      correspondenceSupportProduct f g h z w :=
  pullback.map _ _ _ _ vI vJ (𝟙 S)
    (by simpa only [Category.comp_id, Category.assoc] using
      congrArg (fun a => a ≫ g) (supportMap_snd f g uX uY z z' vI hi))
    (by simpa only [Category.comp_id, Category.assoc] using
      congrArg (fun a => a ≫ g) (supportMap_fst g h uY uZ w w' vJ hj))

instance [IsOpenImmersion vI] [IsOpenImmersion vJ] [IsOpenImmersion uY] :
    IsOpenImmersion (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj) := by
  unfold incidenceMap
  infer_instance

instance [IsOpenImmersion vI] [IsOpenImmersion vJ] :
    IsOpenImmersion (supportProductMap f g h uX uY uZ z w z' w' vI vJ hi hj) := by
  unfold supportProductMap
  infer_instance

/-- Incidence restriction commutes with the actual triple inclusion. -/
@[reassoc (attr := simp)]
theorem incidenceMap_inclusion :
    incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj ≫
      correspondenceIncidenceInclusion f g h z w =
    correspondenceIncidenceInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' ≫
      tripleMap f g h uX uY uZ := by
  apply pullback.hom_ext <;>
    simp [incidenceMap, correspondenceIncidenceInclusion, hi, hj]

/-- Product-support restriction commutes with the actual ambient inclusion. -/
@[reassoc (attr := simp)]
theorem supportProductMap_inclusion :
    supportProductMap f g h uX uY uZ z w z' w' vI vJ hi hj ≫
      correspondenceSupportProductInclusion f g h z w =
    correspondenceSupportProductInclusion (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' ≫
      ambientMap f g h uX uY uZ := by
  apply pullback.hom_ext <;>
    simp [supportProductMap, correspondenceSupportProductInclusion, hi, hj]

/-- The actual incidence-to-product map is unchanged under the open squares. -/
@[reassoc (attr := simp)]
theorem incidenceMap_toSupportProduct :
    incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj ≫
      correspondenceIncidenceToSupportProduct f g h z w =
    correspondenceIncidenceToSupportProduct (uX ≫ f) (uY ≫ g) (uZ ≫ h) z' w' ≫
      supportProductMap f g h uX uY uZ z w z' w' vI vJ hi hj := by
  apply pullback.hom_ext <;>
    simp [incidenceMap, supportProductMap, correspondenceIncidenceToSupportProduct]

/-- Two lifts of the support coordinates give an actual incidence point lift.
Only the native monomorphism of the middle open immersion is used. -/
theorem exists_incidenceMap_point [IsOpenImmersion uY]
    (t : correspondenceIncidence f g h z w)
    (hI : pullback.fst _ _ t ∈ Set.range vI)
    (hJ : pullback.snd _ _ t ∈ Set.range vJ) :
    ∃ t', incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj t' = t := by
  change t ∈ Set.range (incidenceMap f g h uX uY uZ z w z' w' vI vJ hi hj)
  unfold incidenceMap
  rw [Scheme.Pullback.range_map]
  exact ⟨hI, hJ⟩

end Stacks.Chow.CorrespondenceOpenNeighborhoods
