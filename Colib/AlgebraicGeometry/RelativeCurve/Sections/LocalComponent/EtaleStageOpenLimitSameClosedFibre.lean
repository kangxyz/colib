/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.EtaleStageOpenOriginalSection
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Equality on the actual strict-local closed fibre from one actual marked stage

The finite stage is an arbitrary a0 : Over i, not a terminal-identity pullback
identified with U. Equality at its original geometric marking implies equality
on the closed residue field of the original etale local ring.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
set_option backward.isDefEq.respectTransparency false
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [QuasiSeparatedSpace S] (X : SmoothSite S)
  (s : GeometricPoint X.left) {N : Scheme.{u}} (p : N ⟶ X.left)
  (i : SmallEtaleNeighborhood X s) (U : ((etaleCurveDiagram X s p).obj i).Opens)
  (B : BigEtaleSite.{u}) (hX : B.Contains X.left)
  (σ τ : (smallEtaleNeighborhoodToSmooth X s ⋙ forgetScheme S).obj i ⟶ U.toScheme)
  (hσ : σ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)
  (hτ : τ ≫ (U.ι ≫ (etaleCurveStructure X s p).app i) = 𝟙 _)

/-- The original limit sections agree after the geometric point if their actual
sections at any specified finite stage agree after that stage's original mark. -/
theorem etaleStageOpenLimitSection_same_geometric_mark (a0 : Over i)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U σ hσ a0 =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U τ hτ a0) :
    geometricPointToStrictHenselization B X.left hX s ≫
        etaleStageOpenLimitSection X s p i U B hX σ hσ =
      geometricPointToStrictHenselization B X.left hX s ≫
        etaleStageOpenLimitSection X s p i U B hX τ hτ := by
  apply (etaleStageOpenCone_isPullback X s p i U B hX a0).hom_ext
  · simp only [Category.assoc, etaleStageOpenLimitSection_comp]
    simpa only [← Category.assoc,
      geometricPointToStrictHenselization_comp_smallEtaleNeighborhoodCone_π] using hmark
  · simp only [Category.assoc, etaleStageOpenLimitSection_structure]

omit [QuasiSeparatedSpace S] in
/-- Equality at the canonical geometric point descends along the faithfully flat
extension of the etale-local residue field. This uses the actual germ evaluation. -/
theorem strictLocal_residue_maps_eq_of_geometric_eq {T : Scheme.{u}}
    (v w : strictHenselization B X.left hX s ⟶ T)
    (heq : geometricPointToStrictHenselization B X.left hX s ≫ v =
      geometricPointToStrictHenselization B X.left hX s ≫ w) :
    Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue ↥(etaleLocalRing B X.left hX s))) ≫ v =
      Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue ↥(etaleLocalRing B X.left hX s))) ≫ w := by
  let := structureSheafStalkToGeometricField_isLocalHom B X.left hX s
  let φ := IsLocalRing.ResidueField.lift (structureSheafStalkToGeometricField B X.left hX s)
  let z := Spec.map (CommRingCat.ofHom φ)
  have : Surjective z := ⟨Function.surjective_to_subsingleton _⟩
  have : Epi z := Flat.epi_of_flat_of_surjective z
  have hz : z ≫ Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue ↥(etaleLocalRing B X.left hX s))) =
      geometricPointToStrictHenselization B X.left hX s := by
    change Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom _) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun ψ => Spec.map (CommRingCat.ofHom ψ))
      (IsLocalRing.ResidueField.lift_comp_residue _)
  apply (cancel_epi z).mp
  simpa only [← Category.assoc, hz] using heq

/-- The original two component-limit sections agree as morphisms on the actual
closed residue field. This is the hst input of the same-root supplier. -/
theorem etaleStageOpenLimitSection_same_closed_fibre (a0 : Over i)
    (hmark : etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U σ hσ a0 =
      etaleNeighborhoodMark X s.hom
        ((smallEtaleNeighborhoodInclusion X s).obj a0.left) ≫
          etaleStageOpenSection X s p i U τ hτ a0) :
    Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue ↥(etaleLocalRing B X.left hX s))) ≫
      etaleStageOpenLimitSection X s p i U B hX σ hσ =
    Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue ↥(etaleLocalRing B X.left hX s))) ≫
      etaleStageOpenLimitSection X s p i U B hX τ hτ :=
  strictLocal_residue_maps_eq_of_geometric_eq X s B hX _ _
    (etaleStageOpenLimitSection_same_geometric_mark X s p i U B hX σ τ hσ hτ a0 hmark)

end AlgebraicGeometry.Scheme.SmoothSite
