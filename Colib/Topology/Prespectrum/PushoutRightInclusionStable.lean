/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.PushoutConeCollapse
public import Colib.Topology.Prespectrum.ConeStableVanishing
public import Colib.Topology.Prespectrum.PositiveLevelEquivalence

/-!
# The original right pushout inclusion of a stable attaching arrow

Genuine cone-to-fiber excision and stability of an original arrow imply vanishing of its
unchanged cone. The original right-cone collapse then transfers this vanishing to the cone
of a right pushout inclusion. Actual excision for that inclusion detects its stability.
Positive-level point HEP discharges the collapse premise using the existing reduced-cylinder
collapse theorem. No general preservation of stable equivalences by a bare quotient is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
universe u
namespace Topology.LoopPrespectrum

/-- Stable arrows with genuine original cone excision have vanishing original cone groups. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutRightInclusionStable.lean:29"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
theorem mappingCone_stableHomotopyGroup_subsingleton_of_isStableEquivalence
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (he : IsStableEquivalence (mappingConeFiberComparison f))
    (hf : IsStableEquivalence f) (d : ℤ) :
    Subsingleton (stableHomotopyGroup (mappingCone f) d) := by
  have hzero (k : ℤ) (x : stableHomotopyGroup (mappingCone f) (k + 1)) : x = 0 := by
    have hinj := ((ConcreteCategory.isIso_iff_bijective _).mp (hf k)).injective
    have hδ : stableMappingConeConnecting f he k x = 0 := by
      apply hinj
      rw [map_zero]
      exact (stableMappingConeConnecting_exact_source f he k _).mpr ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := (stableMappingConeConnecting_exact_cone f he k x).mp hδ
    obtain ⟨z, rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp (hf (k + 1))).surjective y
    exact hy.symm.trans ((stableMappingCone_exact_target f he (k + 1) _).mpr ⟨z, rfl⟩)
  have hs : Subsingleton (stableHomotopyGroup (mappingCone f) (d - 1 + 1)) :=
    ⟨fun x y ↦ (hzero (d - 1) x).trans (hzero (d - 1) y).symm⟩
  simpa only [sub_add_cancel] using hs

namespace HomotopyPushout
variable {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) (g : A ⟶ C)

/-- Original cone excision and the actual stable cone collapse preserve the right inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutRightInclusionStable.lean:51"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
theorem inr_isStableEquivalence_of_collapse
    (he : IsStableEquivalence (mappingConeFiberComparison f))
    (hi : IsStableEquivalence (mappingConeFiberComparison (inr f g)))
    (hc : IsStableEquivalence (rightConeCollapse f g))
    (hf : IsStableEquivalence f) : IsStableEquivalence (inr f g) := by
  apply isStableEquivalence_of_cone_stableGroup_subsingleton (inr f g) hi
  intro d
  have hinj := ((ConcreteCategory.isIso_iff_bijective _).mp (hc d)).injective
  exact ⟨fun x y ↦ hinj
    ((mappingCone_stableHomotopyGroup_subsingleton_of_isStableEquivalence f he hf d).elim _ _)⟩

/-- Positive-level point HEP and genuine original row excision give the same stable inclusion. -/
@[colib_ref "quillen"
  "Quillen/Topology/Prespectrum/PushoutRightInclusionStable.lean:63"
  "adaptation" "Original actual cone rebracketing, collapse and specified stable excision."]
theorem inr_isStableEquivalence_of_excision
    (hA : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.point (n + 1)))))
    (hB : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.point (n + 1)))))
    (hC : ∀ n, TopCat.HomotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (C.point (n + 1)))))
    (he : IsStableEquivalence (mappingConeFiberComparison f))
    (hi : IsStableEquivalence (mappingConeFiberComparison (inr f g)))
    (hf : IsStableEquivalence f) : IsStableEquivalence (inr f g) :=
  inr_isStableEquivalence_of_collapse f g he hi
    (isStableEquivalence_of_positiveLevel _ (fun n ↦
      rightConeCollapse_level_isWeakHomotopyEquivalence f g (n + 1) (hA n) (hB n) (hC n))) hf

end HomotopyPushout
end Topology.LoopPrespectrum
