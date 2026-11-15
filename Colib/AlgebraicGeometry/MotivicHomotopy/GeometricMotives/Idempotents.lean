/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.GeometricMotives.Effective
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.TorusRightCoproducts
import StacksFrontier.CategoryTheory.Triangulated.Elementary

/-!
# Idempotents in effective geometric motives

A constant countable family of effective motives has a common upper bound.
Its derived coproduct splits idempotents in the effective category, and the
geometric property is preserved by retracts.
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

omit [PerfectField k]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
private theorem hasEffectiveCountableCopower (K : EffectiveMotivesMinus k) :
    HasCoproduct (fun _ : ℕ => K) := by
  let family : ULift.{u + 1} ℕ → EffectiveMotivesMinus k := fun _ => K
  obtain ⟨b, hb⟩ := K.obj.property
  have h : ∀ i, ((effectiveMotivesMinusToDerived k).obj (family i)).IsLE b := fun _ => hb
  let : HasCoproduct family := HasColimit.mk
    ⟨effectiveCofan k family b h, effectiveCofanIsColimit k family b h⟩
  exact hasCoproduct_of_equiv_of_iso family (fun _ : ℕ => K) Equiv.ulift.symm
    (fun _ => Iso.refl _)

instance : IsIdempotentComplete (EffectiveMotivesMinus k) := by
  let : ∀ K : EffectiveMotivesMinus k, HasCoproduct (fun _ : ℕ => K) :=
    hasEffectiveCountableCopower k
  exact (Pretriangulated.isIdempotentComplete_of_hasCountableProducts_or_coproducts
    (EffectiveMotivesMinus k)).2

instance : IsIdempotentComplete (EffectiveGeometricMotives k) where
  idempotents_split X p hp := by
    let F := effectiveGeometricMotivesInclusion k
    have hp' : F.map p ≫ F.map p = F.map p := by rw [← F.map_comp, hp]
    obtain ⟨Y, i, r, hi, hr⟩ := IsIdempotentComplete.idempotents_split X.obj (F.map p) hp'
    let Y' : EffectiveGeometricMotives k :=
      ⟨Y, (isEffectiveGeometric k).prop_of_retract ⟨i, r, hi⟩ X.property⟩
    refine ⟨Y', ObjectProperty.homMk i, ObjectProperty.homMk r, ?_, ?_⟩
    · exact F.map_injective hi
    · exact F.map_injective hr

end AlgebraicGeometry.MotivicHomotopy
