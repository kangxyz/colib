/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.Topology
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootExtraction

/-! # Actual finite étale root covers of smooth-site objects -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Opposite

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite.Kummer

/-- The finite root algebra of a literal global unit. -/
abbrev rootAlgebra {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) :=
  AdjoinRoot (X ^ n - C (v : Γ(T, ⊤)))

/-- The affine morphism adjoining the root. -/
def rootSpecMap {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) :
    Spec (.of (rootAlgebra v n)) ⟶ Spec (Γ(T, ⊤)) :=
  Spec.map (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (rootAlgebra v n)))

/-- Adjoining a root of nonzero degree is finite. -/
theorem rootSpecMap_finite {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ)
    (n : ℕ) (hn : n ≠ 0) : IsFinite (rootSpecMap v n) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr (Stacks.Kummer.finite_adjoinRoot_unit hn v)

/-- Invertibility of the degree makes the root morphism étale. -/
theorem rootSpecMap_etale {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ)
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(T, ⊤))) :
    Etale (rootSpecMap v n) := by
  apply (HasRingHomProperty.Spec_iff (P := @Etale)).2
  exact RingHom.etale_algebraMap.mpr (Stacks.Kummer.etale_adjoinRoot_unit hunit hn v)

/-- The finite root morphism covers every prime, including the empty-scheme case. -/
theorem rootSpecMap_surjective {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ)
    (n : ℕ) (hn : n ≠ 0) : Surjective (rootSpecMap v n) :=
  ⟨Stacks.Kummer.comap_surjective_adjoinRoot_unit hn v⟩

/-- The canonical map to the spectrum of all global functions. -/
def globalSpecMap (T : Scheme.{u}) : T ⟶ Spec (Γ(T, ⊤)) :=
  T.toSpecΓ

/-- The root cover on the original, potentially nonaffine scheme. -/
def rootScheme {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) : Scheme.{u} :=
  pullback (rootSpecMap v n) (globalSpecMap T)

/-- Its actual projection to the original scheme. -/
def rootProjection {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ) (n : ℕ) :
    rootScheme v n ⟶ T :=
  pullback.snd (rootSpecMap v n) (globalSpecMap T)

/-- Finiteness survives the canonical base change. -/
theorem rootProjection_finite {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ)
    (n : ℕ) (hn : n ≠ 0) : IsFinite (rootProjection v n) := by
  have := rootSpecMap_finite v n hn
  change IsFinite (pullback.snd (rootSpecMap v n) (globalSpecMap T))
  infer_instance

/-- Étaleness survives the canonical base change. -/
theorem rootProjection_etale {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ)
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(T, ⊤))) :
    Etale (rootProjection v n) := by
  have := rootSpecMap_etale v n hn hunit
  change Etale (pullback.snd (rootSpecMap v n) (globalSpecMap T))
  infer_instance

/-- Surjectivity survives the canonical base change. -/
theorem rootProjection_surjective {T : Scheme.{u}} (v : Γ(T, ⊤)ˣ)
    (n : ℕ) (hn : n ≠ 0) : Surjective (rootProjection v n) := by
  have := rootSpecMap_surjective v n hn
  change Surjective (pullback.snd (rootSpecMap v n) (globalSpecMap T))
  infer_instance

/-- The finite étale root cover really is an object of the original smooth site. -/
def rootObject {S : Scheme.{u}} (T : SmoothSite S) (v : Γ(T.left, ⊤)ˣ)
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(T.left, ⊤))) : SmoothSite S := by
  have := rootProjection_finite v n hn
  have := rootProjection_etale v n hn hunit
  exact SmoothSite.mk (rootProjection v n ≫ T.hom)

/-- The covering projection as a morphism in the original smooth category. -/
def rootObjectMap {S : Scheme.{u}} (T : SmoothSite S) (v : Γ(T.left, ⊤)ˣ)
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(T.left, ⊤))) :
    rootObject T v n hn hunit ⟶ T :=
  SmoothSite.homMk (rootProjection v n) rfl

/-- The singleton root family is a genuine smooth étale cover. -/
theorem rootObject_cover {S : Scheme.{u}} (T : SmoothSite S) (v : Γ(T.left, ⊤)ˣ)
    (n : ℕ) (hn : n ≠ 0) (hunit : IsUnit (n : Γ(T.left, ⊤))) :
    Presieve.ofArrows (fun _ : Unit => rootObject T v n hn hunit)
      (fun _ => rootObjectMap T v n hn hunit) ∈ etalePrecoverage S T := by
  apply (ofArrows_mem_etalePrecoverage_iff _).mpr
  refine ⟨fun _ => rootProjection_etale v n hn hunit, ?_⟩
  intro x
  obtain ⟨y, hy⟩ := (rootProjection_surjective v n hn).surj x
  exact ⟨(), y, hy⟩

end AlgebraicGeometry.Scheme.SmoothSite.Kummer
