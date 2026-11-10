/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Basic
public import Colib.AlgebraicGeometry.Chow.NormalComponents
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Actual normal components of smooth schemes over a field

Smoothness gives native regularity and normality. Finite type over the field gives
Noetherianity of the scheme, not of its ring of global sections. The actual
irreducible components are clopen; their actual open subschemes form an integral
open cover. Empty and disconnected smooth schemes are allowed.

This is a direct-native reconstruction of the component-cover portion of
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Normal.lean` at motivic commit
`a6805c4a87cdfd7717dd7a94039246a167f15380`. It replaces that source's domain-stalk
component infrastructure by the existing normal-component theorems.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

/-- The actual smooth scheme is locally Noetherian by local finite type over a field. -/
instance isLocallyNoetherian_overField (X : SmoothSite (Spec (.of k))) :
    IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) X.hom

/-- Finite type over a field makes the scheme Noetherian, without a global-sections claim. -/
instance isNoetherian_overField (X : SmoothSite (Spec (.of k))) :
    IsNoetherian X.left := by
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace (Y := Spec (.of k)) X.hom
  exact ⟨⟩

/-- Native smooth regularity supplies normality over an arbitrary field. -/
instance isNormal_overField (X : SmoothSite (Spec (.of k))) : IsNormal X.left :=
  isNormal_of_isRegular X.left (isRegular_of_smooth_over_field X.hom)

/-- Distinct actual irreducible components of a smooth object are disjoint. -/
theorem pairwiseDisjoint_irreducibleComponents (X : SmoothSite (Spec (.of k))) :
    (irreducibleComponents X.left).PairwiseDisjoint id := by
  intro C hC D hD hne
  exact disjoint_of_mem_irreducibleComponents_of_isNormal C D hC hD hne

/-- An actual irreducible component is open and closed. -/
theorem isClopen_irreducibleComponent (X : SmoothSite (Spec (.of k)))
    {Z : Set X.left} (hZ : Z ∈ irreducibleComponents X.left) : IsClopen Z :=
  isClopen_of_mem_irreducibleComponents_of_isNormal Z hZ

/-- The actual open subscheme associated with an irreducible component. -/
def componentOpen (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) : X.left.Opens :=
  ⟨Z, (isClopen_irreducibleComponent k X hZ).isOpen⟩

/-- The component open retains precisely the actual component's points. -/
@[simp] theorem coe_componentOpen (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    (componentOpen k X Z hZ : Set X.left) = Z := rfl

/-- Every actual open component is an integral scheme. -/
instance isIntegral_componentOpen (X : SmoothSite (Spec (.of k)))
    (Z : Set X.left) (hZ : Z ∈ irreducibleComponents X.left) :
    IsIntegral (componentOpen k X Z hZ).toScheme := by
  let : IrreducibleSpace (componentOpen k X Z hZ).toScheme :=
    Subtype.irreducibleSpace hZ.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The actual irreducible component opens cover the smooth scheme. -/
def componentOpenCover (X : SmoothSite (Spec (.of k))) : X.left.OpenCover where
  I₀ := irreducibleComponents X.left
  X Z := (componentOpen k X Z.val Z.property).toScheme
  f Z := (componentOpen k X Z.val Z.property).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, fun _ => inferInstance⟩
    intro x
    exact ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩,
      ⟨⟨x, mem_irreducibleComponent⟩, rfl⟩⟩

/-- There are finitely many actual components, including none for the empty scheme. -/
instance finite_componentOpenCover_index (X : SmoothSite (Spec (.of k))) :
    Finite (componentOpenCover k X).I₀ :=
  (NoetherianSpace.finite_irreducibleComponents (α := X.left)).to_subtype

/-- Every member of the component cover is integral. -/
instance isIntegral_componentOpenCover_obj (X : SmoothSite (Spec (.of k)))
    (Z : (componentOpenCover k X).I₀) : IsIntegral ((componentOpenCover k X).X Z) :=
  isIntegral_componentOpen k X Z.val Z.property

end AlgebraicGeometry.Scheme.SmoothSite
