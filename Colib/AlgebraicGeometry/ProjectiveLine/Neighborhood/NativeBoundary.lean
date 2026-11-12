/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.ProjectiveMap.NativeLine
public import Colib.AlgebraicGeometry.Morphisms.Finite.ClosedBoundaryAffineChart
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineRigidityOverRing
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# The whole boundary of an original polynomial zero neighborhood

The compactification is the existing native projective space. The whole original
zero is `Spec R`, without reduction. Its opposite affine chart proves finiteness
of the entire missing boundary, without a monic equation or a supplied finite
boundary. The vanishing ideal constructs precisely the missing projective open.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u

namespace AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine
variable (R : Type u) [CommRing R]

/-- The native second polynomial chart, with its original coordinate. -/
def oppositeChart : Spec (.of (Polynomial R)) ⟶ projectiveSpaceOverRing 1 (.of R) :=
  projectiveLineYChart R ≫ (projectiveLineIsoProjectiveSpaceOver R).hom

instance : IsOpenImmersion (oppositeChart R) := by unfold oppositeChart; infer_instance

/-- The original whole zero section, including every nilpotent of R. -/
def zeroSection : Spec (.of R) ⟶ projectiveSpaceOverRing 1 (.of R) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫ chart R

@[reassoc (attr := simp)] theorem zeroSection_projection :
    zeroSection R ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) = 𝟙 _ := by
  rw [zeroSection, Category.assoc, chart_projection, ← Spec.map_comp]
  have h : CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R) ≫
      CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)) = 𝟙 _ := by ext r; simp
  rw [h, Spec.map_id]

instance : IsClosedImmersion (zeroSection R) := by
  have : IsClosedImmersion
      (zeroSection R ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))) := by
    rw [zeroSection_projection]
    infer_instance
  exact IsClosedImmersion.of_comp _ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))

/-- The opposite chart is exactly the complement of the whole original zero. -/
theorem range_oppositeChart :
    Set.range (oppositeChart R) = (Set.range (zeroSection R))ᶜ := by
  ext x
  let e := projectiveLineIsoProjectiveSpaceOver R
  have hsurj : Function.Surjective e.hom := fun x =>
    ⟨e.inv x, congrArg (fun f => f x) e.inv_hom_id⟩
  obtain ⟨y, rfl⟩ := hsurj x
  have hleft : Function.LeftInverse e.inv e.hom := fun x =>
    congrArg (fun f => f x) e.hom_inv_id
  have hi := hleft.injective
  have hy : y ∈ Set.range (projectiveLineYChart R) ↔
      y ∉ Set.range (projectiveLineZeroSection R) :=
    Iff.of_eq (congrArg (fun C : Set (projectiveLine R) => y ∈ C)
      (range_projectiveLineYChart_eq_compl (R := R)))
  constructor
  · rintro ⟨a, ha⟩ ⟨b, hb⟩
    have ha' : projectiveLineYChart R a = y := hi ha
    have hb' : projectiveLineZeroSection R b = y := hi hb
    exact hy.mp ⟨a, ha'⟩ ⟨b, hb'⟩
  · intro hx
    have hy' : y ∉ Set.range (projectiveLineZeroSection R) := by
      rintro ⟨b, hb⟩
      exact hx ⟨b, congrArg (projectiveLineIsoProjectiveSpaceOver R).hom hb⟩
    obtain ⟨a, ha⟩ := hy.mpr hy'
    exact ⟨a, congrArg (projectiveLineIsoProjectiveSpaceOver R).hom ha⟩

/-- Every complete closed boundary disjoint from zero lies in the affine opposite chart. -/
theorem isFinite_boundary_disjoint_zero {D : Scheme.{u}}
    (d : D ⟶ projectiveSpaceOverRing 1 (.of R)) [IsClosedImmersion d]
    (hd : Disjoint (Set.range d) (Set.range (zeroSection R))) :
    IsFinite (d ≫ (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))) := by
  apply Scheme.isFinite_closed_boundary_in_affine_chart
    (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R)) d
    (oppositeChart R).opensRange (isAffineOpen_opensRange (oppositeChart R))
  intro x hx
  change x ∈ Set.range (oppositeChart R)
  rw [range_oppositeChart]
  exact fun hz => Set.disjoint_left.mp hd hx hz

namespace ZeroNeighborhood
variable (O : (Spec (.of (Polynomial R))).Opens)

/-- The unchanged original open in its native projective compactification. -/
abbrev projectiveOpen : (projectiveSpaceOverRing 1 (.of R)).Opens := chart R ''ᵁ O

/-- The whole missing projective neighborhood, including infinity. -/
def boundaryIdeal : (projectiveSpaceOverRing 1 (.of R)).IdealSheafData :=
  IdealSheafData.vanishingIdeal
    ⟨(projectiveOpen R O : Set _)ᶜ, (projectiveOpen R O).isOpen.isClosed_compl⟩

/-- The closed subscheme cut out by the vanishing ideal of the complement of the open. -/
abbrev boundary : Scheme.{u} := (boundaryIdeal R O).subscheme

/-- The defining closed immersion of the boundary into the native projective line. -/
abbrev boundaryInclusion : boundary R O ⟶ projectiveSpaceOverRing 1 (.of R) :=
  (boundaryIdeal R O).subschemeι

theorem range_boundaryInclusion :
    Set.range (boundaryInclusion R O) = (projectiveOpen R O : Set _)ᶜ := by
  rw [IdealSheafData.range_subschemeι]
  simp [boundaryIdeal]

/-- No finite boundary is assumed: it follows from the whole zero contained in O. -/
theorem boundary_finite
    (hO : Set.range (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))) ⊆ O) :
    IsFinite (boundaryInclusion R O ≫
      (projectiveSpaceOverRing 1 (.of R) ↘ Spec (.of R))) := by
  apply isFinite_boundary_disjoint_zero
  apply Set.disjoint_left.mpr
  intro x hx hz
  rw [range_boundaryInclusion] at hx
  obtain ⟨b, rfl⟩ := hz
  exact hx ⟨_, hO ⟨b, rfl⟩, rfl⟩

/-- The original source and the full missing boundary are disjoint. -/
theorem inclusion_disjoint_boundary :
    Disjoint (Set.range (O.ι ≫ chart R)) (Set.range (boundaryInclusion R O)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ hx
  rw [range_boundaryInclusion] at hx
  exact hx ⟨x.val, x.property, rfl⟩

/-- The original punctured open, before any coefficient localization. -/
abbrev punctureOpen : (Spec (.of (Polynomial R))).Opens :=
  O ⊓ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)

/-- The actual retained target map into the same projective compactification. -/
abbrev retainedInclusion : (punctureOpen R O).toScheme ⟶ projectiveSpaceOverRing 1 (.of R) :=
  (punctureOpen R O).ι ≫ chart R

theorem punctureOpen_affine (hO : IsAffineOpen O) : IsAffineOpen (punctureOpen R O) :=
  hO.inf (IsAffineOpen.Spec_basicOpen _)

/-- Every point of the compactification lies in the retained target, full boundary, or zero. -/
theorem retained_boundary_zero_cover (x : projectiveSpaceOverRing 1 (.of R)) :
    x ∈ Set.range (retainedInclusion R O) ∨
      x ∈ Set.range (boundaryInclusion R O) ∨ x ∈ Set.range (zeroSection R) := by
  classical
  by_cases hx : x ∈ projectiveOpen R O
  · obtain ⟨y, hyO, hy⟩ := hx
    by_cases hyX : y ∈ PrimeSpectrum.basicOpen (Polynomial.X : Polynomial R)
    · exact Or.inl ⟨⟨y, hyO, hyX⟩, hy⟩
    · right; right
      have hy0 : Polynomial.X ∈ y.asIdeal := by
        change ¬ Polynomial.X ∉ y.asIdeal at hyX
        exact not_not.mp hyX
      obtain ⟨b, hb⟩ := (mem_range_evalZero_iff R y).mpr hy0
      exact ⟨b, (congrArg (fun z => (chart R) z) hb).trans hy⟩
  · right; left
    rwa [range_boundaryInclusion]

end ZeroNeighborhood
end AlgebraicGeometry.Scheme.RelativeCurve.NativeProjectiveLine
