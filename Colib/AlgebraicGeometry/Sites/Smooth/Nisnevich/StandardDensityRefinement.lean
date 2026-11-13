/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.Topology.Dimension.StandardDensity
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Simple Nisnevich refinements and the standard density filtration

A simple refinement of a sieve is a finite tree of geometric distinguished
squares with the covering condition checked on its leaves. Reducing a square
asks for a new square whose base lies in density degree `d + 1`, with the
other three maps factoring through prescribed open immersions. The overlap
is prescribed in degree `d` and the two pieces in degree `d + 1`.

See Voevodsky, [Homotopy theory of simplicial sheaves in completely
decomposable topologies](https://arxiv.org/abs/0805.4578), Definitions 2.2 and 2.21.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Order Topology TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}}

/-- A pullback of an open immersion and an étale morphism which is an
isomorphism over the actual closed complement. -/
structure IsGeometricNisnevichSquare (Q : Square (SmoothSite S)) : Prop where
  isPullback : Q.IsPullback
  isOpenImmersion : IsOpenImmersion Q.f₂₄.left
  etale : Etale Q.f₃₄.left
  complement : ∃ (Z : Scheme.{u}) (z : Z ⟶ Q.X₄.left),
    IsClosedImmersion z ∧ Set.range z = (Set.range Q.f₂₄.left)ᶜ ∧
      IsIso (pullback.snd Q.f₃₄.left z)

/-- A sieve contains a simple refinement when its pullbacks along the two
pieces recursively do, with identity and empty-object leaves. -/
inductive HasSimpleNisnevichRefinement (P : Square (SmoothSite S) → Prop) :
    (X : SmoothSite S) → Sieve X → Prop
  | identity {X : SmoothSite S} {R : Sieve X} (h : R (𝟙 X)) :
      HasSimpleNisnevichRefinement P X R
  | empty {X : SmoothSite S} {R : Sieve X} (h : IsEmpty X.left) :
      HasSimpleNisnevichRefinement P X R
  | square {Q : Square (SmoothSite S)} (hQ : P Q) {R : Sieve Q.X₄}
      (h₂ : HasSimpleNisnevichRefinement P Q.X₂ (R.pullback Q.f₂₄))
      (h₃ : HasSimpleNisnevichRefinement P Q.X₃ (R.pullback Q.f₃₄)) :
      HasSimpleNisnevichRefinement P Q.X₄ R

/-- Every Nisnevich covering sieve contains a simple refinement by squares in `P`. -/
def NisnevichSimpleRefinements (P : Square (SmoothSite S) → Prop) : Prop :=
  ∀ (X : SmoothSite S) (R : Sieve X), R ∈ nisnevichTopology S X →
    HasSimpleNisnevichRefinement P X R

/-- An open immersion lies in the standard density filtration through its actual image open. -/
structure IsStandardDensityMap {X Y : SmoothSite S} (f : X ⟶ Y) (d : ℕ) : Prop where
  isOpenImmersion : IsOpenImmersion f.left
  density :
    letI := isOpenImmersion
    f.left.opensRange.IsInStandardDensity d

/-- Each chosen square admits a density reduction through the three prescribed opens. -/
def NisnevichSquaresReduce (P : Square (SmoothSite S) → Prop) : Prop :=
  ∀ (Q : Square (SmoothSite S)), P Q → ∀ (d : ℕ) {B A V : SmoothSite S}
    (j₁ : B ⟶ Q.X₁) (j₂ : A ⟶ Q.X₂) (j₃ : V ⟶ Q.X₃),
    IsStandardDensityMap j₁ d → IsStandardDensityMap j₂ (d + 1) →
    IsStandardDensityMap j₃ (d + 1) →
    ∃ Q' : Square (SmoothSite S), P Q' ∧ ∃ φ : Q' ⟶ Q,
      IsStandardDensityMap φ.τ₄ (d + 1) ∧
        (∃ f₁ : Q'.X₁ ⟶ B, f₁ ≫ j₁ = φ.τ₁) ∧
        (∃ f₂ : Q'.X₂ ⟶ A, f₂ ≫ j₂ = φ.τ₂) ∧
        (∃ f₃ : Q'.X₃ ⟶ V, f₃ ≫ j₃ = φ.τ₃)

namespace IsStandardDensityMap

/-- Identity maps lie in every standard density degree. -/
theorem id (X : SmoothSite S) (d : ℕ) : IsStandardDensityMap (𝟙 X) d := by
  have h : IsOpenImmersion (𝟙 X : X ⟶ X).left :=
    inferInstanceAs (IsOpenImmersion (𝟙 X.left))
  refine ⟨h, ?_⟩
  change (Scheme.Hom.opensRange (𝟙 X.left)).IsInStandardDensity d
  rw [Scheme.Hom.opensRange_of_isIso]
  exact TopologicalSpace.Opens.isInStandardDensity_top d

attribute [local instance] specializationOrder in
/-- Composing two open immersions in the same density degree preserves that degree. -/
theorem comp {X Y Z : SmoothSite S} {f : X ⟶ Y} {g : Y ⟶ Z} {d : ℕ}
    (hf : IsStandardDensityMap f d) (hg : IsStandardDensityMap g d) :
    IsStandardDensityMap (f ≫ g) d := by
  let : IsOpenImmersion f.left := hf.isOpenImmersion
  let : IsOpenImmersion g.left := hg.isOpenImmersion
  have h : IsOpenImmersion (f ≫ g).left :=
    inferInstanceAs (IsOpenImmersion (f.left ≫ g.left))
  refine ⟨h, ?_⟩
  intro z hz
  by_cases hz' : z ∈ g.left.opensRange
  · obtain ⟨y, rfl⟩ := Scheme.Hom.mem_opensRange.mp hz'
    have hy : y ∉ f.left.opensRange := by
      intro hy
      obtain ⟨x, hx⟩ := Scheme.Hom.mem_opensRange.mp hy
      exact hz (Scheme.Hom.mem_opensRange.mpr
        ⟨x, (Scheme.Hom.comp_apply f.left g.left x).trans (congrArg g.left hx)⟩)
    rw [Topology.IsOpenEmbedding.coheight_eq g.left g.left.isOpenEmbedding]
    exact hf.density y hy
  · exact hg.density z hz'

/-- Above the topological Krull dimension, a map in the standard density
filtration is an isomorphism. -/
theorem isIso_of_topologicalKrullDim_lt {X Y : SmoothSite S} {f : X ⟶ Y} {d : ℕ}
    (hf : IsStandardDensityMap f d) (hd : topologicalKrullDim Y.left < d) :
    IsIso f := by
  let : IsOpenImmersion f.left := hf.isOpenImmersion
  let : IsIso ((forgetScheme S).map f) := isIso_of_isOpenImmersion_of_opensRange_eq_top
    f.left (hf.density.eq_top_of_topologicalKrullDim_lt hd)
  exact isIso_of_reflects_iso f (forgetScheme S)

end IsStandardDensityMap

end AlgebraicGeometry.Scheme.SmoothSite
