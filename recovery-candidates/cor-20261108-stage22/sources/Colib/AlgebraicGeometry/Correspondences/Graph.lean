/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Integral graph correspondences

For an integral source and a separated target over any base scheme, the actual
graph is an admissible integral closed subscheme. Its native prime algebraic cycle
therefore belongs to `Stacks.Chow.finiteCorrespondences`. The source-first graph is
Mathlib's canonical `pullback.lift`; its closed image and generic point are the
existing Mathlib and Stacks constructions.

Source: `kangxyz/motivic` at `a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/AlgebraicGeometry/Correspondences/Generators/Basic.lean`, graph section.
The graph over a disconnected smooth source requires a sum over its components;
that construction and compatibility with composition are not asserted here.

Literature: Mazza--Voevodsky--Weibel, *Lecture notes on motivic cohomology*,
Lecture 1, Example 1.2, AMS/Clay published edition (2006). The integral-source
argument uses only target separatedness and an isomorphic source projection.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Function.locallyFinsuppWithin

attribute [local instance] Classical.propDecidable

universe u

namespace Stacks.Chow

variable {S X Y : Scheme.{u}} (φ : X ⟶ Y) (g : Y ⟶ S)

/-- The source-first graph is a closed immersion for a separated target. -/
theorem isClosedImmersion_graphLift [IsSeparated g] :
    IsClosedImmersion (pullback.lift (𝟙 X) φ (by simp) : X ⟶ pullback (C := Scheme) (φ ≫ g) g) := by
  let j : X ⟶ pullback (C := Scheme) (φ ≫ g) g := pullback.lift (𝟙 X) φ (by simp)
  have : IsClosedImmersion (j ≫ pullback.fst (φ ≫ g) g) := by
    simpa [j] using (inferInstance : IsClosedImmersion (𝟙 X))
  exact IsClosedImmersion.of_comp j (pullback.fst (φ ≫ g) g)

/-- The projection from the actual closed graph image to its source is an isomorphism. -/
theorem isIso_graphImage_projection [IsSeparated g] :
    IsIso ((pullback.lift (𝟙 X) φ (by simp) : X ⟶ pullback (C := Scheme) (φ ≫ g) g).ker.subschemeι ≫
      pullback.fst (φ ≫ g) g) := by
  let j : X ⟶ pullback (C := Scheme) (φ ≫ g) g := pullback.lift (𝟙 X) φ (by simp)
  let : IsClosedImmersion j := isClosedImmersion_graphLift φ g
  let π : j.image ⟶ X := j.ker.subschemeι ≫ pullback.fst (φ ≫ g) g
  have hj : j.toImage ≫ π = 𝟙 X := by simp [π, j]
  have hπ : π = inv j.toImage := by
    apply (cancel_epi j.toImage).mp
    simp [hj]
  change IsIso π
  rw [hπ]
  infer_instance

/-- The actual graph image of an integral source is integral. -/
theorem isIntegral_graphImage [IsIntegral X] [IsSeparated g] :
    IsIntegral (pullback.lift (𝟙 X) φ (by simp) : X ⟶ pullback (C := Scheme) (φ ≫ g) g).image := by
  let j : X ⟶ pullback (C := Scheme) (φ ≫ g) g := pullback.lift (𝟙 X) φ (by simp)
  let : IsClosedImmersion j := isClosedImmersion_graphLift φ g
  exact IsIntegral.of_isIso j.toImage

/-- The graph image covers the source's unique irreducible component. -/
theorem range_graphImage_projection_mem [IsIntegral X] [IsSeparated g] :
    Set.range
      ((pullback.lift (𝟙 X) φ (by simp) : X ⟶ pullback (C := Scheme) (φ ≫ g) g).ker.subschemeι ≫
      pullback.fst (φ ≫ g) g) ∈ irreducibleComponents X := by
  let j : X ⟶ pullback (C := Scheme) (φ ≫ g) g := pullback.lift (𝟙 X) φ (by simp)
  let π : j.image ⟶ X := j.ker.subschemeι ≫ pullback.fst (φ ≫ g) g
  let : IsIso π := isIso_graphImage_projection φ g
  have hsurj : Function.Surjective π := (Scheme.homeoOfIso (asIso π)).surjective
  change Set.range π ∈ irreducibleComponents X
  simp [Set.range_eq_univ.mpr hsurj, irreducibleComponents_eq_singleton]

/-- The graph correspondence is the native prime cycle of the actual graph image. -/
def graphFiniteCorrespondence [IsIntegral X] [IsSeparated g] :
    finiteCorrespondences (φ ≫ g) g := by
  let j : X ⟶ pullback (C := Scheme) (φ ≫ g) g := pullback.lift (𝟙 X) φ (by simp)
  letI : IsIso (j.ker.subschemeι ≫ pullback.fst (φ ≫ g) g) :=
    isIso_graphImage_projection φ g
  exact finiteCorrespondenceOfIntegralClosedSubscheme (φ ≫ g) g j.ker
    (isIntegral_graphImage φ g) inferInstance (range_graphImage_projection_mem φ g)

/-- The underlying cycle has multiplicity one at a point whose native integral
closed subscheme is exactly the graph ideal. -/
theorem graphFiniteCorrespondence_prime [IsIntegral X] [IsSeparated g] :
    ∃ z : pullback (C := Scheme) (φ ≫ g) g,
      (graphFiniteCorrespondence φ g).1 = single z 1 ∧
        integralComponentAt z =
          (pullback.lift (𝟙 X) φ (by simp) : X ⟶ pullback (C := Scheme) (φ ≫ g) g).ker := by
  refine ⟨_, rfl, ?_⟩
  exact integralComponentAt_genericPointOf _ (isIntegral_graphImage φ g)

/-- The integral graph correspondence is nonzero. -/
theorem graphFiniteCorrespondence_ne_zero [IsIntegral X] [IsSeparated g] :
    graphFiniteCorrespondence φ g ≠ 0 := by
  obtain ⟨z, hz, -⟩ := graphFiniteCorrespondence_prime φ g
  intro h
  have he := congrArg (fun c : finiteCorrespondences (φ ≫ g) g => c.1 z) h
  simp [hz] at he

end Stacks.Chow
