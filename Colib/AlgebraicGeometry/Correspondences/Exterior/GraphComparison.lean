/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Exterior.GraphSupport

/-!
# Uniqueness of actual native integral graph supports

Two integral native closed supports lying in the same actual graph are equal
when their original source images agree. Use Stacks' native genericPointOf /
integralComponentAt uniqueness, rather than a new generator representation.
Adapted from motivic_source_a6805c4, Exterior/Simplex/Graph.lean.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme
universe u
namespace Stacks.Chow

variable {S : Scheme.{u}} (X Y : SmoothSite S)

/-- Integral native closed subschemes with the same underlying support are equal. -/
theorem nativeIntegralClosedSupport_eq
    (W V : (pullback X.hom Y.hom).IdealSheafData)
    (hW : IsIntegral W.subscheme) (hV : IsIntegral V.subscheme)
    (h : (W.support : Set (pullback (C := Scheme) X.hom Y.hom)) = V.support) : W = V := by
  have he : closure ({genericPointOf W hW} : Set (pullback (C := Scheme) X.hom Y.hom)) =
      closure {genericPointOf V hV} := by
    rw [← support_eq_closure_genericPointOf W hW, ← support_eq_closure_genericPointOf V hV]
    exact h
  have hp : genericPointOf W hW = genericPointOf V hV := by
    apply (isGenericPoint_closure :
      IsGenericPoint (genericPointOf W hW) (closure {genericPointOf W hW})).eq
    rw [he]
    exact isGenericPoint_closure
  calc
    W = integralComponentAt (genericPointOf W hW) := (integralComponentAt_genericPointOf W hW).symm
    _ = integralComponentAt (genericPointOf V hV) := congrArg integralComponentAt hp
    _ = V := integralComponentAt_genericPointOf V hV

/-- The actual source image determines an integral support in a fixed graph. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Exterior/Simplex/Graph.lean:63-77"
  "adaptation" "Native integral graph-support equality from actual source-image equality"]
theorem nativeIntegralGraphSupport_eq_of_sourceRange_eq
    (W V : (pullback X.hom Y.hom).IdealSheafData)
    (hWI : IsIntegral W.subscheme) (hVI : IsIntegral V.subscheme)
    (φ : X ⟶ Y)
    (hW : exteriorSupportSourceProjection X Y W ≫ φ.left =
      exteriorSupportTargetProjection X Y W)
    (hV : exteriorSupportSourceProjection X Y V ≫ φ.left =
      exteriorSupportTargetProjection X Y V)
    (h : Set.range (exteriorSupportSourceProjection X Y W) =
      Set.range (exteriorSupportSourceProjection X Y V)) : W = V := by
  apply nativeIntegralClosedSupport_eq X Y W V hWI hVI
  rw [← Scheme.IdealSheafData.range_subschemeι, ← Scheme.IdealSheafData.range_subschemeι]
  rw [exteriorSupport_inclusion_eq_graph X Y W φ hW,
    exteriorSupport_inclusion_eq_graph X Y V φ hV]
  change Set.range ((pullback.lift (C := Scheme) (𝟙 X.left) φ.left
        (by simp only [Category.id_comp, MorphismProperty.Over.w])) ∘
      exteriorSupportSourceProjection X Y W) =
    Set.range ((pullback.lift (C := Scheme) (𝟙 X.left) φ.left
        (by simp only [Category.id_comp, MorphismProperty.Over.w])) ∘
      exteriorSupportSourceProjection X Y V)
  rw [Set.range_comp, Set.range_comp, h]

end Stacks.Chow
