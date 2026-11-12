/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Sections.LocalComponent.Basic

/-! # The original normal component maps into its specified clopen stage model

Containment is proved from the original marked point and connectedness, rather
than assumed from equality of two inverse images at the limit.
-/
@[expose] public noncomputable section
open CategoryTheory TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme

/-- A connected original component lands in a prescribed clopen model whenever
its original marked point does. -/
theorem normalComponent_range_subset_clopen
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (f : X ⟶ Y) (x : X) (V : Y.Opens) (hV : IsClopen (V : Set Y))
    (hx : f x ∈ V) :
    Set.range ((normalComponentOpen x).ι ≫ f) ⊆ Set.range V.ι := by
  rw [Opens.range_ι]
  let t : (normalComponentOpen x).toScheme := ⟨x, mem_normalComponentOpen x⟩
  exact (isPreconnected_range ((normalComponentOpen x).ι ≫ f).continuous).subset_isClopen
    hV ⟨f x, ⟨t, rfl⟩, hx⟩

/-- The actual normal component factors through the original chosen clopen model. -/
def normalComponentToClopenModel
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (f : X ⟶ Y) (x : X) (V : Y.Opens) (hV : IsClopen (V : Set Y))
    (hx : f x ∈ V) : (normalComponentOpen x).toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι ((normalComponentOpen x).ι ≫ f)
    (normalComponent_range_subset_clopen f x V hV hx)

/-- This is a factorization of the unchanged actual component morphism. -/
@[simp, reassoc] theorem normalComponentToClopenModel_fac
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X]
    (f : X ⟶ Y) (x : X) (V : Y.Opens) (hV : IsClopen (V : Set Y))
    (hx : f x ∈ V) :
    normalComponentToClopenModel f x V hV hx ≫ V.ι = (normalComponentOpen x).ι ≫ f :=
  IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry.Scheme
