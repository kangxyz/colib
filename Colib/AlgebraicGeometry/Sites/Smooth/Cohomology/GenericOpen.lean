/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Cohomology.LocalTriviality
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Colib.AlgebraicGeometry.Sites.Smooth.Injectives
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Colib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FieldPoints
public import Mathlib.AlgebraicGeometry.FunctionField

/-! # Positive ordinary classes vanish on an actual generic open

A Nisnevich covering sieve contains an open neighborhood of the generic point
of an integral model: its residue-field lift spreads out. This uses no claim
that a function-field spectrum is a finite-type object of the smooth site.
-/
/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Cohomology/GenericOpen.lean`, blob
`fd6e2e5d6f35ef7af2b9db1dcfb77748f2b0ed8a`.
The source is the actual original scheme or ordinary free-Yoneda Ext group.
All monic quotient fibers retain their full scheme structure.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe w u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} [IsNoetherian S]

/-- All actual opens of a noetherian smooth model remain smooth finite-type objects. -/
def opensFunctor (X : SmoothSite S) : X.left.Opens ⥤ SmoothSite S where
  obj U := mk (U.ι ≫ X.hom)
  map f := homMk (X.left.homOfLE f.le) (by simp)
  map_id U := by
    apply MorphismProperty.Over.Hom.ext
    exact Scheme.homOfLE_rfl _ _
  map_comp f g := by
    apply MorphismProperty.Over.Hom.ext
    exact (X.left.homOfLE_homOfLE f.le g.le).symm

/-- The original inclusion of an open into its model. -/
def openInclusion (X : SmoothSite S) (U : X.left.Opens) :
    (opensFunctor X).obj U ⟶ X := homMk U.ι rfl

/-- Every Nisnevich covering sieve of an integral model contains a generic open. -/
theorem exists_generic_open_mem_covering_sieve (X : SmoothSite S) [IsIntegral X.left]
    (R : Sieve X) (hR : R ∈ nisnevichTopology S X) :
    ∃ (W : X.left.Opens), genericPoint X.left ∈ W ∧ R (openInclusion X W) := by
  obtain ⟨P, hP, hPR⟩ := mem_nisnevichTopology_iff.mp hR
  obtain ⟨ι, U, p, rfl⟩ := P.exists_eq_ofArrows
  have hp' : Presieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (p i).left) ∈
      Nisnevich.precoverage X.left := by
    have h := mem_nisnevichPrecoverage_iff.mp hP
    rw [Presieve.map_ofArrows] at h
    exact h
  obtain ⟨_, _, ⟨i⟩, g, hg⟩ := Nisnevich.exists_lift_of_field_point hp'
    X.left.functionField (X.left.fromSpecStalk (genericPoint X.left))
  have : Etale (p i).left :=
    (ofArrows_mem_nisnevichPrecoverage_iff p).mp hP |>.1 i
  obtain ⟨W, hηW, t, _, ht⟩ := spread_out_of_isGermInjective' (𝟙 X.left)
    (p i).left g (by simpa using hg)
  let b : (opensFunctor X).obj W ⟶ U i := homMk t (by
    change t ≫ (U i).hom = W.ι ≫ X.hom
    rw [← MorphismProperty.Over.w (p i), ← Category.assoc, ht, Category.comp_id])
  have hb : b ≫ p i = openInclusion X W := by
    apply MorphismProperty.Over.Hom.ext
    change t ≫ (p i).left = W.ι
    simpa using ht
  refine ⟨W, hηW, ?_⟩
  rw [← hb]
  exact R.downward_closed (hPR _ _ (Presieve.ofArrows.mk i)) b

end AlgebraicGeometry.Scheme.SmoothSite

namespace Stacks.Cohomology.FreeYonedaUnivLE
open _root_.AlgebraicGeometry.Scheme
variable {S : Scheme.{u}} [IsNoetherian S]
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})]

/-- A positive original ordinary cohomology class vanishes after restricting to a
constructed generic open. No homotopy invariance or field continuity is used. -/
theorem exists_generic_open_restriction_eq_zero
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{u + 1})
    (n : ℕ) (X : SmoothSite S) [IsIntegral X.left]
    (e : (cohomologyPresheaf.{w, u + 1} F (n + 1)).obj (op X)) :
    ∃ (W : X.left.Opens), genericPoint X.left ∈ W ∧
      (cohomologyPresheaf.{w, u + 1} F (n + 1)).map
        (SmoothSite.openInclusion X W).op e = 0 := by
  obtain ⟨W, hW, he⟩ := SmoothSite.exists_generic_open_mem_covering_sieve X _
    (zeroSieve_mem_succ (SmoothSite.nisnevichTopology S) F n X e)
  exact ⟨W, hW, he.trans (map_zero _)⟩

end Stacks.Cohomology.FreeYonedaUnivLE
