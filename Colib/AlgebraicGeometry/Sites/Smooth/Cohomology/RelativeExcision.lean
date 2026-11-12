/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.RelativeCohomology.Excision
public import Colib.CategoryTheory.Sites.RelativeCohomology.BoundaryNaturality
public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare

/-!
# Relative excision on smooth sites
-/

/-!
Adapted from `kangxyz/motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
`Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Cohomology/RelativeExcision.lean`, blob
`e5fa6824a42eda360342768c97da3609a08b10f0`.
The actual ordinary free-Yoneda Ext groups, signed boundary and original
restriction arrows are retained. No positive-cohomology sheaf gluing or
whole-cylinder generic-base vanishing is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

universe w t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE
open _root_.AlgebraicGeometry.Scheme
section Nisnevich

variable {S : Scheme.{u}} [HasSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}]
  (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
  [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]

include hpb z hcomp

/-- Genuine Nisnevich excision of the actual relative source. -/
theorem isIso_relativeSourceMap_nisnevich :
    IsIso (relativeSourceMap (SmoothSite.nisnevichTopology S)
      sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm) :=
  isIso_relativeSourceFunctor_map_of_section_descent _ sq
    (SmoothSite.isPullback_op_map_of_iso_complement sq hpb z hcomp)

variable [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t})]

/-- Genuine Nisnevich excision in every relative cohomological degree. -/
theorem isIso_relativeRestriction_nisnevich
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ) :
    IsIso (relativeRestriction (SmoothSite.nisnevichTopology S)
      sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm F n) :=
  isIso_relativeCohomologyFunctor_map_of_section_descent _ sq
    (SmoothSite.isPullback_op_map_of_iso_complement sq hpb z hcomp) F n

/-- The actual restriction, packaged as the Nisnevich excision isomorphism. -/
def relativeNisnevichExcisionIso
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ) :
    relativeH (SmoothSite.nisnevichTopology S) sq.f₂₄ F n ≅
      relativeH (SmoothSite.nisnevichTopology S) sq.f₁₃ F n := by
  letI := isIso_relativeRestriction_nisnevich sq hpb z hcomp F n
  exact asIso (relativeRestriction (SmoothSite.nisnevichTopology S)
    sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm F n)

local instance : Mono sq.f₂₄ := (SmoothSite.forgetScheme S).mono_of_mono_map (by
  change Mono sq.f₂₄.left
  infer_instance)

/-- The excision isomorphism commutes with the standard signed boundary. -/
theorem relativeNisnevichExcisionIso_boundary
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ)
    (x : (cohomologyPresheaf.{w, t} F n).obj (op sq.X₂)) :
    letI : Mono sq.f₁₃ := hpb.mono_f₁₃
    (relativeNisnevichExcisionIso sq hpb z hcomp F (n + 1)).hom
        (relativeBoundary (SmoothSite.nisnevichTopology S) sq.f₂₄ F n x) =
      relativeBoundary (SmoothSite.nisnevichTopology S) sq.f₁₃ F n
        ((cohomologyPresheaf.{w, t} F n).map sq.f₁₂.op x) := by
  let : Mono sq.f₁₃ := hpb.mono_f₁₃
  exact relativeBoundary_restriction _ _ _ _ _ _ F n x

end Nisnevich

end Stacks.Cohomology.FreeYonedaUnivLE
