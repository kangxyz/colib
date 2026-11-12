/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare

/-! # Sheaf gluing detects extension across a whole-complement étale neighborhood -/
/-!
Adapted from `Motivic/Cohomology/A1/Boundary/Contraction/SheafKernel.lean` at
`motivic@a6805c4a87cdfd7717dd7a94039246a167f15380`,
blob `75b744079219177aba7abf51b6389b0cad4f971f`. The actual native cylinder, Laurent open,
whole closed fiber and original residue marking are retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}}

/-- A section on the original open complement which extends on a whole-complement
étale neighborhood already extends on the original scheme. This uses ordinary
sheaf descent, not a homotopy-invariance assertion for a cokernel. -/
theorem exists_extension_of_iso_complement_neighborhood
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq.f₃₄.left z)]
    (s : F.obj.obj (op sq.X₂)) (t : F.obj.obj (op sq.X₃))
    (h : F.obj.map sq.f₁₂.op s = F.obj.map sq.f₁₃.op t) :
    ∃ a : F.obj.obj (op sq.X₄),
      F.obj.map sq.f₂₄.op a = s ∧ F.obj.map sq.f₃₄.op a = t := by
  have H := (CategoryTheory.forget AddCommGrpCat.{u + 1}).map_isPullback
    (isPullback_op_map_of_iso_complement sq hpb z hcomp F)
  exact Types.exists_of_isPullback H s t h

end AlgebraicGeometry.Scheme.SmoothSite
