/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Topology.DeformationRetract.Basic
public import Colib.Topology.Realization.FiniteCompact

/-!
# Finite support for a realized deformation retraction

On each finite target subcomplex, the actual retraction and the entire
deformation have finite simplicial support. This gives the compact witness
used in the bounded cofibration argument of Jardine, *Simplicial presheaves*,
Lemma 2.4, pp. 65–66. https://doi.org/10.1016/0022-4049(87)90100-9
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Topology
open scoped Simplicial

universe u

namespace SSet

/-- The prescribed retraction and homotopy on a finite subcomplex both
factor through finite subcomplexes, retaining their original values. -/
theorem finiteSubcomplex_deformationRetract_support {X Y : SSet.{u}} {f : X ⟶ Y}
    (R : TopCat.CylinderStrongDeformationRetract (SSet.toTop.map f))
    (A : Y.Subcomplex) [SSet.Finite A] :
    ∃ B : X.Subcomplex, SSet.Finite B ∧
      ∃ D : Y.Subcomplex, SSet.Finite D ∧
        ∃ (r : SSet.toTop.obj A ⟶ SSet.toTop.obj B)
          (H : SSet.toTop.obj A ⊗ TopCat.I ⟶ SSet.toTop.obj D),
          r ≫ SSet.toTop.map B.ι = SSet.toTop.map A.ι ≫ R.r ∧
            H ≫ SSet.toTop.map D.ι = (SSet.toTop.map A.ι ▷ TopCat.I) ≫ R.H := by
  let r₀ := SSet.toTop.map A.ι ≫ R.r
  let H₀ := (SSet.toTop.map A.ι ▷ TopCat.I) ≫ R.H
  let : CompactSpace (SSet.toTop.obj A) := realizationFinite_compactSpace A
  let : CompactSpace (↑TopCat.I.{u}) := TopCat.I.homeomorph.symm.compactSpace
  let : CompactSpace (↑(SSet.toTop.obj A ⊗ TopCat.I.{u})) := inferInstanceAs
    (CompactSpace (↑(SSet.toTop.obj A) × ↑TopCat.I.{u}))
  obtain ⟨B, hB, r, hr⟩ := realization_continuousMap_factors_finiteSubcomplex r₀.hom
  obtain ⟨D, hD, H, hH⟩ := realization_continuousMap_factors_finiteSubcomplex H₀.hom
  exact ⟨B, hB, D, hD, TopCat.ofHom r, TopCat.ofHom H,
    congrArg TopCat.ofHom hr, congrArg TopCat.ofHom hH⟩

end SSet
