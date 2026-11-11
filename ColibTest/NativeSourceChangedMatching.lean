/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Colib.AlgebraicGeometry.RelativeCurve.Pencils.SourceChangedMatching
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.RelativeCurvePencil
universe u
example {X X' Z Z' : Scheme.{u}} (g : X' ⟶ X) (i : Z ⟶ X)
    (i' : Z' ⟶ X') (β : Z' ⟶ Z) (h : i' ≫ g = β ≫ i)
    (M : X.Modules) (s : Γ(M, ⊤)) :
    (boundaryPullbackSquareIso g i i' β h M).hom.app ⊤
      (pullbackGlobalSections i' _ (pullbackGlobalSections g M s)) =
        pullbackGlobalSections β _ (pullbackGlobalSections i M s) :=
  boundaryPullbackSquareIso_section g i i' β h M s
#check graphPole_boundary_eq_coordinate_smul
#check boundary_smul_identity_after_sourceChange
#check boundary_tensor_matching_after_sourceChange
