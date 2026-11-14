/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleDerivedComparison
public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.DerivedRestrictionAtBase

/-!
# Actual finite motivic comparison on the full small etale site

Compose the original finite motivic derived comparison with exact full-small
restriction at the identity neighborhood. Both the source motivic cohomology and
the restricted finite cone are the actual previously defined objects. No Tate
identification, comparison isomorphism or ordinary Sheaf.H endpoint is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Stacks.Cohomology.FreeYonedaUnivLE

universe w w' w'' u

namespace AlgebraicGeometry.PresheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open EtaleSeparatedFiniteType

variable (k : Type u) [Field k]
variable [HasSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
variable [(Cor.nisnevichTopology k).HasSheafCompose
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [(Cor.nisnevichTopology k).PreservesSheafification
  (CategoryTheory.forget AddCommGrpCat.{u + 1})]
variable [HasSheafify (SmoothSite.nisnevichTopology (Spec (.of k)))
  AddCommGrpCat.{u + 1}]

variable [HasSheafify (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w'}
  (Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

variable (X : SmoothSite (Spec (.of k)))
variable [HasDerivedCategory.{w''} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The original etale finite motivic cone restricted to the actual full small site. -/
abbrev motivicFiniteFullSmallEtaleComplex (q n : ℕ) :=
  ((fullSmallEtaleRestrict X).mapHomologicalComplex (.up ℤ)).obj
    (motivicFiniteEtaleSheafComplex k q n)

/-- Full-small derived-Hom of the actual restricted finite cone at its terminal object. -/
abbrev motivicFiniteFullSmallEtaleCohomology (p : ℤ) (q n : ℕ) : Type w'' :=
  ((DerivedCategory.singleFunctor _ 0).obj
    ((freeYoneda.{u + 1} X.left.smallEtaleTopology).obj (Scheme.Etale.mk (𝟙 X.left))) ⟶
      (DerivedCategory.Q.obj (motivicFiniteFullSmallEtaleComplex k X q n))⟦p⟧)

/-- The original finite motivic comparison followed by actual full-small restriction. -/
@[colib_tag "COL-1228", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:39-132" "ingredient"
  "Native exact derived lifts and source comparisons; composed here for the actual finite cone"]
def motivicFiniteFullSmallEtaleCohomologyComparison (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomology k p q n X →+
      motivicFiniteFullSmallEtaleCohomology k X p q n :=
  (fullSmallDerivedHomMapAtBase X (motivicFiniteEtaleSheafComplex k q n) p).comp
    (motivicFiniteEtaleCohomologyComparison k p q n X)

end AlgebraicGeometry.PresheafWithTransfers
