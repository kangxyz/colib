/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.Hypercohomology
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleChangeOfTopology
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedChangeOfTopology

/-!
# Genuine derived comparison for finite motivic cohomology

The source is the existing finite motivic cohomology, not a replacement group.
The target is derived-Hom into the actual degreewise étale sheafification of
its finite cone. This construction makes no claim that the comparison is an
isomorphism or that its target has already been identified with a Tate sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.FreeYonedaUnivLE

universe w w' u

namespace AlgebraicGeometry.PresheafWithTransfers
open _root_.AlgebraicGeometry.Scheme

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

/-- Actual étale finite motivic hypercohomology, with the original mapped cone as target. -/
abbrev motivicFiniteEtaleCohomology (p : ℤ) (q n : ℕ)
    (X : SmoothSite (Spec (.of k))) : Type w' :=
  ((DerivedCategory.singleFunctor _ 0).obj
    ((freeYoneda.{u + 1} (SmoothSite.etaleTopology (Spec (.of k)))).obj X) ⟶
      (DerivedCategory.Q.obj (motivicFiniteEtaleSheafComplex k q n))⟦p⟧)

/-- The exact derived comparison out of the existing finite motivic cohomology groups. -/
@[colib_tag "COL-1228",
  colib_ref "mathlib_stable_localization_pin"
    "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean" "ingredient"
    "Exact change-of-topology functor and native shift/single comparisons; no cohomology iso"]
def motivicFiniteEtaleCohomologyComparison (p : ℤ) (q n : ℕ)
    (X : SmoothSite (Spec (.of k))) :
    motivicFiniteCohomology k p q n X →+ motivicFiniteEtaleCohomology k p q n X :=
  SmoothSite.nisnevichToEtaleDerivedHomMap (Spec (.of k)) X
    (motivicFiniteSheafComplex k q n) p

end AlgebraicGeometry.PresheafWithTransfers
