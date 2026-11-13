/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleDerivedComparison
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.DerivedNaturality

/-!
# Restriction compatibility on the original finite motivic groups

Both restrictions are the actual representing-source precomposition maps. The
comparison commutes with them as an equality on existing derived-Hom elements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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

/-- The actual etale finite motivic groups as an additive presheaf. -/
def motivicFiniteEtaleCohomologyPresheaf (p : ℤ) (q n : ℕ) :
    (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w'} :=
  hypercohomologyPresheaf.{w', u + 1}
    (SmoothSite.etaleTopology (Spec (.of k))) (motivicFiniteEtaleSheafComplex k q n) p

/-- Actual restriction in the etale finite motivic presheaf. -/
abbrev motivicFiniteEtaleCohomologyRestriction (p : ℤ) (q n : ℕ)
    {X Y : SmoothSite (Spec (.of k))} (g : X ⟶ Y) :
    AddCommGrpCat.of (motivicFiniteEtaleCohomology k p q n Y) ⟶
      AddCommGrpCat.of (motivicFiniteEtaleCohomology k p q n X) :=
  (motivicFiniteEtaleCohomologyPresheaf k p q n).map g.op

/-- The original finite motivic restriction commutes with the genuine derived comparison. -/
@[colib_tag "COL-1228", colib_ref "mathlib_stable_localization_pin"
  "Mathlib/Algebra/Homology/DerivedCategory/ExactFunctor.lean:39-132" "specialization"
  "Exact derived comparison on the existing finite motivic restriction maps"]
theorem motivicFiniteEtaleCohomologyComparison_restriction (p : ℤ) (q n : ℕ)
    {X Y : SmoothSite (Spec (.of k))} (g : X ⟶ Y)
    (a : motivicFiniteCohomology k p q n Y) :
    motivicFiniteEtaleCohomologyComparison k p q n X
        (motivicFiniteCohomologyRestriction k p q n g a) =
      motivicFiniteEtaleCohomologyRestriction k p q n g
        (motivicFiniteEtaleCohomologyComparison k p q n Y a) :=
  SmoothSite.nisnevichToEtaleDerivedHomMap_restriction
    (Spec (.of k)) g (motivicFiniteSheafComplex k q n) p a

end AlgebraicGeometry.PresheafWithTransfers
