/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Correspondences.Category.Objects
public import Colib.AlgebraicGeometry.Correspondences.Composition.Associativity
public import Colib.AlgebraicGeometry.Correspondences.Graph.IdentitySum
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The category of actual finite correspondences

Objects are the existing smooth separated finite-type schemes over an arbitrary field,
wrapped only to distinguish the correspondence category from the ordinary smooth site.
Morphisms are the existing native signed finite-cycle subgroup. Identity is the full
componentwise diagonal graph, and composition is the actual incidence Tor pairing.
The proved geometric unit and associativity laws supply the category axioms. Native
additive groups and the actual pairing's biadditivity supply the preadditive structure.

This construction allows empty and disconnected objects, with no integrality or
perfect-field hypothesis. Finite type supplies the compactness needed for finite
identity support; no caller must provide that support or any categorical law.

Implementation provenance: `motivic_source_a6805c4`,
`Motivic/AlgebraicGeometry/Correspondences/Basic.lean`, blob
`f09b33fa79079e5ffa6f4772563f3d27f4085e4f`. Mathematical convention: MVW (2006),
Lecture 1, printed pp. 4-6, the additive category of finite correspondences.
-/

@[expose] public noncomputable section

open CategoryTheory Stacks.Chow TopologicalSpace

universe u

namespace AlgebraicGeometry.Cor

variable (k : Type u) [Field k]

/-- The finite-type object has finitely many actual generic points for its identity graph. -/
theorem finite_genericPoints (X : Cor k) : (genericPoints X.toSmoothSite.left).Finite :=
  finite_genericPoints_of_smooth_of_compact X.toSmoothSite.hom

/-- The category with actual signed finite cycles and the actual incidence Tor composition. -/
@[colib_ref "motivic_source_a6805c4"
  "Motivic/AlgebraicGeometry/Correspondences/Basic.lean: Cor.category"
  "adaptation" "native signed cycles, full diagonal identity and actual incidence Tor pairing",
  colib_ref "MVW2006" "Lecture 1, printed pp. 4-6, finite-correspondence category"
  "adaptation" "arbitrary fields and all smooth separated finite-type objects",
  colib_tag "COL-0354"]
instance category : Category.{u} (Cor k) where
  Hom X Y := finiteCorrespondences X.toSmoothSite.hom Y.toSmoothSite.hom
  id X := graphCorrespondenceOfComponents X.toSmoothSite.hom X.toSmoothSite.hom
    (𝟙 X.toSmoothSite.left) (Category.id_comp _)
    (finite_genericPoints k X)
  comp {X Y Z} α β :=
    incidenceTorPairing X.toSmoothSite.hom Y.toSmoothSite.hom Z.toSmoothSite.hom α β
  id_comp {X Y} α := incidenceTorPairing_graphIdentity_left
    X.toSmoothSite.hom Y.toSmoothSite.hom
    (finite_genericPoints k X) α
  comp_id {X Y} α := incidenceTorPairing_graphIdentity_right
    X.toSmoothSite.hom Y.toSmoothSite.hom
    (finite_genericPoints k Y) α
  assoc {X Y Z W} α β γ := incidenceTorPairing_assoc k
    X.toSmoothSite.hom Y.toSmoothSite.hom Z.toSmoothSite.hom W.toSmoothSite.hom α β γ

/-- The existing additive cycle groups and biadditivity make the actual category preadditive. -/
@[colib_tag "COL-0354"]
instance preadditive : Preadditive (Cor k) where
  homGroup X Y := inferInstanceAs
    (AddCommGroup (finiteCorrespondences X.toSmoothSite.hom Y.toSmoothSite.hom))
  add_comp X Y Z α α' β := incidenceTorPairing_add_left
    X.toSmoothSite.hom Y.toSmoothSite.hom Z.toSmoothSite.hom α α' β
  comp_add X Y Z α β β' := incidenceTorPairing_add_right
    X.toSmoothSite.hom Y.toSmoothSite.hom Z.toSmoothSite.hom α β β'

end AlgebraicGeometry.Cor
