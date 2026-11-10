/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Nisnevich.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# Global functions on the actual Nisnevich site

Nisnevich subcanonicity follows from the native pro-étale result. Testing global
functions by a commutative ring gives the presheaf represented by its spectrum,
so actual global functions form a ring-valued sheaf on the big Nisnevich site.

Extracted from `Motivic/Aglib/AlgebraicGeometry/Sites/Smooth/Units/Basic.lean`
at motivic commit `a6805c4a87cdfd7717dd7a94039246a167f15380`. This lower owner
does not depend on the smooth site, unit groups, or any transfer structure.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry

instance Nisnevich.subcanonical : Nisnevich.topology.{u}.Subcanonical :=
  .of_le (Nisnevich.topology_le_etaleTopology.trans Scheme.etaleTopology_le_proetaleTopology)

namespace Scheme

/-- Global functions tested by a ring are represented by its actual spectrum. -/
def globalFunctionsRepresentable (R : CommRingCat.{u}) :
    Scheme.Γ ⋙ coyoneda.obj (op R) ≅ yoneda.obj (Spec R) :=
  NatIso.ofComponents (fun X =>
    (Equiv.trans (CategoryTheory.opEquiv (op (Scheme.Γ.obj X)) (op R)).symm
      (ΓSpec.adjunction.homEquiv X.unop (op R))).toIso) (by
    intro X Y f
    ext g
    exact ΓSpec.adjunction.homEquiv_naturality_left f.unop g.op)

/-- Global functions satisfy Nisnevich descent as genuine ring-valued sections. -/
theorem globalFunctions_isSheaf : Presheaf.IsSheaf Nisnevich.topology Scheme.Γ := by
  intro R
  exact Presieve.isSheaf_iso Nisnevich.topology (globalFunctionsRepresentable R).symm
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _)

end Scheme

end AlgebraicGeometry
