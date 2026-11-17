/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Etale.Adjunction

/-!
# Local constancy on the smooth etale site

We use MVW Definition 6.7: extension of the restriction to the base field's
small etale site recovers the original sheaf via the canonical counit.
This definition concerns abelian-group sheaves, before adding transfers or
any torsion hypothesis. It imposes no finite-stalk condition.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable (k : Type u) [Field k]

/-- MVW local constancy for an abelian-group sheaf on the smooth etale site:
the canonical extension-restriction counit from the base field is invertible.
No finiteness, torsion, or transfer structure is part of this definition. -/
@[colib_tag "COL-1303", colib_ref "MVW2006"
  "Lecture 6, Definition 6.7, p. 38" "adaptation"
  "Counit criterion, using the equivalent full small etale site"]
def IsLocallyConstant
    (F : Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) : Prop :=
  IsIso ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app F)

/-- Unfolding local constancy recovers precisely the original rigidity counit condition. -/
theorem isLocallyConstant_iff_isIso_counit
    (F : Sheaf (SmoothSite.etaleTopology (Spec (.of k))) AddCommGrpCat.{u + 1}) :
    IsLocallyConstant k F ↔
      IsIso ((fullSmallEtaleAdjunction (SmoothSite.base (Spec (.of k)))).counit.app F) :=
  Iff.rfl

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
