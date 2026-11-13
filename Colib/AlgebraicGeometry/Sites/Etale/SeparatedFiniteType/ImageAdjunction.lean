/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Nisnevich
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Functor.Flat

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/Sites/Etale/SeparatedFiniteType/Boundary/Cokernel.lean`,
blob `f1f4e3f99cf84b82951ebb24c1f1648b1197fe3e`.

 # The actual small-Nisnevich inverse/direct-image adjunction

The closed inverse image is the left adjoint induced by actual base change of
finite-type separated étale neighborhoods. In particular it is not restriction
along the closed map in the big smooth slice.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType

variable {S T : Scheme.{u}}

/-- Direct image along the actual base-change functor of the small Nisnevich sites. -/
def directImage (b : T ⟶ S) :
    Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1} ⥤
      Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1} :=
  (baseChange b).sheafPushforwardContinuous _ _ _

/-- Genuine inverse image: the left adjoint, constructed from left Kan extension
and sheafification, rather than naive precomposition along a closed immersion. -/
def inverseImage (b : T ⟶ S) :
    Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (nisnevichTopology T) AddCommGrpCat.{u + 1} :=
  (baseChange b).sheafPullback _ _ _

/-- The actual inverse/direct-image adjunction. -/
def imageAdjunction (b : T ⟶ S) : inverseImage b ⊣ directImage b :=
  (baseChange b).sheafAdjunctionContinuous _ _ _


/-- The actual base-change functor is representably flat. -/
instance baseChange_representablyFlat (b : T ⟶ S) : RepresentablyFlat (baseChange b) :=
  flat_of_preservesFiniteLimits _

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
