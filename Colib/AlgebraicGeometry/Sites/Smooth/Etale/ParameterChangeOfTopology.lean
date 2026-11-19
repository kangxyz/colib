/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ParameterContinuity
public import Colib.AlgebraicGeometry.Sites.Smooth.Etale.ChangeOfTopology
public import Colib.CategoryTheory.Sites.SheafifyContinuous

/-! # The canonical parameter comparison under change of topology

Changing from Nisnevich to étale sheaves does not automatically commute
isomorphically with parameter sections. This file constructs the actual natural
comparison map from the reindexed sheafification unit, without asserting invertibility.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (S : Scheme.{u}) (A : Type v) [Category.{w} A]
variable [HasWeakSheafify (etaleTopology S) A]

/-- The canonical comparison from change of topology of Nisnevich parameter
sections to étale parameter sections after change of topology. -/
def parameterNisnevichToEtaleComparison (T : SmoothSite S) :
    (Contraction.parameterProduct T).sheafPushforwardContinuous A
        (nisnevichTopology S) (nisnevichTopology S) ⋙ nisnevichToEtaleSheaf S A ⟶
    nisnevichToEtaleSheaf S A ⋙
      (Contraction.parameterProduct T).sheafPushforwardContinuous A
        (etaleTopology S) (etaleTopology S) where
  app P := ((Contraction.parameterProduct T).sheafifyReindexComparison
    (etaleTopology S) (etaleTopology S) A).app P.obj
  naturality _ _ f := ((Contraction.parameterProduct T).sheafifyReindexComparison
    (etaleTopology S) (etaleTopology S) A).naturality f.hom

/-- The parameter comparison extends the literal reindexed étale unit. -/
@[reassoc]
theorem toSheafify_parameterNisnevichToEtaleComparison (T : SmoothSite S)
    (P : Sheaf (nisnevichTopology S) A) :
    toSheafify (etaleTopology S) ((Contraction.parameterProduct T).op ⋙ P.obj) ≫
      ((parameterNisnevichToEtaleComparison S A T).app P).hom =
    Functor.whiskerLeft (Contraction.parameterProduct T).op
      (toSheafify (etaleTopology S) P.obj) :=
  (Contraction.parameterProduct T).toSheafify_sheafifyReindexComparison
    (etaleTopology S) (etaleTopology S) A P.obj

end AlgebraicGeometry.Scheme.SmoothSite
