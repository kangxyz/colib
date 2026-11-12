/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.ParameterCylinderCochains
public import Colib.CategoryTheory.Sites.Simplicial.ReducedHypercohomology

import Colib.Algebra.Homology.Embedding.MapExtend
import Colib.AlgebraicTopology.DoldKan.NormalizedMooreMap
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Sheafification of reduced presheaf cochains

Exact sheafification commutes with the native normalized Moore complex and
with the extension by zero into cochain degrees. The comparison is natural
for the actual maps of pointed simplicial presheaves.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicTopology

universe u v w

namespace CategoryTheory.PointedSimplicialPresheaf

variable (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{w}]

/-- The original reduced sheaf cochains are the degreewise sheafification
of the original reduced presheaf cochains. -/
@[no_expose]
def reducedCochainsSheafificationIso :
    reducedCochains.{w} C J ≅ reducedPresheafCochains.{w} C ⋙
      (presheafToSheaf J AddCommGrpCat.{w}).mapHomologicalComplex (.up ℤ) := by
  let F := presheafToSheaf J AddCommGrpCat.{w}
  let E := ComplexShape.embeddingUpIntLE 0
  let e := Functor.isoWhiskerLeft (reducedFreeAbelian.{w} C)
    (normalizedMooreComplexCompMapHomologicalComplexIso F).symm
  exact Functor.isoWhiskerRight e (E.extendFunctor _) ≪≫
    Functor.isoWhiskerLeft (reducedChains.{w} C) (E.mapExtendNatIso F).symm

end CategoryTheory.PointedSimplicialPresheaf
