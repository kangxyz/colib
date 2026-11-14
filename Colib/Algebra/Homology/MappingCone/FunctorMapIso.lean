/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.MappingCone.ShortExact
public import Colib.Algebra.Homology.CochainComplex.SplitFactorization.AdditiveMap

/-! # Natural isomorphisms of signed mapping cones -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
universe u v u' v' w z

namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {B : Type u'} [Category.{v'} B] [Abelian B]
variable {D : Type w} [Category.{z} D]

/-- Applying an additive functor to the actual cone is natural on the coefficient category. -/
def mappingConeNatTransFunctorMapIso {F G : D ⥤ CochainComplex A ℤ}
    (α : F ⟶ G) (J : A ⥤ B) [J.Additive] :
    mappingConeNatTransFunctor α ⋙ J.mapHomologicalComplex (.up ℤ) ≅
      mappingConeNatTransFunctor (Functor.whiskerRight α (J.mapHomologicalComplex (.up ℤ))) :=
  NatIso.ofComponents (fun K => mappingCone.mapHomologicalComplexIso (α.app K) J)
    (fun f => SplitFactorization.coneMapIso_naturality J _ _ _ _ (α.naturality f).symm)

end CochainComplex
