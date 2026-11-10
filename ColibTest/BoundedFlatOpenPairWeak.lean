/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Colib.AlgebraicGeometry.KTheory.BoundedFlatPerfectOpenPullback
import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-! The actual restricted weak class, with arbitrary maps on the empty open. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.RingedSpace

universe u
attribute [local instance] Abelian.hasFiniteBiproducts

example {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B)
    {K L : (boundedAboveFlatPerfectComplex B.right.toRingedSpace).FullSubcategory}
    (p : K ⟶ L)
    (hp : QuasiIso (((restrictFunctor B.hom).mapHomologicalComplex (.up ℤ)).map p.hom)) :
    (boundedAboveFlatPerfectOpenWaldhausen A.hom).weq
      ((boundedAboveFlatPerfectPullback f.right).map p) :=
  (boundedAboveFlatPerfectOpenPullback_isExact f).weak p hp

example (X : Scheme.{u})
    {K L : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory} (p : K ⟶ L) :
    (boundedAboveFlatPerfectOpenWaldhausen (⊥ : X.Opens).ι).weq p := by
  apply (boundedAboveFlatPerfectOpenWaldhausen_weq_iff _ p).2
  exact (SheafOfModules.quasiIso_iff_forall_stalk_quasiIso _ _).2 fun x => False.elim x.2

example (X : Scheme.{u})
    {K L : (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory} (p : K ⟶ L)
    (hp : ¬ QuasiIso p.hom) :
    (boundedAboveFlatPerfectOpenWaldhausen (⊥ : X.Opens).ι).weq p ∧
      ¬ (boundedAboveFlatPerfectWaldhausen X.toRingedSpace).weq p := by
  refine ⟨?_, hp⟩
  apply (boundedAboveFlatPerfectOpenWaldhausen_weq_iff _ p).2
  exact (SheafOfModules.quasiIso_iff_forall_stalk_quasiIso _ _).2 fun x => False.elim x.2

example {A B : Scheme.OpenPairs.{u}} (f : A ⟶ B)
    {K L : (boundedAboveFlatPerfectComplex B.right.toRingedSpace).FullSubcategory}
    (p : K ⟶ L) :
    ((boundedAboveFlatPerfectPullback f.right).map p).hom =
      (((Scheme.Modules.pullback f.right).mapHomologicalComplex (.up ℤ)).map p.hom) := rfl
