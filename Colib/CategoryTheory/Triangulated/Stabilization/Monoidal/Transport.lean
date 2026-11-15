/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.CategoryTheory.Triangulated.Stabilization.ChangeFunctor
public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Powers
public import Colib.CategoryTheory.Triangulated.Stabilization.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Braided.Transport

/-!
# The stable tensor for an isomorphic transition

Transport the stable tensor to the original category of finite stages when
its transition is naturally isomorphic to tensoring with a fixed object.
The additive and triangulated structures retain their original carrier.
-/

@[expose] public noncomputable section

open CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

universe u v

namespace CategoryTheory.Stabilization

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  {T : C ⥤ C} [T.Full] [T.Faithful] (L : C)
  [(tensorRight L).Full] [(tensorRight L).Faithful]
  (e : tensorRight L ≅ T) (hL : (β_ L L).hom = 𝟙 _)

local notation "E" => changeEquivalence e

/-- The canonical stable tensor on the category of the selected endofunctor. -/
@[instance_reducible]
def transportedMonoidalCategory : MonoidalCategory (Stabilization T) :=
  letI := monoidalCategory L hL
  CategoryTheory.Monoidal.transport E

/-- Its braiding and symmetry are transported along the same equivalence. -/
@[instance_reducible]
def transportedSymmetricCategory :
    letI := transportedMonoidalCategory L e hL
    SymmetricCategory (Stabilization T) :=
  letI := monoidalCategory L hL
  letI := symmetricCategory L hL
  inferInstanceAs (SymmetricCategory (CategoryTheory.Monoidal.Transported E))

/-- The change of transition is braided monoidal for the transported structure. -/
@[instance_reducible]
def transportedChangeBraided :
    letI := monoidalCategory L hL
    letI := symmetricCategory L hL
    letI := transportedMonoidalCategory L e hL
    letI := transportedSymmetricCategory L e hL
    (changeFunctor e).Braided := by
  letI := monoidalCategory L hL
  letI := symmetricCategory L hL
  letI := transportedMonoidalCategory L e hL
  letI := transportedSymmetricCategory L e hL
  change (CategoryTheory.Monoidal.equivalenceTransported E).functor.Braided
  infer_instance

/-- The original denominator-zero inclusion is braided for the transported tensor. -/
@[instance_reducible]
def transportedInclusionBraided :
    letI := transportedMonoidalCategory L e hL
    letI := transportedSymmetricCategory L e hL
    (inclusion T).Braided :=
  letI := monoidalCategory L hL
  letI := symmetricCategory L hL
  letI := transportedMonoidalCategory L e hL
  letI := transportedSymmetricCategory L e hL
  letI := inclusionBraided L hL
  letI := transportedChangeBraided L e hL
  let i := inclusionChangeFunctorIso e
  letI := Functor.Monoidal.transport i
  letI := Functor.Monoidal.natTransIsMonoidal_of_transport i
  letI := Functor.LaxBraided.ofNatIso i
  { }

section Additive

variable [Preadditive C] [MonoidalPreadditive C] [T.Additive]

/-- The transported tensor remains additive in both arguments for the
original additive structure on stable Hom groups. -/
theorem transportedMonoidalPreadditive :
    letI := transportedMonoidalCategory L e hL
    MonoidalPreadditive (Stabilization T) :=
  letI := monoidalCategory L hL
  letI := monoidalPreadditive L hL
  letI := transportedMonoidalCategory L e hL
  let J := E
  let : J.functor.Additive := inferInstanceAs (changeFunctor e).Additive
  let : J.inverse.Monoidal :=
    (inferInstance : (CategoryTheory.Monoidal.equivalenceTransported E).inverse.Monoidal)
  monoidalPreadditive_of_faithful J.inverse

end Additive

end CategoryTheory.Stabilization
