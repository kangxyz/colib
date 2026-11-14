/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Modules.ZModSheafComplex

/-!
# Actual additive transport of coefficient complexes

This transports the actual torsion complex first, then reads
its uniquely determined coefficient action. It never lifts a derived abelian isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory

universe t s v u v' u'

namespace Stacks.Cohomology.ZModSheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (J : GrothendieckTopology C) (J' : GrothendieckTopology D)
variable (F : Sheaf J AddCommGrpCat.{t} ⥤ Sheaf J' AddCommGrpCat.{t}) [F.Additive]
variable (n : ℕ) (K : CochainComplex (Sheaf J AddCommGrpCat.{t}) ℤ)

/-- Additive transport retains the original termwise annihilation equation. -/
theorem transportedComplex_nsmul_id
    (hK : ∀ i, n • 𝟙 (K.X i) = 0) (i : ℤ) :
    n • 𝟙 (((F.mapHomologicalComplex (.up ℤ)).obj K).X i) = 0 := by
  change n • 𝟙 (F.obj (K.X i)) = 0
  simpa only [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] using
    congrArg F.map (hK i)

/-- Sectionwise torsion of the actual transported complex. -/
theorem transportedComplex_torsion
    (hK : ∀ i, n • 𝟙 (K.X i) = 0) (i : ℤ) :
    torsionSheafProperty J' n (((F.mapHomologicalComplex (.up ℤ)).obj K).X i) := by
  intro X x
  have h := congrArg
    (fun f => (((sheafToPresheaf _ AddCommGrpCat).map f).app X).hom x)
    (transportedComplex_nsmul_id J J' F n K hK i)
  rw [Functor.map_nsmul, CategoryTheory.Functor.map_id, Functor.map_zero] at h
  simpa using h

end Stacks.Cohomology.ZModSheaf
