/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Colib.AlgebraicGeometry.KTheory.ProjectiveLine.FlasqueResolution
public import Colib.KTheory.Waldhausen.Functoriality

/-! # The K-map equivalence of the actual flasque resolution -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.FlasquePerfect

universe u

/-- Inclusion after original totalization induces the identity native K-map. -/
theorem inclusion_comp_total_KMap (X : Scheme.{u}) (n : ℕ) :
    (Waldhausen.KMap (inclusion_exact X) n).comp (Waldhausen.KMap (total_exact X) n) =
      MonoidHom.id ((BoundedBelowPerfect.waldhausen X).K n) := by
  calc
    _ = Waldhausen.KMap ((total_exact X).comp (inclusion_exact X)) n :=
      Waldhausen.KMap_comp_KMap (total_exact X) (inclusion_exact X) n
    _ = Waldhausen.KMap
        (Waldhausen.IsExact.id (BoundedBelowPerfect.waldhausen X).cof
          (BoundedBelowPerfect.waldhausen X).weq) n :=
      (Waldhausen.KMap_eq_of_weakNatTrans
        (Waldhausen.IsExact.id (BoundedBelowPerfect.waldhausen X).cof
          (BoundedBelowPerfect.waldhausen X).weq)
        ((total_exact X).comp (inclusion_exact X)) (unit X) (unit_weak X) n).symm
    _ = _ := Waldhausen.KMap_id (BoundedBelowPerfect.waldhausen X) n

/-- Original totalization after inclusion induces the identity native K-map. -/
theorem total_comp_inclusion_KMap (X : Scheme.{u}) (n : ℕ) :
    (Waldhausen.KMap (total_exact X) n).comp (Waldhausen.KMap (inclusion_exact X) n) =
      MonoidHom.id ((waldhausen X).K n) := by
  calc
    _ = Waldhausen.KMap ((inclusion_exact X).comp (total_exact X)) n :=
      Waldhausen.KMap_comp_KMap (inclusion_exact X) (total_exact X) n
    _ = Waldhausen.KMap (Waldhausen.IsExact.id (waldhausen X).cof (waldhausen X).weq) n :=
      (Waldhausen.KMap_eq_of_weakNatTrans
        (Waldhausen.IsExact.id (waldhausen X).cof (waldhausen X).weq)
        ((inclusion_exact X).comp (total_exact X)) (flasqueUnit X) (flasqueUnit_weak X) n).symm
    _ = _ := Waldhausen.KMap_id (waldhausen X) n

/-- The inverse on original K-groups is supplied by the actual Godement total map. -/
theorem total_KMap_leftInverse (X : Scheme.{u}) (n : ℕ) :
    Function.LeftInverse (Waldhausen.KMap (total_exact X) n)
      (Waldhausen.KMap (inclusion_exact X) n) :=
  fun x => DFunLike.congr_fun (total_comp_inclusion_KMap X n) x

/-- The other inverse law follows from the actual source-model augmentation. -/
theorem total_KMap_rightInverse (X : Scheme.{u}) (n : ℕ) :
    Function.RightInverse (Waldhausen.KMap (total_exact X) n)
      (Waldhausen.KMap (inclusion_exact X) n) :=
  fun x => DFunLike.congr_fun (inclusion_comp_total_KMap X n) x

/-- The actual original full inclusion induces a bijection in every natural degree. -/
theorem inclusion_KMap_bijective (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (inclusion_exact X) n) :=
  ⟨(total_KMap_leftInverse X n).injective, (total_KMap_rightInverse X n).surjective⟩

/-- The literal inclusion into the unchanged native perfect category. -/
def perfectInclusion (X : Scheme.{u}) :
    Obj X ⥤ ObjectProperty.FullSubcategory
      (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) :=
  inclusion X ⋙ BoundedBelowPerfect.inclusion X

/-- This same literal composite inclusion is Waldhausen-exact. -/
lemma perfectInclusion_exact (X : Scheme.{u}) : Waldhausen.IsExact
    (waldhausen X).cof (waldhausen X).weq
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
    (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq (perfectInclusion X) :=
  (inclusion_exact X).comp (BoundedBelowPerfect.inclusion_exact X)

/-- The K-map is the composite of the two actual original inclusion K-maps. -/
theorem perfectInclusion_KMap_eq (X : Scheme.{u}) (n : ℕ) :
    Waldhausen.KMap (perfectInclusion_exact X) n =
      (Waldhausen.KMap (BoundedBelowPerfect.inclusion_exact X) n).comp
        (Waldhausen.KMap (inclusion_exact X) n) :=
  (Waldhausen.KMap_comp_KMap (inclusion_exact X) (BoundedBelowPerfect.inclusion_exact X) n).symm

/-- On a compact scheme the unchanged original flasque-perfect inclusion induces
an isomorphism on native K-groups, including degree zero. -/
theorem perfectInclusion_KMap_bijective (X : Scheme.{u}) [CompactSpace X] (n : ℕ) :
    Function.Bijective (Waldhausen.KMap (perfectInclusion_exact X) n) := by
  rw [perfectInclusion_KMap_eq]
  exact (BoundedBelowPerfect.inclusion_KMap_bijective X n).comp (inclusion_KMap_bijective X n)

end AlgebraicGeometry.Scheme.Modules.FlasquePerfect

attribute [colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/FlasqueBoundedBelowComparison.lean:38-95"
  "adaptation" "Literal inclusion and the actual Godement total have inverse K-maps"]
  AlgebraicGeometry.Scheme.Modules.FlasquePerfect.perfectInclusion_KMap_bijective
