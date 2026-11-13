/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.Algebra.Homology.DerivedCategory.KInjectiveAdjunction
public import Colib.Algebra.Homology.DerivedCategory.KInjectiveAdjunctionMap

/-! # Precomposition into the original K-injective targets -/

@[expose] public noncomputable section

open CategoryTheory

namespace CochainComplex.IsKInjective

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
  {K L J : CochainComplex C ℤ} [J.IsKInjective]

/-- The comparison into a K-injective target retains precomposition by an original chain map. -/
theorem localizedHomAddEquiv_precomp (f : L ⟶ K)
    (x : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj J) :
    localizedHomAddEquiv L J ((HomotopyCategory.quotient C (.up ℤ)).map f ≫ x) =
      DerivedCategory.Q.map f ≫ localizedHomAddEquiv K J x := by
  let Q := HomotopyCategory.quotient C (.up ℤ)
  obtain ⟨g, rfl⟩ := Q.map_surjective x
  change localizedHomAddEquiv L J (Q.map f ≫ Q.map g) =
    DerivedCategory.Q.map f ≫ localizedHomAddEquiv K J (Q.map g)
  rw [← Q.map_comp, localizedHomAddEquiv_map, localizedHomAddEquiv_map,
    CategoryTheory.Functor.map_comp]

/-- The inverse comparison preserves precomposition by the original localized map. -/
theorem localizedHomAddEquiv_symm_precomp (f : L ⟶ K)
    (x : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj J) :
    (localizedHomAddEquiv L J).symm (DerivedCategory.Q.map f ≫ x) =
      (HomotopyCategory.quotient C (.up ℤ)).map f ≫ (localizedHomAddEquiv K J).symm x := by
  apply (localizedHomAddEquiv L J).injective
  rw [AddEquiv.apply_symm_apply, localizedHomAddEquiv_precomp, AddEquiv.apply_symm_apply]

end CochainComplex.IsKInjective

namespace CategoryTheory.Adjunction

open CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (a : L ⊣ R)
  (I : CochainComplex D ℤ) [I.IsKInjective]
  [CochainComplex.IsKInjective ((R.mapHomologicalComplex (.up ℤ)).obj I)]

/-- The actual K-injective adjunction transpose is natural in the source complex. -/
theorem kInjectiveHomAddEquiv_symm_precomp {X Y : CochainComplex C ℤ} (f : X ⟶ Y)
    (g : DerivedCategory.Q.obj ((L.mapHomologicalComplex (.up ℤ)).obj Y) ⟶
      DerivedCategory.Q.obj I) :
    (a.kInjectiveHomAddEquiv X I).symm
        (DerivedCategory.Q.map ((L.mapHomologicalComplex (.up ℤ)).map f) ≫ g) =
      DerivedCategory.Q.map f ≫ (a.kInjectiveHomAddEquiv Y I).symm g := by
  let F := L.mapHomologicalComplex (.up ℤ)
  let D₀ := L.mapDerivedCategory
  let d := L.mapDerivedCategoryFactors
  let Q : CochainComplex C ℤ ⥤ DerivedCategory C := DerivedCategory.Q
  let Q' : CochainComplex D ℤ ⥤ DerivedCategory D := DerivedCategory.Q
  let K := (R.mapHomologicalComplex (.up ℤ)).obj I
  let u := (a.kInjectiveHomAddEquiv Y I).symm g
  let h := Q'.map ((a.counit.mapHomologicalComplex (.up ℤ)).app I)
  have hu : d.inv.app Y ≫ D₀.map u ≫ d.hom.app K ≫ h = g :=
    (a.kInjectiveHomAddEquiv_eq Y I u).symm.trans
      ((a.kInjectiveHomAddEquiv Y I).apply_symm_apply g)
  have hd : d.inv.app X ≫ D₀.map (Q.map f) = Q'.map (F.map f) ≫ d.inv.app Y :=
    (d.inv.naturality f).symm
  apply (a.kInjectiveHomAddEquiv X I).injective
  rw [AddEquiv.apply_symm_apply, a.kInjectiveHomAddEquiv_eq]
  change Q'.map (F.map f) ≫ g = d.inv.app X ≫ D₀.map (Q.map f ≫ u) ≫ d.hom.app K ≫ h
  symm
  calc
    _ = (d.inv.app X ≫ D₀.map (Q.map f)) ≫ D₀.map u ≫ d.hom.app K ≫ h := by
      rw [D₀.map_comp]
      simp only [Category.assoc]
    _ = (Q'.map (F.map f) ≫ d.inv.app Y) ≫ D₀.map u ≫ d.hom.app K ≫ h :=
      congrArg (fun z => z ≫ D₀.map u ≫ d.hom.app K ≫ h) hd
    _ = _ := (Category.assoc _ _ _).trans (congrArg (Q'.map (F.map f) ≫ ·) hu)

end CategoryTheory.Adjunction
