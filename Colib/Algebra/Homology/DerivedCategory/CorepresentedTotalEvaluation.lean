/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import StacksFrontier.Homology.Ext.CorepresentedHomotopyComparison
public import StacksFrontier.Homology.Injectives.DerivedCategory.RightDerivedTriangulated

/-!
# Total derived evaluation of a corepresented functor

The original cohomology comparison on the homotopy category is invertible
on K-injective complexes. It therefore identifies total derived
cohomology with the actual shifted derived Hom.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

universe w w' v u g

namespace Stacks.Cohomology.Corepresented

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [IsGrothendieckAbelian.{g} A] [HasDerivedCategory.{w'} AddCommGrpCat.{v}]
  (T : A ⥤ AddCommGrpCat.{v}) [T.Additive] (Z : A) (e : preadditiveCoyoneda.obj (op Z) ≅ T)
  (R : DerivedCategory A ⥤ DerivedCategory AddCommGrpCat.{v})
  (α : T.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ R)
  [R.IsRightDerivedFunctor α (HomologicalComplex.quasiIso A (.up ℤ))]

/-- The actual shifted Hom out of the original single object. -/
abbrev totalCorepresentedDerivedHomFunctor (n : ℤ) :
    DerivedCategory A ⥤ AddCommGrpCat.{max v w} :=
  shiftFunctor (DerivedCategory A) n ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.singleFunctor A 0).obj Z)) ⋙
      AddCommGrpCat.uliftFunctor.{v, w}

/-- Cohomology of the actual total derived functor is the original shifted
derived Hom, naturally in the coefficient complex. -/
@[no_expose]
def totalCorepresentedHomologyNatIso (n : ℤ) :
    R ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{v} n ⋙
        AddCommGrpCat.uliftFunctor.{w, v} ≅
      totalCorepresentedDerivedHomFunctor Z n := by
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{v} n ⋙
    AddCommGrpCat.uliftFunctor.{w, v}
  let G := homotopyHomologyFunctor T n
  let q : HomotopyCategory A (.up ℤ) ⥤ DerivedCategory A := DerivedCategory.Qh
  let W := HomotopyCategory.quasiIso A (.up ℤ)
  let β := Stacks.Injectives.homotopyUnitOfComplexUnit T R α
  let γ : G ⟶ q ⋙ (R ⋙ H) := Functor.whiskerRight β H
  let M := totalCorepresentedDerivedHomFunctor Z n
  let δ : G ⟶ q ⋙ M := homotopyComparison T Z e n
  have hres := Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian A
  let : (R ⋙ H).IsRightDerivedFunctor γ W :=
    Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
      hres G (R ⋙ H) γ (fun I hI => by
        change IsIso (H.map (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj I)))
        let : IsIso (β.app ((HomotopyCategory.quotient A (.up ℤ)).obj I)) :=
          Stacks.Injectives.isIso_homotopyUnitOfComplexUnit_app_quotient T R α I hI
        infer_instance)
  let : M.IsRightDerivedFunctor δ W :=
    Stacks.Injectives.KInjectiveResolution.isRightDerivedFunctor_of_isIso_app_quotient_isKInjective
      hres G M δ (fun I hI => by
        let : I.IsKInjective := hI
        exact inferInstanceAs (IsIso ((homotopyComparison T Z e n).app
          ((HomotopyCategory.quotient A (.up ℤ)).obj I))))
  exact Functor.rightDerivedUnique (R ⋙ H) M γ δ W

/-- On each object the total derived identification is an additive
equivalence, with the universe lift removed. -/
def totalCorepresentedHomologyAddEquiv (n : ℤ) (K : DerivedCategory A) :
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} n).obj (R.obj K)) ≃+
      ((DerivedCategory.singleFunctor A 0).obj Z ⟶ K⟦n⟧) :=
  AddEquiv.ulift.symm.trans
    ((((totalCorepresentedHomologyNatIso T Z e R α n).app K).addCommGroupIsoToAddEquiv).trans
      AddEquiv.ulift)

/-- The identification carries the original coefficient map to shifted
postcomposition. -/
theorem totalCorepresentedHomologyAddEquiv_naturality (n : ℤ)
    {K L : DerivedCategory A} (f : K ⟶ L)
    (x : (DerivedCategory.homologyFunctor AddCommGrpCat.{v} n).obj (R.obj K)) :
    totalCorepresentedHomologyAddEquiv T Z e R α n L
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} n).map (R.map f) x) =
      totalCorepresentedHomologyAddEquiv T Z e R α n K x ≫ f⟦n⟧' :=
  congrArg ULift.down <| ConcreteCategory.congr_hom
    ((totalCorepresentedHomologyNatIso T Z e R α n).hom.naturality f) (ULift.up x)

end Stacks.Cohomology.Corepresented
