/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.RingTheory.KTheory.Plus.ProjectiveGroupCompletion
public import Colib.CategoryTheory.GroupCompletion.ConnectedComponents

/-!
# Components of projective completion and the original Grothendieck group

The actual grading of a pair `(A, B)` is `[B] - [A]`. Its inverse is induced by
unit-entry components and the proved splitting of every finite-projective
conflation. Both inverse identities are proved on the original generators.

The group on components is induced by tensoring pairs and switching their
coordinates; it is not transported from the Grothendieck group. No cancellation,
rank formula, plus construction or additional splitting hypothesis is used.
-/

@[expose] public noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open GroupCompletion.Localization

namespace ModuleCat.FiniteProjective

variable (R : Type u) [Ring R]
attribute [local instance] categoryDirectSumMonoidal categoryDirectSumSymmetric
  directSumMonoidal directSumSymmetric hasBinaryBiproducts_of_finite_biproducts

/-- The native categorical components use the actual direct-sum completion group structure. -/
instance completionComponentsAddCommGroup :
    AddCommGroup (ConnectedComponents (GroupCompletionCategory R)) :=
  inferInstanceAs (AddCommGroup (Components (IsoCategory R)))

/-- The original grading descends to a homomorphism on native categorical components. -/
def completionComponentGrade :
    ConnectedComponents (GroupCompletionCategory R) →+ (exactStructure R).GrothendieckGroup where
  toFun := ConnectedComponents.liftFunctor _ (completionGrading R)
  map_zero' := by
    change coreClass R (𝟙_ (IsoCategory R)) - coreClass R (𝟙_ (IsoCategory R)) = 0
    exact sub_self _
  map_add' x y := by
    induction x using Quotient.inductionOn with
    | h X =>
      induction y using Quotient.inductionOn with
      | h Y =>
        change coreClass R (X.obj.2 ⊗ Y.obj.2) - coreClass R (X.obj.1 ⊗ Y.obj.1) =
          (coreClass R X.obj.2 - coreClass R X.obj.1) +
            (coreClass R Y.obj.2 - coreClass R Y.obj.1)
        rw [coreClass_tensor, coreClass_tensor]
        abel

/-- The component map has exactly the original numerator-minus-denominator value. -/
@[simp] theorem completionComponentGrade_mk (X : GroupCompletionCategory R) :
    completionComponentGrade R (ConnectedComponents.mk X) = completionGrade R X := rfl

/-- An actual finite-projective conflation gives the direct-sum relation on components. -/
theorem componentUnitClass_additive
    (K : ShortComplex (Category.{u, u} R)) (hK : (exactStructure R).conflation K) :
    componentUnitClass (⟨K.X₂⟩ : IsoCategory R) =
      componentUnitClass (⟨K.X₁⟩ : IsoCategory R) +
        componentUnitClass (⟨K.X₃⟩ : IsoCategory R) := by
  let e : (⟨K.X₂⟩ : IsoCategory R) ≅ ⟨K.X₁⟩ ⊗ ⟨K.X₃⟩ :=
    Core.isoMk ((splittingOfConflation R K hK).isoBinaryBiproduct ≪≫
      biprod.isoCoprod K.X₁ K.X₃)
  exact (componentUnitClass_iso e).trans (componentUnitClass_tensor _ _)

/-- The inverse homomorphism uses the original conflation presentation of K₀. -/
def grothendieckToCompletionComponents :
    (exactStructure R).GrothendieckGroup →+
      ConnectedComponents (GroupCompletionCategory R) :=
  (exactStructure R).grothendieckLift
    (fun P ↦ componentUnitClass (⟨P⟩ : IsoCategory R))
    (componentUnitClass_additive R)

/-- An original projective object class maps to its actual unit-entry component. -/
@[simp] theorem grothendieckToCompletionComponents_class (P : Category.{u, u} R) :
    grothendieckToCompletionComponents R ((exactStructure R).grothendieckClass P) =
      componentUnitClass (⟨P⟩ : IsoCategory R) :=
  (exactStructure R).grothendieckLift_class _ _ P

/-- Grading after the actual unit-entry lift fixes every original Grothendieck class. -/
theorem completionComponentGrade_comp_grothendieckToCompletionComponents :
    (completionComponentGrade R).comp (grothendieckToCompletionComponents R) =
      AddMonoidHom.id _ := by
  apply (exactStructure R).grothendieck_hom_ext
  intro P
  change completionComponentGrade R
    (grothendieckToCompletionComponents R ((exactStructure R).grothendieckClass P)) = _
  rw [grothendieckToCompletionComponents_class]
  change coreClass R ⟨P⟩ - coreClass R (𝟙_ (IsoCategory R)) =
    (exactStructure R).grothendieckClass P
  rw [coreClass_unit, sub_zero]
  rfl

/-- The denominator arrow proves the other inverse identity on every original pair. -/
theorem grothendieckToCompletionComponents_comp_completionComponentGrade :
    (grothendieckToCompletionComponents R).comp (completionComponentGrade R) =
      AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  induction x using Quotient.inductionOn with
  | h X =>
    change grothendieckToCompletionComponents R
      (coreClass R X.obj.2 - coreClass R X.obj.1) = ConnectedComponents.mk X
    rw [map_sub]
    change grothendieckToCompletionComponents R
      ((exactStructure R).grothendieckClass X.obj.2.of) -
        grothendieckToCompletionComponents R
          ((exactStructure R).grothendieckClass X.obj.1.of) = _
    rw [grothendieckToCompletionComponents_class, grothendieckToCompletionComponents_class]
    exact (componentClass_pair_eq_sub X.obj.1 X.obj.2).symm

/-- Native categorical components of projective completion are the original exact K₀. -/
def completionComponentsGrothendieckEquiv :
    ConnectedComponents (GroupCompletionCategory R) ≃+ (exactStructure R).GrothendieckGroup where
  toFun := completionComponentGrade R
  invFun := grothendieckToCompletionComponents R
  left_inv x := DFunLike.congr_fun
    (grothendieckToCompletionComponents_comp_completionComponentGrade R) x
  right_inv x := DFunLike.congr_fun
    (completionComponentGrade_comp_grothendieckToCompletionComponents R) x
  map_add' := map_add (completionComponentGrade R)

/-- The equivalence keeps the original sign on every actual pair. -/
@[simp] theorem completionComponentsGrothendieckEquiv_pair (A B : IsoCategory R) :
    completionComponentsGrothendieckEquiv R (ConnectedComponents.mk (completionPair R A B)) =
      coreClass R B - coreClass R A := rfl

/-- The inverse of the equivalence keeps the original projective object generator. -/
@[simp] theorem completionComponentsGrothendieckEquiv_symm_class (P : Category.{u, u} R) :
    (completionComponentsGrothendieckEquiv R).symm
      ((exactStructure R).grothendieckClass P) =
        ConnectedComponents.mk ((completionUnit R).obj ⟨P⟩) :=
  grothendieckToCompletionComponents_class R P

/-- Equality of actual virtual classes is precisely a zigzag in projective completion. -/
theorem completionGrade_eq_iff_zigzag (X Y : GroupCompletionCategory R) :
    completionGrade R X = completionGrade R Y ↔ Zigzag X Y := by
  change completionComponentsGrothendieckEquiv R (ConnectedComponents.mk X) =
    completionComponentsGrothendieckEquiv R (ConnectedComponents.mk Y) ↔ _
  rw [(completionComponentsGrothendieckEquiv R).injective.eq_iff]
  exact Quotient.eq

end ModuleCat.FiniteProjective

attribute [colib_tag "COL-0378",
  colib_ref "WeibelKBook" "IV, Lemma 4.3.1" "adaptation"
    "Actual categorical component group; denominator first gives $[B]-[A]$",
  colib_ref "WeibelKBook" "II, Definition 7.1 and Examples 7.1.1-7.1.2" "comparison"
    "The original inherited exact structure and its proved projective conflation splittings"]
  ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv
  ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_pair
  ModuleCat.FiniteProjective.completionComponentsGrothendieckEquiv_symm_class
  ModuleCat.FiniteProjective.completionGrade_eq_iff_zigzag
