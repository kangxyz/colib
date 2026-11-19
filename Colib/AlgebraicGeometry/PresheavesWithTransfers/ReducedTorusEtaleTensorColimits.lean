/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleTensorMono
public import Colib.CategoryTheory.Limits.ReflectiveColimits
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-! # Right exactness of the ordinary smooth étale tensor

Colimit preservation is descended through the actual sheafification reflector.
The inclusion is not assumed to preserve colimits. This supplies the right
exactness input complementary to pointwise-flat mono preservation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

universe u v w

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

attribute [local instance] smoothEtaleIntegral_isMonoidal_W Sheaf.monoidalCategory

/-- Fixed-coefficient sheaf tensor preserves every available module-colimit shape. -/
theorem smoothEtaleIntegralTensorRight_preservesColimitsOfShape
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
    (J : Type v) [Category.{w} J] [HasColimitsOfShape J (ModuleCat.{u + 1} ℤ)] :
    PreservesColimitsOfShape J
      (tensorRight ((presheafToSheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
        (ModuleCat.{u + 1} ℤ)).obj P)) := by
  let a := presheafToSheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
    (ModuleCat.{u + 1} ℤ)
  let i := sheafToPresheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
    (ModuleCat.{u + 1} ℤ)
  let : PreservesColimitsOfShape J (tensorRight P) := by
    apply preservesColimitsOfShape_of_evaluation
    intro X
    change PreservesColimitsOfShape J
      (((evaluation _ (ModuleCat.{u + 1} ℤ)).obj X) ⋙ tensorRight (P.obj X))
    infer_instance
  let : PreservesColimitsOfShape J (a ⋙ tensorRight (a.obj P)) :=
    preservesColimitsOfShape_of_natIso (Functor.Monoidal.commTensorRight a P).symm
  exact preservesColimitsOfShape_of_reflector a i (tensorRight (a.obj P))
    (asIso (sheafificationAdjunction
      (SmoothSite.etaleTopology (Spec (CommRingCat.of k))) (ModuleCat.{u + 1} ℤ)).counit)

/-- In particular the ordinary sheaf tensor is right exact, without a flatness assumption. -/
theorem smoothEtaleIntegralTensorRight_preservesFiniteColimits
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) :
    PreservesFiniteColimits
      (tensorRight ((presheafToSheaf (SmoothSite.etaleTopology (Spec (CommRingCat.of k)))
        (ModuleCat.{u + 1} ℤ)).obj P)) :=
  ⟨fun J _ _ => smoothEtaleIntegralTensorRight_preservesColimitsOfShape k P J⟩

end AlgebraicGeometry.PresheafWithTransfers
