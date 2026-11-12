/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.DifferenceSheafBoundary
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionRegular
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing

/-!
# Canonical evaluation on the entire empty-divisor boundary model

The original unit ideal has a unique section mapping to one. Tensoring that
section with the original positive canonical section gives coordinate one in
`differenceSheafTopIso` over every open of any scheme, including nonreduced schemes.
This is an equality of actual sheaf sections, not equality on geometric points.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace Stacks.Divisors

variable (X : Scheme.{u})

/-- Over every open, the unit ideal has a section whose inclusion is the function one. -/
theorem exists_idealSheafSection_top_eq_one (U : X.Opens) :
    ∃ b : (negativeTwist' (⊤ : X.IdealSheafData)).val.obj (op U),
      idealSheafSection (⊤ : X.IdealSheafData) b = (1 : Γ(X, U)) := by
  apply (subschemeι_app_eq_zero_iff_exists_idealSheafSection (⊤ : X.IdealSheafData) 1).mp
  exact Subsingleton.elim _ _

/-- The uniquely determined section one of the original unit ideal. -/
def unitIdealOneSection (U : X.Opens) :
    (negativeTwist' (⊤ : X.IdealSheafData)).val.obj (op U) :=
  (exists_idealSheafSection_top_eq_one X U).choose

/-- Its image is literally the function one, on the full open scheme. -/
@[simp]
theorem idealSheafSection_unitIdealOneSection (U : X.Opens) :
    idealSheafSection (⊤ : X.IdealSheafData) (unitIdealOneSection X U) = (1 : Γ(X, U)) :=
  (exists_idealSheafSection_top_eq_one X U).choose_spec

/-- The canonical empty-divisor tensor section has coordinate one under the exact
boundary evaluation frame. No reducedness or integrality hypothesis is imposed. -/
theorem differenceSheafTopIso_canonicalSection_tensor_unitIdealOneSection (U : X.Opens) :
    (differenceSheafTopIso X).hom.val.app (op U)
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        (invertibleSheaf' (⊤ : X.IdealSheafData)) (negativeTwist' (⊤ : X.IdealSheafData))
        ((canonicalSection' (⊤ : X.IdealSheafData)).eval (op U)) (unitIdealOneSection X U)) =
      (1 : Γ(X, U)) := by
  exact (Stacks.SheafOfModules.evaluation_tensorPt X.presheaf X.ringCatSheaf.property
    (negativeTwist' (⊤ : X.IdealSheafData)) (op U)
    ((canonicalSection' (⊤ : X.IdealSheafData)).eval (op U))
    (unitIdealOneSection X U)).trans (idealSheafSection_unitIdealOneSection X U)

/-- Any section of the original unit ideal with ambient value one gives the same
canonical tensor and the same exact boundary coordinate. -/
theorem differenceSheafTopIso_tensor_canonical_of_eq_one (U : X.Opens)
    (b : Γ(negativeTwist' (⊤ : X.IdealSheafData), U))
    (hb : idealSheafSection (⊤ : X.IdealSheafData) b = (1 : Γ(X, U))) :
    (differenceSheafTopIso X).hom.app U
      (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
        (invertibleSheaf' (⊤ : X.IdealSheafData)) (negativeTwist' (⊤ : X.IdealSheafData))
        ((canonicalSection' (⊤ : X.IdealSheafData)).eval (op U)) b) = (1 : Γ(X, U)) := by
  have h : b = unitIdealOneSection X U :=
    idealSheafSection_injective (⊤ : X.IdealSheafData)
      (hb.trans (idealSheafSection_unitIdealOneSection X U).symm)
  exact (congrArg (fun z => (differenceSheafTopIso X).hom.app U
    (Stacks.SheafOfModules.tensorSectionsAt X.sheaf.obj X.ringCatSheaf.property (op U)
      (invertibleSheaf' (⊤ : X.IdealSheafData)) (negativeTwist' (⊤ : X.IdealSheafData))
      ((canonicalSection' (⊤ : X.IdealSheafData)).eval (op U)) z)) h).trans
    (differenceSheafTopIso_canonicalSection_tensor_unitIdealOneSection X U)

end Stacks.Divisors
