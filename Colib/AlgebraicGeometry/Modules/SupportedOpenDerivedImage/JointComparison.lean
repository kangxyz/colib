/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Opposite
public import Colib.CategoryTheory.Waldhausen.Fibration.Rows.OppositeComplexJointMap

/-! # Coherent actual opposite cylinders under image corestriction

The canonical additive biproduct and identity-cone comparison transports through
actual opposite equivalences. All six endpoint equations are retained; independently
chosen cofibers are compared by this natural isomorphism, not by definitional equality.

Adapted from Quillen `AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/JointComparison.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen CategoryTheory.ExactCategory
open AlgebraicGeometry.RingedSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
universe u d

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j T)]

/-- The literal restriction intertwines the actual opposite joint-cylinder functors. -/
def corestrictJointIso :
    (perfectSupportedOppositeJointData T.ι).joint ⋙
      ExtensionCategory.postcompose (perfectSupportedOppositeWaldhausen T.ι)
        (oppositeWaldhausen j T)
        (corestrict_op_isExact j T) ≅
      (corestrict j T).op.mapArrow ⋙
        (oppositeJointData j T).joint :=
  oppositeComplexJointDataMapIso
    (C := X.Modules)
    (D := U.Modules) (restrictFunctor j)
    (perfectSupported T.ι) (complexObjects j T)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => perfectSupported_shift_of_quasiIso_zero T.ι h (-1))
    (fun _ h => complexObjects_shift j T h (-1))
    (corestrict_op_isExact j T)

variable (f : Arrow (ObjectProperty.FullSubcategory
  (perfectSupported T.ι))ᵒᵖ)

/-- The forward comparison retains the original first endpoint. -/
theorem corestrictJointIso_inl :
    (corestrict j T).op.map
        ((perfectSupportedOppositeJointData T.ι).inl.app f) ≫
      ((corestrictJointIso j T).hom.app f).hom.left =
    (oppositeJointData j T).inl.app
      ((corestrict j T).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inl
    (C := X.Modules)
    (D := U.Modules) (restrictFunctor j)
    (perfectSupported T.ι) (complexObjects j T)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => perfectSupported_shift_of_quasiIso_zero T.ι h (-1))
    (fun _ h => complexObjects_shift j T h (-1))
    (corestrict_op_isExact j T) f

/-- The forward comparison retains the original second endpoint. -/
theorem corestrictJointIso_inr :
    (corestrict j T).op.map
        ((perfectSupportedOppositeJointData T.ι).inr.app f) ≫
      ((corestrictJointIso j T).hom.app f).hom.left =
    (oppositeJointData j T).inr.app
      ((corestrict j T).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inr
    (C := X.Modules)
    (D := U.Modules) (restrictFunctor j)
    (perfectSupported T.ι) (complexObjects j T)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => perfectSupported_shift_of_quasiIso_zero T.ι h (-1))
    (fun _ h => complexObjects_shift j T h (-1))
    (corestrict_op_isExact j T) f

/-- The forward comparison retains the original weak projection. -/
theorem corestrictJointIso_projection :
    ((corestrictJointIso j T).hom.app f).hom.right ≫
      (oppositeJointData j T).projection.app
        ((corestrict j T).op.mapArrow.obj f) =
    (corestrict j T).op.map
      ((perfectSupportedOppositeJointData T.ι).projection.app f) :=
  oppositeComplexJointDataMapIso_projection
    (C := X.Modules)
    (D := U.Modules) (restrictFunctor j)
    (perfectSupported T.ι) (complexObjects j T)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => perfectSupported_shift_of_quasiIso_zero T.ι h (-1))
    (fun _ h => complexObjects_shift j T h (-1))
    (corestrict_op_isExact j T) f

/-- The inverse comparison retains the original first endpoint. -/
theorem corestrictJointIso_inv_inl :
    (oppositeJointData j T).inl.app
        ((corestrict j T).op.mapArrow.obj f) ≫
      ((corestrictJointIso j T).inv.app f).hom.left =
    (corestrict j T).op.map
      ((perfectSupportedOppositeJointData T.ι).inl.app f) :=
  oppositeComplexJointDataMapIso_inv_inl
    (C := X.Modules)
    (D := U.Modules) (restrictFunctor j)
    (perfectSupported T.ι) (complexObjects j T)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => perfectSupported_shift_of_quasiIso_zero T.ι h (-1))
    (fun _ h => complexObjects_shift j T h (-1))
    (corestrict_op_isExact j T) f

/-- The inverse comparison retains the original second endpoint. -/
theorem corestrictJointIso_inv_inr :
    (oppositeJointData j T).inr.app
        ((corestrict j T).op.mapArrow.obj f) ≫
      ((corestrictJointIso j T).inv.app f).hom.left =
    (corestrict j T).op.map
      ((perfectSupportedOppositeJointData T.ι).inr.app f) :=
  oppositeComplexJointDataMapIso_inv_inr
    (C := X.Modules)
    (D := U.Modules) (restrictFunctor j)
    (perfectSupported T.ι) (complexObjects j T)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => perfectSupported_shift_of_quasiIso_zero T.ι h (-1))
    (fun _ h => complexObjects_shift j T h (-1))
    (corestrict_op_isExact j T) f

/-- The inverse comparison retains the original weak projection. -/
theorem corestrictJointIso_inv_projection :
    ((corestrictJointIso j T).inv.app f).hom.right ≫
      (corestrict j T).op.map
        ((perfectSupportedOppositeJointData T.ι).projection.app f) =
    (oppositeJointData j T).projection.app
      ((corestrict j T).op.mapArrow.obj f) :=
  oppositeComplexJointDataMapIso_inv_projection
    (C := X.Modules)
    (D := U.Modules) (restrictFunctor j)
    (perfectSupported T.ι) (complexObjects j T)
    (fun K hK => ⟨K, hK, ⟨Iso.refl _⟩⟩)
    (fun _ h => perfectSupported_shift_of_quasiIso_zero T.ι h (-1))
    (fun _ h => complexObjects_shift j T h (-1))
    (corestrict_op_isExact j T) f

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
