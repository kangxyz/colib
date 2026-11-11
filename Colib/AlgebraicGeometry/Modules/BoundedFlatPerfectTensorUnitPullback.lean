/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectTensorUnitAction
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfectPullbackUnit

/-!
# Tensor-unit action on the original geometric pullback

The underlying functor first performs the original termwise geometric pullback and then tensors
by the structure module. Its genuine left unitor identifies the coefficient-unit action with
the existing forward scalar automorphism on pullback, as an equality of natural transformations.

Adapted from Quillen at `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open Stacks.RegularSequence (globalSmulCenter)
universe u
namespace AlgebraicGeometry.Scheme.Modules

local instance boundedFlatPerfectTensorUnitPullbackMonoidal (X : Scheme.{u}) :
    MonoidalCategory X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidal X.toRingedSpace
local instance boundedFlatPerfectTensorUnitPullbackPreadditive (X : Scheme.{u}) :
    MonoidalPreadditive X.Modules :=
  Stacks.SheafOfModules.OnSpace.monoidalPreadditive X.toRingedSpace


/-- Original geometric pullback followed by genuine degreewise tensor by the structure module. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitPullback.lean:31"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def boundedAboveFlatPerfectTensorUnitPullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory ⥤
      (boundedAboveFlatPerfectComplex X.toRingedSpace).FullSubcategory :=
  boundedAboveFlatPerfectPullback f ⋙ boundedAboveFlatPerfectTensorUnit X

/-- The actual tensor left unitor on every original pulled-back complex. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitPullback.lean:36"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def boundedAboveFlatPerfectTensorUnitPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    boundedAboveFlatPerfectTensorUnitPullback f ≅ boundedAboveFlatPerfectPullback f :=
  Functor.isoWhiskerLeft (boundedAboveFlatPerfectPullback f) (boundedAboveFlatPerfectTensorUnitIso
      X) ≪≫
    Functor.rightUnitor _

/-- Tensor the original structure-module unit automorphism on every pulled-back complex. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitPullback.lean:42"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
def boundedAboveFlatPerfectTensorUnitPullbackAutomorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    boundedAboveFlatPerfectTensorUnitPullback f ≅ boundedAboveFlatPerfectTensorUnitPullback f :=
  Functor.isoWhiskerLeft (boundedAboveFlatPerfectPullback f)
    (boundedAboveFlatPerfectTensorUnitAutomorphism X r)

/-- The unitor retains the actual tensor-unit comparison after arbitrary geometric pullback. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitPullback.lean:49"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
theorem boundedAboveFlatPerfectTensorUnitPullbackIso_hom_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : (boundedAboveFlatPerfectComplex Y.toRingedSpace).FullSubcategory) :
    (boundedAboveFlatPerfectTensorUnitPullbackIso f).hom.app K =
      (boundedAboveFlatPerfectTensorUnitIso X).hom.app ((boundedAboveFlatPerfectPullback f).obj K)
      := by
  simp only [boundedAboveFlatPerfectTensorUnitPullbackIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact Category.comp_id _

/-- This is the original forward scalar, with tensor order and geometric pullback unchanged. -/
@[colib_ref "quillen"
  "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/TensorUnitPullback.lean:58"
  "adaptation" "Native degreewise tensor and left-unitor comparison"]
theorem boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_unitor {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (boundedAboveFlatPerfectTensorUnitPullbackAutomorphism f r).hom ≫
        (boundedAboveFlatPerfectTensorUnitPullbackIso f).hom =
      (boundedAboveFlatPerfectTensorUnitPullbackIso f).hom ≫
        (boundedAboveFlatPerfectPullbackUnitIso f r).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, boundedAboveFlatPerfectTensorUnitPullbackAutomorphism,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    boundedAboveFlatPerfectTensorUnitPullbackIso_hom_app, boundedAboveFlatPerfectPullbackUnitIso,
    Iso.trans_hom, Iso.symm_hom, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp]
  exact NatTrans.congr_app (boundedAboveFlatPerfectTensorUnitAutomorphism_unitor X r)
    ((boundedAboveFlatPerfectPullback f).obj K)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

attribute [colib_tag "COL-0542"] boundedAboveFlatPerfectTensorUnitPullbackAutomorphism_unitor

end AlgebraicGeometry.Scheme.Modules
