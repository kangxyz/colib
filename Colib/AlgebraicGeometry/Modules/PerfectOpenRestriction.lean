/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectRestriction
public import StacksFrontier.Homology.PseudoCoherentRelative.StrictlyPerfectRestrict

/-! # Literal restriction of native perfect complexes along any open immersion

This extends, without replacing, the open-subset API in `PerfectRestriction`.
Local strictly perfect representatives are restricted to inverse-image opens.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Literal degreewise restriction along an arbitrary open immersion preserves native
Stacks perfectness, without a chosen model of the perfect category. -/
@[stacks 08CM "Restriction of native perfect complexes along an arbitrary open immersion"]
theorem Complex.isPerfectComplex_restrictOpenImmersion (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K) :
    RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  apply RingedSpace.isPerfectComplex_of_forall_exists
  intro y
  obtain ⟨U, hy, P, hP, α, hα⟩ := hK.exists_local (j y)
  let V : Y.Opens := j ⁻¹ᵁ U
  let k : V.toScheme ⟶ U.toScheme := j ∣_ U
  let F := (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)
  let G := (restrictFunctor k).mapHomologicalComplex (ComplexShape.up ℤ)
  let e₁ := RingedSpace.restrictComplexIsoRestrictFunctor U k K
  let e₂ := (NatIso.mapHomologicalComplex
    ((restrictFunctorCongr (morphismRestrict_ι j U)) ≪≫
      restrictFunctorComp V.ι j) (ComplexShape.up ℤ)).app K
  let e₃ := (NatIso.mapHomologicalComplex
    (RingedSpace.restrictModulesIsoRestrictFunctor Y V)
      (ComplexShape.up ℤ)).app (F.obj K)
  let e : G.obj (RingedSpace.restrictComplex K U) ≅
      RingedSpace.restrictComplex (F.obj K) V := e₁ ≪≫ e₂ ≪≫ e₃.symm
  have : QuasiIso α := hα
  have : QuasiIso (G.map α) := by
    change QuasiIso (((restrictFunctor k).mapHomologicalComplex _).map α)
    infer_instance
  exact ⟨V, hy, G.obj P, isStrictlyPerfect_restrictFunctor k hP,
    G.map α ≫ e.hom, inferInstance⟩

/-- The restriction functor on the actual native full subcategories. -/
def perfectComplexesRestrictOpenImmersion :
    ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⥤
      ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)) :=
  ObjectProperty.lift (RingedSpace.IsPerfectComplex (X := Y.toRingedSpace))
    (ObjectProperty.ι (RingedSpace.IsPerfectComplex (X := X.toRingedSpace)) ⋙
      (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ))
    (fun K => Complex.isPerfectComplex_restrictOpenImmersion j K.obj K.property)

@[simp] theorem perfectComplexesRestrictOpenImmersion_obj
    (K : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))) :
    ((perfectComplexesRestrictOpenImmersion j).obj K).obj =
      ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K.obj := rfl

@[simp] theorem perfectComplexesRestrictOpenImmersion_map
    {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : K ⟶ L) :
    ((perfectComplexesRestrictOpenImmersion j).map f).hom =
      ((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f.hom := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Exactness for the existing ambient-monomorphism Waldhausen structure. -/
theorem perfectComplexesRestrictOpenImmersion_isExact :
    Waldhausen.IsExact (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen X.toRingedSpace).weq
      (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).cof
      (RingedSpace.perfectComplexesWaldhausen Y.toRingedSpace).weq
      (perfectComplexesRestrictOpenImmersion j) := by
  let F := (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)
  let P : ObjectProperty (CochainComplex X.Modules ℤ) :=
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace)
  let Q : ObjectProperty (CochainComplex Y.Modules ℤ) :=
    RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)
  refine { zero := ?_, cofibration := ?_, weak := ?_, pushout := ?_ }
  · intro Z hZ
    apply IsZero.of_full_of_faithful_of_isZero Q.ι
    exact F.map_isZero
      ((Waldhausen.CofibrationClosedSubcategory.inclusion_exact
        (Waldhausen.complexes X.Modules) P
        (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace)).zero hZ)
  · intro K L f hf
    change Mono (F.map f.hom)
    have : Mono (C := CochainComplex X.Modules ℤ) f.hom := hf
    infer_instance
  · intro K L f hf
    change QuasiIso (F.map f.hom)
    have : QuasiIso (C := X.Modules) f.hom := hf
    infer_instance
  · intro A B D T i f g k hi h
    apply IsPushout.of_map_of_faithful Q.ι
    exact (Waldhausen.CofibrationClosedSubcategory.inclusion_map_pushout
      (Waldhausen.complexes X.Modules) P
      (RingedSpace.perfectComplexes_cofibrationClosed X.toRingedSpace) hi h).map F

end AlgebraicGeometry.Scheme.Modules
