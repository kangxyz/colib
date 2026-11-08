/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupport
public import StacksFrontier.Homology.KFlat.Bifunctor

/-! # The actual cone of an open-detected quasi-isomorphism is supported

Native perfect cone closure and the native cone/restriction isomorphism are used
on the actual complexes. The acyclic-cone criterion is the existing public Stacks
lemma. This separate consumer keeps the K-flat import out of the support foundation.
No relative fibration or boundary theorem is assumed.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]

/-- Restriction of an actual mapping cone is acyclic exactly when the restricted
actual chain map is a quasi-isomorphism. -/
theorem mappingCone_restrict_acyclic_iff {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) :
    (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (CochainComplex.mappingCone f)).Acyclic ↔
    QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  let e := CochainComplex.mappingCone.mapHomologicalComplexIso f (restrictFunctor j)
  rw [CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone]
  exact forall_congr' fun n => exactAt_iff_of_quasiIsoAt e.hom n

/-- The cone of a map between native perfect complexes is supported if its actual
restriction is a quasi-isomorphism. -/
theorem perfectSupported_mappingCone {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K)
    (hL : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) L)
    (hf : QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :
    perfectSupported j (CochainComplex.mappingCone f) :=
  ⟨RingedSpace.isPerfectComplex_mappingCone f hK hL,
    (mappingCone_restrict_acyclic_iff j f).2 hf⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Relative weakness supplies the same supported cone, without changing its map or sign. -/
theorem perfectOpenWeak_mappingCone_supported
    {K L : ObjectProperty.FullSubcategory (RingedSpace.IsPerfectComplex (X := X.toRingedSpace))}
    (f : K ⟶ L) (hf : (perfectOpenWeakWaldhausen j).weq f) :
    perfectSupported j (CochainComplex.mappingCone f.hom) :=
  perfectSupported_mappingCone j f.hom K.property L.property hf
end AlgebraicGeometry.Scheme.Modules
