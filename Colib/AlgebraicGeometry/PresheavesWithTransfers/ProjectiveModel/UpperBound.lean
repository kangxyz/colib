/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ProjectiveModel

/-!
# Upper bounds in the projective transfer model

A projective representative can be chosen with the prescribed upper
bound. The existing quotient equivalence compares it with the chosen
projective representative, so the actual derived coefficient functor
retains that bound.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]

/-- Applying an additive coefficient functor on the actual bounded-above
projective model preserves each cohomological upper bound. -/
theorem projectiveDerivedMinusFunctor_isLE
    (F : PresheafWithTransfers.{u + 1} k ⥤ PresheafWithTransfers.{u + 1} k) [F.Additive]
    (K : DerivedCategory.Minus (PresheafWithTransfers.{u + 1} k)) (b : ℤ)
    (hK : K.obj.IsLE b) : ((projectiveDerivedMinusFunctor k F).obj K).obj.IsLE b := by
  let C := PresheafWithTransfers.{u + 1} k
  let t := DerivedCategory.TStructure.t (C := C)
  let : K.obj.IsLE b := hK
  obtain ⟨L, hL, ⟨d⟩⟩ := K.obj.exists_iso_Q_obj_of_isLE b
  obtain ⟨P, _⟩ := ProjectiveResolutionLemma.statement3 b L hL
  let : QuasiIso P.α := P.quasiIso
  let c := ComplexShape.up ℤ
  let U := HomotopyCategory.quotient C c
  let M : BoundedAboveProjectiveHomotopy k :=
    ⟨U.obj P.complex, b, P.boundedAbove, P.projective⟩
  let E := boundedAboveProjectiveEquivalence k
  let eM : E.functor.obj M ≅ K :=
    ObjectProperty.isoMk t.minus
      ((DerivedCategory.quotientCompQhIso C).app P.complex ≪≫
        asIso (DerivedCategory.Q.map P.α) ≪≫ d.symm)
  let eP : M ≅ E.inverse.obj K := E.unitIso.app M ≪≫ E.inverse.mapIso eM
  let G := projectiveHomotopyMapToDerivedMinus k F
  let N := (F.mapHomologicalComplex c).obj P.complex
  let : P.complex.IsStrictlyLE b := P.boundedAbove
  let : CochainComplex.IsStrictlyLE N b := (CochainComplex.isStrictlyLE_iff N b).2
    (fun i hi => F.map_isZero (CochainComplex.isZero_of_isStrictlyLE P.complex b i hi))
  let : (DerivedCategory.Q.obj N).IsLE b := inferInstance
  let : (G.obj M).obj.IsLE b := t.isLE_of_iso
    ((DerivedCategory.quotientCompQhIso C).app N).symm b
  let dP : (G.obj M).obj ≅ (G.obj (E.inverse.obj K)).obj :=
    (DerivedCategory.Minus.ι (C := C)).mapIso (G.mapIso eP)
  exact t.isLE_of_iso dP b

end AlgebraicGeometry.PresheafWithTransfers
