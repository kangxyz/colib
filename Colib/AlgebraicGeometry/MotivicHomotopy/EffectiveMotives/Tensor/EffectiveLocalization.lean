/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Tensor.NisnevichLocalization
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Exactness
import Mathlib.CategoryTheory.Localization.Composition
import Mathlib.CategoryTheory.Localization.Prod
import StacksFrontier.CategoryTheory.Triangulated.Quotient

/-! # Localization by Nisnevich sheafification and affine-line reflection -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open PresheafWithTransfers SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "PST(" K ")" => LargePresheaves K
local notation "NST(" K ")" => LargeSheaves K
local notation "a(" K ")" => derivedNisnevichSheafification K
local notation "q(" K ")" => singularPresheafToEffective K
local notation "M(" K ")" => effectiveReflection K

/-- The canonical abelian structure on transfer sheaves. -/
local instance instAbelianEffectiveLocalization : Abelian NST(k) := SheafWithTransfers.abelian k

private abbrev effectiveReflectionEquivalences : MorphismProperty (DerivedCategory.Minus NST(k)) :=
  (MorphismProperty.isomorphisms (EffectiveMotivesMinus k)).inverseImage M(k)

/-- The actual singular and Nisnevich equivalences of bounded-above
derived transfer presheaves. -/
abbrev effectivePresheafEquivalences : MorphismProperty (DerivedCategory.Minus PST(k)) :=
  (MorphismProperty.isomorphisms (EffectiveMotivesMinus k)).inverseImage q(k)

private theorem effectiveReflectionEquivalences_le_map :
    effectiveReflectionEquivalences k ≤ (effectivePresheafEquivalences k).map a(k) := by
  intro X Y f hf
  let W := (nisnevichDerivedMinusKernel k).trW
  let P := presheafLift k X
  let Q := presheafLift k Y
  let e := sheafificationPresheafLiftIso k X
  let d := sheafificationPresheafLiftIso k Y
  let g := e.hom ≫ f ≫ d.inv
  obtain ⟨p, hp⟩ := Localization.exists_leftFraction (a(k)) W g
  let : IsIso ((M(k)).map f) := hf
  let : IsIso ((M(k)).map g) := by
    change IsIso ((M(k)).map (e.hom ≫ f ≫ d.inv))
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  let : IsIso ((a(k)).map p.s) := Localization.inverts (a(k)) W p.s p.hs
  have h : g ≫ (a(k)).map p.s = (a(k)).map p.f := by
    rw [hp]
    exact MorphismProperty.LeftFraction.map_comp_map_s p (a(k)) (Localization.inverts (a(k)) W)
  have hg : IsIso ((M(k)).map ((a(k)).map p.f)) := by
    rw [← h, Functor.map_comp]
    infer_instance
  have hp' : effectivePresheafEquivalences k p.f :=
    (NatIso.isIso_map_iff (sheafificationEffectiveReflectionIso k) p.f).1 hg
  let z := d.symm ≪≫ asIso ((a(k)).map p.s)
  refine ⟨P, p.Y', p.f, hp', ⟨Arrow.isoMk e z.symm ?_⟩⟩
  change e.hom ≫ f = (a(k)).map p.f ≫ z.inv
  have hf' : (a(k)).map p.f = (e.hom ≫ f) ≫ z.hom := by
    rw [← h]
    change (e.hom ≫ f ≫ d.inv) ≫ (a(k)).map p.s = (e.hom ≫ f) ≫ (d.inv ≫ (a(k)).map p.s)
    simp only [Category.assoc]
  rw [hf', Category.assoc, z.hom_inv_id, Category.comp_id]

/-- The sheafified singular functor localizes at the maps it inverts. -/
instance singularPresheafToEffective_isLocalization :
    (q(k)).IsLocalization (effectivePresheafEquivalences k) := by
  let V := effectiveReflectionEquivalences k
  let W := (nisnevichDerivedMinusKernel k).trW
  let U := effectivePresheafEquivalences k
  let e := sheafificationEffectiveReflectionIso k
  let E := effectiveReflectionAdjunction k
  let : (M(k)).IsLocalization V := E.isLocalization
  let : (a(k) ⋙ M(k)).IsLocalization U := Functor.IsLocalization.comp (a(k)) (M(k)) W V U
    (fun _ _ f hf => (NatIso.isIso_map_iff e f).2 hf)
    (fun _ _ f hf => (NatIso.isIso_map_iff e f).1
      (inferInstanceAs (IsIso ((M(k)).map (Localization.isoOfHom (a(k)) W f hf).hom))))
    (effectiveReflectionEquivalences_le_map k)
  exact Functor.IsLocalization.of_iso U e

instance : (q(k)).CommShift ℤ := Functor.CommShift.ofIso (sheafificationEffectiveReflectionIso k) ℤ

instance : (q(k)).IsTriangulated := by
  let e := sheafificationEffectiveReflectionIso k
  let : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofIso_compatibility e ℤ
  exact Functor.isTriangulated_of_iso e

/-- The effective equivalences are the morphisms with a cone killed by
the sheafified singular functor. -/
theorem effectivePresheafEquivalences_eq_trW :
    effectivePresheafEquivalences k = (q(k)).kernel.trW := by
  ext X Y f
  change IsIso ((q(k)).map f) ↔ (q(k)).kernel.trW f
  let : (q(k)).kernel.IsClosedUnderIsomorphisms :=
    ⟨fun e h => h.of_iso ((q(k)).mapIso e).symm⟩
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  let T := Triangle.mk f g h
  exact ((ObjectProperty.trW_iff_of_distinguished (q(k)).kernel T hT).trans
    (Triangle.isZero₃_iff_isIso₁ ((q(k)).mapTriangle.obj T) ((q(k)).map_distinguished T hT))).symm

instance : (effectivePresheafEquivalences k).HasLeftCalculusOfFractions := by
  rw [effectivePresheafEquivalences_eq_trW]
  let : (q(k)).kernel.IsTriangulated := (q(k)).isTriangulated_and_isSaturated_kernel.1
  infer_instance

end AlgebraicGeometry.MotivicHomotopy
