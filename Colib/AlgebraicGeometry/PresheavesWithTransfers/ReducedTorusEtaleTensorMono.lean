/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ReducedTorusEtaleTensor
public import Colib.Algebra.Homology.CochainComplex.PointwiseFlatTensor

/-! # Monomorphisms and sheafified pointwise-flat coefficients

The inclusion of sheaves is used only to preserve monomorphisms, not acyclic
complexes. This is one exactness input, not a K-flatness assertion.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

attribute [local instance] smoothEtaleIntegral_isMonoidal_W Sheaf.monoidalCategory

local notation "a" => smoothEtaleIntegralSheafify k
local notation "i" => smoothEtaleIntegralInclusion k

/-- The original counit and tensorator compare the two fixed-coefficient functors. -/
def smoothEtaleIntegralTensorRightIso
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ) :
    tensorRight ((a).obj P) ≅ i ⋙ tensorRight P ⋙ a :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso (sheafificationAdjunction
        (SmoothSite.etaleTopology (Spec (CommRingCat.of k))) (ModuleCat.{u + 1} ℤ)).counit).symm
      (tensorRight ((a).obj P)) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft i (Functor.Monoidal.commTensorRight a P)

/-- Sectionwise flatness preserves monomorphisms before sheafification. -/
theorem smoothIntegralTensorRight_preservesMonomorphisms
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
    [∀ X, Module.Flat ℤ (P.obj X)] : (tensorRight P).PreservesMonomorphisms where
  preserves {X Y} f hf := by
    let := hf
    apply (NatTrans.mono_iff_mono_app _).2
    intro U
    apply (ModuleCat.mono_iff_injective _).2
    change Function.Injective ((f.app U).hom.rTensor (P.obj U))
    exact Module.Flat.rTensor_preserves_injective_linearMap (f.app U).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)

/-- The actual sheaf tensor with a sheafified pointwise-flat coefficient preserves monos. -/
theorem smoothEtaleIntegralTensorRight_preservesMonomorphisms
    (P : (SmoothSite (Spec (CommRingCat.of k)))ᵒᵖ ⥤ ModuleCat.{u + 1} ℤ)
    [∀ X, Module.Flat ℤ (P.obj X)] : (tensorRight ((a).obj P)).PreservesMonomorphisms where
  preserves {X Y} f hf := by
    let := hf
    let := smoothIntegralTensorRight_preservesMonomorphisms k P
    let : Mono ((i).map f) := Functor.map_mono i f
    let : Mono ((tensorRight P).map ((i).map f)) :=
      Functor.map_mono (tensorRight P) ((i).map f)
    let : Mono ((a).map ((tensorRight P).map ((i).map f))) :=
      Functor.map_mono a ((tensorRight P).map ((i).map f))
    let : Mono ((i ⋙ tensorRight P ⋙ a).map f) :=
      inferInstanceAs (Mono ((a).map ((tensorRight P).map ((i).map f))))
    let e := smoothEtaleIntegralTensorRightIso k P
    constructor
    intro Z g h hgh
    have hcomp : g ≫ e.hom.app X = h ≫ e.hom.app X := by
      apply (cancel_mono ((i ⋙ tensorRight P ⋙ a).map f)).mp
      simpa only [Category.assoc, ← e.hom.naturality f] using
        congrArg (fun t => t ≫ e.hom.app Y) hgh
    have := congrArg (fun t => t ≫ e.inv.app X) hcomp
    simpa only [Category.assoc, e.hom_inv_id_app, Category.comp_id] using this

end AlgebraicGeometry.PresheafWithTransfers
