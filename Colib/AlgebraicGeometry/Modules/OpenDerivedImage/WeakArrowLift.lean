/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.WeakArrow
public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.DualFactorization
public import Colib.AlgebraicGeometry.Modules.PerfectOpenWeak

/-! # Strict incoming lifts on the actual image weak-arrow category

Both chain-map equations and both component kernels come from the actual geometric
factorization. The source remains the original relative perfect-complex category.
No ordinary outgoing approximation or fine weak-equivalence reflection is asserted.

Adapted from Quillen `AlgebraicGeometry/PerfectComplexes/OpenDerivedImage/Approximation.lean`
at commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen CategoryTheory.ExactCategory
open AlgebraicGeometry.RingedSpace HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
universe u d
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{d} U.Modules] [Fact (HasDerivedRoofs j)]

/-- Actual incoming lifts on the fine weak-arrow objects. No global fine
reflection is asserted for open restriction. -/
theorem weakArrow_target_lift
    {Z : WeakArrow.Obj (waldhausen j Fact.out) (corestrict j)} {B' : Obj j}
    (b : B' ⟶ (WeakArrow.target (waldhausen j Fact.out) (corestrict j)).obj Z) :
    ∃ (Y : WeakArrow.Obj (waldhausen j Fact.out) (corestrict j))
      (f : Y ⟶ Z) (v : B' ⟶ (WeakArrow.target (waldhausen j Fact.out) (corestrict j)).obj Y),
      (weakArrowOppositeWaldhausen j).cof.unop f ∧ (waldhausen j Fact.out).weq v ∧
      v ≫ (WeakArrow.target (waldhausen j Fact.out) (corestrict j)).map f = b := by
  have hw : QuasiIso Z.obj.hom.hom := Z.property
  obtain ⟨C, D, c, d, u, v, hC, hD, hu, hv, hsq, he, hc, hd, hkc, hkd⟩ :=
    exists_dual_factorization j (Fact.out : HasDerivedRoofs j)
      Z.obj.left.obj Z.obj.left.property Z.obj.right.obj B'.obj B'.property Z.obj.hom.hom b.hom
  let Y : WeakArrow.Obj (waldhausen j Fact.out) (corestrict j) :=
    ⟨⟨⟨C, hC⟩, ⟨D, hD⟩, ObjectProperty.homMk u⟩, hu⟩
  let f : Y ⟶ Z := ObjectProperty.homMk
    ⟨ObjectProperty.homMk c, ObjectProperty.homMk d, ObjectProperty.hom_ext _ hsq.symm⟩
  have : Epi c := HomologicalComplex.epi_of_epi_f c (fun i => by have := hc i; infer_instance)
  have : Epi d := HomologicalComplex.epi_of_epi_f d (fun i => by have := hd i; infer_instance)
  refine ⟨Y, f, ObjectProperty.homMk v, ?_, hv, ObjectProperty.hom_ext _ he⟩
  constructor
  · apply (ExactSubcategory.deflation_iff (abelianExactStructure (CochainComplex X.Modules ℤ))
      (IsPerfectComplex (X := X.toRingedSpace))
    f.hom.left).mpr
    refine ⟨kernel c, hkc, kernel.ι c, kernel.condition c, ?_⟩
    exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel c)
            mono_f := inferInstance
            epi_g := by change Epi c; infer_instance }
  · apply (ExactSubcategory.deflation_iff (abelianExactStructure (CochainComplex U.Modules ℤ))
      (complexObjects j)
    f.hom.right).mpr
    refine ⟨kernel d, hkd, kernel.ι d, kernel.condition d, ?_⟩
    exact { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel d)
            mono_f := inferInstance
            epi_g := by change Epi d; infer_instance }

/-- Coarse exactness retains the actual original relative source model. -/
theorem relativeCorestrict_isExact : IsExact
    (perfectOpenWeakWaldhausen j).cof (perfectOpenWeakWaldhausen j).weq
    (waldhausen j Fact.out).cof (waldhausen j Fact.out).weq (corestrict j) where
  zero := (corestrict_isExact j Fact.out).zero
  cofibration := (corestrict_isExact j Fact.out).cofibration
  weak _ h := h
  pushout := (corestrict_isExact j Fact.out).pushout

end AlgebraicGeometry.Scheme.Modules.OpenDerivedImage
