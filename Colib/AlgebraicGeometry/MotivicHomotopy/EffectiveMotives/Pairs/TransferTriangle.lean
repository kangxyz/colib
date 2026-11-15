/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.ReflectionNaturality
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.ReflectionExactness
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle

/-!
# Effective triangles of transfer short exact sequences

The degree-zero triangle attached to a short exact sequence of Nisnevich
transfer sheaves is bounded above. Effective reflection retains the
original degree-zero maps and signed connecting morphism.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

variable (k : Type u) [Field k] [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "NST(" field ")" => LargeSheaves field
local notation "S" => singleTransferSheafMinus k
local notation "M" => effectiveReflection k
set_option quotPrecheck false in
local notation "V" => DerivedCategory.Minus.ι (C := NST(k))

/-- Use the native transfer abelian structure for the derived single triangles. -/
local instance instAbelianTransferTriangle : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The short exact sequence of single transfer sheaves in the bounded-above derived category. -/
@[expose] def singleTransferSheafTriangle {Q : ShortComplex NST(k)} (h : Q.ShortExact) :
    Triangle (DerivedCategory.Minus NST(k)) :=
  Triangle.mk ((S).map Q.f) ((S).map Q.g)
    (ObjectProperty.homMk (X := (S).obj Q.X₃) (Y := ((S).obj Q.X₁)⟦(1 : ℤ)⟧)
      (h.singleδ ≫ ((V).commShiftIso (1 : ℤ)).inv.app ((S).obj Q.X₁)))

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The triangle of the original short exact sequence of transfer sheaves is distinguished. -/
theorem singleTransferSheafTriangle_distinguished {Q : ShortComplex NST(k)}
    (h : Q.ShortExact) : singleTransferSheafTriangle k h ∈ distTriang _ := by
  change (V).mapTriangle.obj (singleTransferSheafTriangle k h) ∈ distTriang _
  have he : (V).mapTriangle.obj (singleTransferSheafTriangle k h) = h.singleTriangle := by
    rw [Functor.mapTriangle_obj]
    dsimp only [singleTransferSheafTriangle, Triangle.mk_mor₁, Triangle.mk_mor₂,
      Triangle.mk_mor₃, Triangle.mk_obj₁]
    let d := ((V).commShiftIso (1 : ℤ)).app ((S).obj Q.X₁)
    let δ : (V).obj ((S).obj Q.X₃) ⟶
        (shiftFunctor (DerivedCategory NST(k)) (1 : ℤ)).obj ((V).obj ((S).obj Q.X₁)) :=
      h.singleδ
    change Triangle.mk ((DerivedCategory.singleFunctor NST(k) 0).map Q.f)
        ((DerivedCategory.singleFunctor NST(k) 0).map Q.g) ((δ ≫ d.inv) ≫ d.hom) =
      Triangle.mk ((DerivedCategory.singleFunctor NST(k) 0).map Q.f)
        ((DerivedCategory.singleFunctor NST(k) 0).map Q.g) δ
    exact congrArg (Triangle.mk ((DerivedCategory.singleFunctor NST(k) 0).map Q.f)
      ((DerivedCategory.singleFunctor NST(k) 0).map Q.g)) (by simp [Category.assoc])
  rw [he]
  exact h.singleTriangle_distinguished

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})] in
/-- The map of bounded-above single triangles induced by a map of short exact sequences. -/
@[expose] def singleTransferSheafTriangleMap {Q Q' : ShortComplex NST(k)}
    (h : Q.ShortExact) (h' : Q'.ShortExact) (f : Q ⟶ Q') :
    singleTransferSheafTriangle k h ⟶ singleTransferSheafTriangle k h' where
  hom₁ := (S).map f.τ₁
  hom₂ := (S).map f.τ₂
  hom₃ := (S).map f.τ₃
  comm₁ := by
    change (S).map Q.f ≫ (S).map f.τ₂ = (S).map f.τ₁ ≫ (S).map Q'.f
    exact (Functor.map_comp _ _ _).symm.trans
      (((S).congr_map f.comm₁₂.symm).trans (Functor.map_comp _ _ _))
  comm₂ := by
    change (S).map Q.g ≫ (S).map f.τ₃ = (S).map f.τ₂ ≫ (S).map Q'.g
    exact (Functor.map_comp _ _ _).symm.trans
      (((S).congr_map f.comm₂₃.symm).trans (Functor.map_comp _ _ _))
  comm₃ := by
    apply (V).map_injective
    simp only [Functor.map_comp]
    let d := (V).commShiftIso (1 : ℤ)
    let D := DerivedCategory.singleFunctor NST(k) 0
    change (h.singleδ ≫ d.inv.app ((S).obj Q.X₁)) ≫
        (V).map (((S).map f.τ₁)⟦(1 : ℤ)⟧') =
      (D).map f.τ₃ ≫ h'.singleδ ≫ d.inv.app ((S).obj Q'.X₁)
    have hδ : h.singleδ ≫ ((D).map f.τ₁)⟦(1 : ℤ)⟧' =
        (D).map f.τ₃ ≫ h'.singleδ :=
      (ShortComplex.ShortExact.singleTriangle.map h h' f).comm₃
    rw [Category.assoc, ← (V).commShiftIso_inv_naturality ((S).map f.τ₁) (1 : ℤ)]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ d.inv.app ((S).obj Q'.X₁)) hδ).trans (Category.assoc _ _ _))

/-- The native connecting map after effective reflection. -/
@[expose] def effectiveTransferSheafConnecting {Q : ShortComplex NST(k)} (h : Q.ShortExact) :
    ((S) ⋙ (M)).obj Q.X₃ ⟶ (((S) ⋙ (M)).obj Q.X₁)⟦(1 : ℤ)⟧ :=
  ((M).mapTriangle.obj (singleTransferSheafTriangle k h)).mor₃

/-- The effective triangle of the given short exact sequence of transfer coefficients. -/
@[expose] def effectiveTransferSheafTriangle {Q : ShortComplex NST(k)} (h : Q.ShortExact) :
    Triangle (EffectiveMotivesMinus k) :=
  Triangle.mk (((S) ⋙ (M)).map Q.f) (((S) ⋙ (M)).map Q.g)
    (effectiveTransferSheafConnecting k h)

/-- The original transfer sequence remains distinguished under effective reflection. -/
theorem effectiveTransferSheafTriangle_distinguished {Q : ShortComplex NST(k)} (h : Q.ShortExact) :
    effectiveTransferSheafTriangle k h ∈ distTriang _ :=
  (M).map_distinguished _ (singleTransferSheafTriangle_distinguished k h)

/-- A map of short exact transfer sequences induces the original reflected
degree-zero maps in their effective triangles. -/
@[expose] def effectiveTransferSheafTriangleMap {Q Q' : ShortComplex NST(k)}
    (h : Q.ShortExact) (h' : Q'.ShortExact) (f : Q ⟶ Q') :
    effectiveTransferSheafTriangle k h ⟶ effectiveTransferSheafTriangle k h' :=
  (M).mapTriangle.map (singleTransferSheafTriangleMap k h h' f)

/-- Its third component is the reflection of the literal third map. -/
theorem effectiveTransferSheafTriangleMap_hom₃ {Q Q' : ShortComplex NST(k)}
    (h : Q.ShortExact) (h' : Q'.ShortExact) (f : Q ⟶ Q') :
    (effectiveTransferSheafTriangleMap k h h' f).hom₃ = ((S) ⋙ (M)).map f.τ₃ := rfl

end AlgebraicGeometry.MotivicHomotopy
