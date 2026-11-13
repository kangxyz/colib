/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialPresentation
public import Colib.Topology.Prespectrum.SuspensionLoopHomotopy
public import Colib.Topology.Prespectrum.ZigzagSequentializationColimitNaturality

/-!
# Actual finite-input maps of whole-track ordinary presentations

Original finite maps between any two actual Model inputs determine the two solid-arrow
squares using their specified current-transition square and the literal suspension unit.
The resulting actual ordinary-colimit maps preserve identity, composition and zero, and
retain the original whole current-telescope comparison.
-/
/-!
Implementation provenance: adapted from Quillen at
`SchemeTrackSequentialFiniteMap.lean` in its original source owner.
`c561118b7795eb9780be9ed391c3251d6a4d0afd`. The actual maps, whole homotopies,
chosen nulls and proof terms are retained; namespaces and dependency owners are migrated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan ModelZigzagSequentialization
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ)
    (M' : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A' : Track laurent.op coefficient (M' ⋙ prespectrumFunctor)) (Y : Scheme.{u}ᵒᵖ)
    (d : ∀ i, vertex squareFunctor M X i ⟶ vertex squareFunctor M' Y i)
    (hd : ∀ i, current M A X i ≫ d (i + 1) = d i ≫ current M' A' Y i)

/-- The actual next-stage finite map acts on the unchanged looped suspension. -/
def suspendedFiniteMap (i : ℕ) :
    suspendedVertex squareFunctor M X i ⟶ suspendedVertex squareFunctor M' Y i :=
  parameterLoopingMap (suspensionConeMap (d (i + 1)))

/-- The backward solid arrow retains the original unit square. -/
theorem finiteUnit_square (i : ℕ) :
    unit squareFunctor M X i ≫ suspendedFiniteMap M X M' Y d i =
      d (i + 1) ≫ unit squareFunctor M' Y i :=
  (suspensionLoopUnit_naturality (d (i + 1))).symm

include hd in
/-- The forward square uses the given current square and the same original unit. -/
theorem finiteForward_square (i : ℕ) :
    forward M A X i ≫ suspendedFiniteMap M X M' Y d i = d i ≫ forward M' A' Y i := by
  unfold forward
  rw [Category.assoc, finiteUnit_square, ← Category.assoc, hd, Category.assoc]

/-- Actual finite maps induce the actual ordinary presentation map. -/
def finiteMap : presentation M A X ⟶ presentation M' A' Y :=
  ZigzagSequentialization.ordinaryColimitMap
    (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
    (forward M A X) (unit squareFunctor M X)
    (vertex squareFunctor M' Y) (suspendedVertex squareFunctor M' Y)
    (forward M' A' Y) (unit squareFunctor M' Y)
    d (suspendedFiniteMap M X M' Y d)
    (finiteForward_square M A X M' A' Y d hd) (finiteUnit_square M X M' Y d)

/-- The original finite maps also give their literal strict current-telescope map. -/
def finiteCurrentTelescopeMap :
    Telescope.prespectrum (vertex squareFunctor M X) (current M A X) ⟶
      Telescope.prespectrum (vertex squareFunctor M' Y) (current M' A' Y) :=
  Telescope.map _ _ _ _ d (fun i ↦ (hd i).symm)

/-- The actual ordinary comparison retains its entire original finite-input naturality. -/
theorem comparison_finiteMap :
    finiteCurrentTelescopeMap M A X M' A' Y d hd ≫ comparison M' A' Y =
      comparison M A X ≫ finiteMap M A X M' A' Y d hd := by
  have h := ZigzagSequentialization.telescopeMap_naturality
    (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
    (forward M A X) (unit squareFunctor M X)
    (vertex squareFunctor M' Y) (suspendedVertex squareFunctor M' Y)
    (forward M' A' Y) (unit squareFunctor M' Y)
    d (suspendedFiniteMap M X M' Y d)
    (finiteForward_square M A X M' A' Y d hd) (finiteUnit_square M X M' Y d)
    (current M A X) (current M' A' Y) (factorization M A X) (factorization M' A' Y)
    (fun i n _r x ↦ congrArg (fun m ↦ m.map n x)
      (finiteForward_square M A X M' A' Y d hd i)) (fun i ↦ (hd i).symm)
  unfold finiteCurrentTelescopeMap comparison finiteMap
  rw [← Category.assoc, h, Category.assoc,
    ZigzagSequentialization.telescopeToOrdinaryColimit_naturality, ← Category.assoc]

/-- The original identity finite maps induce the literal identity presentation map. -/
@[simp] theorem finiteMap_id :
    finiteMap M A X M A X (fun i ↦ 𝟙 (vertex squareFunctor M X i))
      (fun i ↦ by simp) = 𝟙 (presentation M A X) := by
  unfold finiteMap
  have h : suspendedFiniteMap M X M X (fun i ↦ 𝟙 (vertex squareFunctor M X i)) =
      fun i ↦ 𝟙 (suspendedVertex squareFunctor M X i) := by
    funext i
    unfold suspendedFiniteMap
    rw [suspensionConeMap_id]
    exact parameterLoopingFunctor.map_id _
  simp only [h]
  exact ZigzagSequentialization.ordinaryColimitMap_id _ _ _ _

/-- Original zero finite maps retain a literal zero ordinary-presentation endpoint. -/
@[simp] theorem finiteMap_zero :
    finiteMap M A X M' A' Y (fun i ↦ LoopPrespectrum.zeroHom _ _)
      (fun i ↦ by
        apply Topology.LoopPrespectrum.Hom.ext
        funext n
        ext _x
        exact (current M' A' Y i).map_point n |>.symm) =
        LoopPrespectrum.zeroHom (presentation M A X) (presentation M' A' Y) := by
  unfold finiteMap
  have h : suspendedFiniteMap M X M' Y (fun i ↦ LoopPrespectrum.zeroHom _ _) =
      fun i ↦ LoopPrespectrum.zeroHom _ _ := by
    funext i
    exact suspensionLoopMap_zeroHom _ _
  simp only [h]
  exact ZigzagSequentialization.ordinaryColimitMap_zero _ _ _ _ _ _ _ _

variable (M'' : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A'' : Track laurent.op coefficient (M'' ⋙ prespectrumFunctor)) (Z : Scheme.{u}ᵒᵖ)
    (d' : ∀ i, vertex squareFunctor M' Y i ⟶ vertex squareFunctor M'' Z i)
    (hd' : ∀ i, current M' A' Y i ≫ d' (i + 1) = d' i ≫ current M'' A'' Z i)

/-- The unchanged composite of original finite maps induces their actual composite map. -/
@[simp] theorem finiteMap_comp :
    finiteMap M A X M' A' Y d hd ≫ finiteMap M' A' Y M'' A'' Z d' hd' =
      finiteMap M A X M'' A'' Z (fun i ↦ d i ≫ d' i)
        (fun i ↦ by rw [← Category.assoc, hd, Category.assoc, hd', Category.assoc]) := by
  unfold finiteMap
  rw [ZigzagSequentialization.ordinaryColimitMap_comp]
  congr 1
  funext i
  unfold suspendedFiniteMap
  rw [suspensionConeMap_comp]
  exact (parameterLoopingFunctor.map_comp _ _).symm

end KTheory.Bass.SchemeTrackSequentialPresentation
