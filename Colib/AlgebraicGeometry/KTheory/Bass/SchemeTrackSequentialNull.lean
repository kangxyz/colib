/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialHomotopy
public import Colib.Topology.Prespectrum.TelescopeConeDescent
public import Colib.Topology.Prespectrum.FiberLiftNaturality

/-!
# The same original finite null on current and ordinary whole-track presentations

The original three finite Model towers, their original two map families, and their given
whole finite composite nulls determine the actual ordinary-colimit composite null.
Only the proved composition and zero laws identify its endpoints. The whole comparison
preserves that original null at every time. Existing path-space fiber-lift naturality then
transports stability of this specified lift in either direction.
-/
/-!
Implementation provenance: adapted from `Quillen/KTheory/Bass/SchemeTrackSequentialNull.lean` at
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
open scoped unitInterval
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
universe u w
namespace KTheory.Bass.SchemeTrackSequentialPresentation
open NaturalTrack GeometricSeedCospan ModelZigzagSequentialization
variable (M₀ M₁ M₂ : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A₀ : Track laurent.op coefficient (M₀ ⋙ prespectrumFunctor))
    (A₁ : Track laurent.op coefficient (M₁ ⋙ prespectrumFunctor))
    (A₂ : Track laurent.op coefficient (M₂ ⋙ prespectrumFunctor))
    (X₀ X₁ X₂ : Scheme.{u}ᵒᵖ)
    (d : ∀ i, vertex squareFunctor M₀ X₀ i ⟶ vertex squareFunctor M₁ X₁ i)
    (e : ∀ i, vertex squareFunctor M₁ X₁ i ⟶ vertex squareFunctor M₂ X₂ i)
    (hd : ∀ i, current M₀ A₀ X₀ i ≫ d (i + 1) = d i ≫ current M₁ A₁ X₁ i)
    (he : ∀ i, current M₁ A₁ X₁ i ≫ e (i + 1) = e i ≫ current M₂ A₂ X₂ i)
    (N : ∀ i, Homotopy (d i ≫ e i)
      (LoopPrespectrum.zeroHom (vertex squareFunctor M₀ X₀ i) (vertex squareFunctor M₂ X₂ i)))
    (hN : ∀ i n r x, (current M₂ A₂ X₂ i).map n ((N i).level n (r, x)) =
      (N (i + 1)).level n (r, (current M₀ A₀ X₀ i).map n x))

/-- The literal original current-telescope null of the original finite composite nulls. -/
def originalCurrentNull : Homotopy
    (finiteCurrentTelescopeMap M₀ A₀ X₀ M₁ A₁ X₁ d hd ≫
      finiteCurrentTelescopeMap M₁ A₁ X₁ M₂ A₂ X₂ e he)
    (LoopPrespectrum.zeroHom _ _) :=
  Telescope.mapNullHomotopy (vertex squareFunctor M₀ X₀) (current M₀ A₀ X₀)
    (vertex squareFunctor M₁ X₁) (current M₁ A₁ X₁)
    (vertex squareFunctor M₂ X₂) (current M₂ A₂ X₂)
    d e (fun i ↦ (hd i).symm) (fun i ↦ (he i).symm) N hN

/-- The original finite nulls, with unchanged interior, descend to the actual ordinary composite. -/
def ordinaryCompositeNull : Homotopy
    (finiteMap M₀ A₀ X₀ M₁ A₁ X₁ d hd ≫ finiteMap M₁ A₁ X₁ M₂ A₂ X₂ e he)
    (LoopPrespectrum.zeroHom (presentation M₀ A₀ X₀) (presentation M₂ A₂ X₂)) :=
  (finiteHomotopy M₀ A₀ X₀ M₂ A₂ X₂ (fun i ↦ d i ≫ e i)
    (fun i ↦ LoopPrespectrum.zeroHom _ _)
    (fun i ↦ by rw [← Category.assoc, hd, Category.assoc, he, Category.assoc])
    (fun i ↦ by
      apply Topology.LoopPrespectrum.Hom.ext
      funext n
      ext _x
      exact (current M₂ A₂ X₂ i).map_point n |>.symm)
    N hN).cast (finiteMap_comp M₀ A₀ X₀ M₁ A₁ X₁ d hd M₂ A₂ X₂ e he).symm
      (finiteMap_zero M₀ A₀ X₀ M₂ A₂ X₂)

/-- The actual comparisons keep the entire original current null, at exactly the same time. -/
theorem comparison_originalNull (n : ℕ) (r : unitInterval)
    (q : (Telescope.prespectrum (vertex squareFunctor M₀ X₀) (current M₀ A₀ X₀)).space n) :
    (comparison M₂ A₂ X₂).map n
        ((originalCurrentNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN).level n (r, q)) =
      (ordinaryCompositeNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN).level n
        (r, (comparison M₀ A₀ X₀).map n q) :=
  (comparison_finiteHomotopy M₀ A₀ X₀ M₂ A₂ X₂ (fun i ↦ d i ≫ e i)
    (fun i ↦ LoopPrespectrum.zeroHom _ _)
    (fun i ↦ by rw [← Category.assoc, hd, Category.assoc, he, Category.assoc])
    (fun i ↦ by
      apply Topology.LoopPrespectrum.Hom.ext
      funext k
      ext _x
      exact (current M₂ A₂ X₂ i).map_point k |>.symm)
    N hN n r q).symm

/-- The actual path-space fiber lifts form the strict square of these same original nulls. -/
theorem sameNull_fiberLift_square :
    homotopyFiberLift (finiteCurrentTelescopeMap M₁ A₁ X₁ M₂ A₂ X₂ e he)
      (finiteCurrentTelescopeMap M₀ A₀ X₀ M₁ A₁ X₁ d hd)
      (originalCurrentNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN) ≫
      homotopyFiberMap (Arrow.homMk
        (f := Arrow.mk (finiteCurrentTelescopeMap M₁ A₁ X₁ M₂ A₂ X₂ e he))
        (g := Arrow.mk (finiteMap M₁ A₁ X₁ M₂ A₂ X₂ e he))
        (comparison M₁ A₁ X₁) (comparison M₂ A₂ X₂)
        (comparison_finiteMap M₁ A₁ X₁ M₂ A₂ X₂ e he).symm) =
      comparison M₀ A₀ X₀ ≫ homotopyFiberLift (finiteMap M₁ A₁ X₁ M₂ A₂ X₂ e he)
        (finiteMap M₀ A₀ X₀ M₁ A₁ X₁ d hd)
        (ordinaryCompositeNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN) :=
  homotopyFiberLift_naturality _ _ _ _ _ _
    (comparison M₀ A₀ X₀) (comparison M₁ A₁ X₁) (comparison M₂ A₂ X₂)
    (comparison_finiteMap M₀ A₀ X₀ M₁ A₁ X₁ d hd)
    (comparison_finiteMap M₁ A₁ X₁ M₂ A₂ X₂ e he).symm
    (comparison_originalNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN)

/-- The three genuine stable comparisons transport stability of this same-null fiber lift. -/
theorem sameNull_fiberLift_isStableEquivalence_iff :
    IsStableEquivalence (homotopyFiberLift
      (finiteCurrentTelescopeMap M₁ A₁ X₁ M₂ A₂ X₂ e he)
      (finiteCurrentTelescopeMap M₀ A₀ X₀ M₁ A₁ X₁ d hd)
      (originalCurrentNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN)) ↔
    IsStableEquivalence (homotopyFiberLift (finiteMap M₁ A₁ X₁ M₂ A₂ X₂ e he)
      (finiteMap M₀ A₀ X₀ M₁ A₁ X₁ d hd)
      (ordinaryCompositeNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN)) :=
  homotopyFiberLift_isStableEquivalence_iff _ _ _ _ _ _
    (comparison M₀ A₀ X₀) (comparison M₁ A₁ X₁) (comparison M₂ A₂ X₂)
    (comparison_finiteMap M₀ A₀ X₀ M₁ A₁ X₁ d hd)
    (comparison_finiteMap M₁ A₁ X₁ M₂ A₂ X₂ e he).symm
    (comparison_originalNull M₀ M₁ M₂ A₀ A₁ A₂ X₀ X₁ X₂ d e hd he N hN)
    (comparison_stable M₀ A₀ X₀) (comparison_stable M₁ A₁ X₁) (comparison_stable M₂ A₂ X₂)

end KTheory.Bass.SchemeTrackSequentialPresentation
