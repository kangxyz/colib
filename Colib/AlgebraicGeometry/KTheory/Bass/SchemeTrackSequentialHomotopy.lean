/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialFiniteMap
public import Colib.Topology.Prespectrum.ZigzagSequentializationColimitHomotopy

/-!
# Original finite whole families on actual whole-track presentations

The given original finite homotopies determine their looped-suspension homotopies. The
actual current all-time square and actual unit give both solid-arrow all-time squares.
The unchanged original family then descends to the actual ordinary presentation, and the
original current-telescope comparison retains it at every time. Literal zero endpoints
use only the proved zero-map laws, without choosing any new nullhomotopy.
-/
/-!
Implementation provenance: adapted from `Quillen/KTheory/Bass/SchemeTrackSequentialHomotopy.lean` at
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
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A : Track laurent.op coefficient (M ⋙ prespectrumFunctor)) (X : Scheme.{u}ᵒᵖ)
    (M' : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A' : Track laurent.op coefficient (M' ⋙ prespectrumFunctor)) (Y : Scheme.{u}ᵒᵖ)
    (d₀ d₁ : ∀ i, vertex squareFunctor M X i ⟶ vertex squareFunctor M' Y i)
    (hd₀ : ∀ i, current M A X i ≫ d₀ (i + 1) = d₀ i ≫ current M' A' Y i)
    (hd₁ : ∀ i, current M A X i ≫ d₁ (i + 1) = d₁ i ≫ current M' A' Y i)
    (HE : ∀ i, Homotopy (d₀ i) (d₁ i))
    (hE : ∀ i n r x, (current M' A' Y i).map n ((HE i).level n (r, x)) =
      (HE (i + 1)).level n (r, (current M A X i).map n x))

/-- The actual suspended-side family is exactly the looped suspension of the original next null. -/
def suspendedFiniteHomotopy (i : ℕ) :
    Homotopy (suspendedFiniteMap M X M' Y d₀ i) (suspendedFiniteMap M X M' Y d₁ i) :=
  (HE (i + 1)).suspensionLoop

/-- The actual unit has its original naturality at every value of the original family time. -/
theorem finiteUnit_homotopy (i n : ℕ) (r : unitInterval)
    (x : (vertex squareFunctor M X (i + 1)).space n) :
    (suspendedFiniteHomotopy M X M' Y d₀ d₁ HE i).level n
        (r, (unit squareFunctor M X i).map n x) =
      (unit squareFunctor M' Y i).map n ((HE (i + 1)).level n (r, x)) :=
  (HE (i + 1)).suspensionLoop_unit n r x

include hE in
/-- The actual current all-time square supplies the whole original forward-leg square. -/
theorem finiteForward_homotopy (i n : ℕ) (r : unitInterval)
    (x : (vertex squareFunctor M X i).space n) :
    (suspendedFiniteHomotopy M X M' Y d₀ d₁ HE i).level n
        (r, (forward M A X i).map n x) =
      (forward M' A' Y i).map n ((HE i).level n (r, x)) := by
  change (suspendedFiniteHomotopy M X M' Y d₀ d₁ HE i).level n
    (r, (unit squareFunctor M X i).map n ((current M A X i).map n x)) =
      (unit squareFunctor M' Y i).map n ((current M' A' Y i).map n ((HE i).level n (r, x)))
  rw [finiteUnit_homotopy, hE]

/-- The original finite whole homotopies descend to the actual ordinary presentations. -/
def finiteHomotopy : Homotopy (finiteMap M A X M' A' Y d₀ hd₀)
    (finiteMap M A X M' A' Y d₁ hd₁) :=
  ZigzagSequentialization.ordinaryColimitHomotopy
    (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
    (forward M A X) (unit squareFunctor M X)
    (vertex squareFunctor M' Y) (suspendedVertex squareFunctor M' Y)
    (forward M' A' Y) (unit squareFunctor M' Y)
    d₀ d₁ (suspendedFiniteMap M X M' Y d₀) (suspendedFiniteMap M X M' Y d₁)
    (finiteForward_square M A X M' A' Y d₀ hd₀) (finiteUnit_square M X M' Y d₀)
    (finiteForward_square M A X M' A' Y d₁ hd₁) (finiteUnit_square M X M' Y d₁)
    HE (suspendedFiniteHomotopy M X M' Y d₀ d₁ HE)
    (finiteForward_homotopy M A X M' A' Y d₀ d₁ HE hE)
    (finiteUnit_homotopy M X M' Y d₀ d₁ HE)

/-- Every family-time slice is the finite map of the same original input slices. -/
theorem finiteHomotopy_at (r : unitInterval) :
    (finiteHomotopy M A X M' A' Y d₀ d₁ hd₀ hd₁ HE hE).at r =
      finiteMap M A X M' A' Y (fun i ↦ (HE i).at r)
        (fun i ↦ by
          apply Topology.LoopPrespectrum.Hom.ext
          funext n
          ext x
          exact (hE i n r x).symm) := by
  unfold finiteHomotopy finiteMap
  rw [ZigzagSequentialization.ordinaryColimitHomotopy_at]
  congr 1
  funext i
  exact (HE (i + 1)).suspensionLoop_at r

/-- The same original finite family gives its original compatible current-telescope family. -/
def finiteCurrentHomotopy : Homotopy (finiteCurrentTelescopeMap M A X M' A' Y d₀ hd₀)
    (finiteCurrentTelescopeMap M A X M' A' Y d₁ hd₁) :=
  Telescope.mapHomotopy _ _ _ _ d₀ d₁ (fun i ↦ (hd₀ i).symm) (fun i ↦ (hd₁ i).symm) HE hE

/-- The actual ordinary comparison preserves this specified original family at every time. -/
theorem comparison_finiteHomotopy (n : ℕ) (r : unitInterval)
    (q : (Telescope.prespectrum (vertex squareFunctor M X) (current M A X)).space n) :
    (finiteHomotopy M A X M' A' Y d₀ d₁ hd₀ hd₁ HE hE).level n
        (r, (comparison M A X).map n q) =
      (comparison M' A' Y).map n
        ((finiteCurrentHomotopy M A X M' A' Y d₀ d₁ hd₀ hd₁ HE hE).level n (r, q)) := by
  have h := ZigzagSequentialization.telescopeMap_homotopy
    (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
    (forward M A X) (unit squareFunctor M X)
    (vertex squareFunctor M' Y) (suspendedVertex squareFunctor M' Y)
    (forward M' A' Y) (unit squareFunctor M' Y)
    d₀ d₁ (suspendedFiniteMap M X M' Y d₀) (suspendedFiniteMap M X M' Y d₁)
    (finiteForward_square M A X M' A' Y d₀ hd₀) (finiteUnit_square M X M' Y d₀)
    (finiteForward_square M A X M' A' Y d₁ hd₁) (finiteUnit_square M X M' Y d₁)
    HE (suspendedFiniteHomotopy M X M' Y d₀ d₁ HE)
    (finiteForward_homotopy M A X M' A' Y d₀ d₁ HE hE)
    (finiteUnit_homotopy M X M' Y d₀ d₁ HE)
    (current M A X) (current M' A' Y) (factorization M A X) (factorization M' A' Y)
    (fun i k t _s x ↦ finiteForward_homotopy M A X M' A' Y d₀ d₁ HE hE i k t x)
    (fun i ↦ (hd₀ i).symm) (fun i ↦ (hd₁ i).symm) hE n r q
  unfold finiteHomotopy comparison
  exact (ZigzagSequentialization.telescopeToOrdinaryColimit_homotopy
    (vertex squareFunctor M X) (suspendedVertex squareFunctor M X)
    (forward M A X) (unit squareFunctor M X)
    (vertex squareFunctor M' Y) (suspendedVertex squareFunctor M' Y)
    (forward M' A' Y) (unit squareFunctor M' Y)
    d₀ d₁ (suspendedFiniteMap M X M' Y d₀) (suspendedFiniteMap M X M' Y d₁)
    (finiteForward_square M A X M' A' Y d₀ hd₀) (finiteUnit_square M X M' Y d₀)
    (finiteForward_square M A X M' A' Y d₁ hd₁) (finiteUnit_square M X M' Y d₁)
    HE (suspendedFiniteHomotopy M X M' Y d₀ d₁ HE)
    (finiteForward_homotopy M A X M' A' Y d₀ d₁ HE hE)
    (finiteUnit_homotopy M X M' Y d₀ d₁ HE) n r
    ((ZigzagSequentialization.telescopeMap _ _ _ _ _ _).map n q)).trans
      (congrArg (fun x ↦ (ZigzagSequentialization.telescopeToOrdinaryColimit
        (vertex squareFunctor M' Y) (suspendedVertex squareFunctor M' Y)
        (forward M' A' Y) (unit squareFunctor M' Y)).map n x) h)

end KTheory.Bass.SchemeTrackSequentialPresentation
