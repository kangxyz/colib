/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialNull
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeTrackSequentialComparison
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeInputNull

/-!
# The original input diagram null on actual ordinary whole-track presentations

The existing equivariant input maps, original iterated finite null, and original all-time
current equation instantiate the actual finite same-null consumer. Every ordinary null
slice is the actual image of the original diagram time slice, so the whole descended null
is scheme-natural. The resulting fiber-lift stability statement has exactly the existing
original current input maps and original current input null on its left side.
-/
/-!
Implementation provenance: adapted from Quillen at
`SchemeTrackSequentialDiagramNull.lean` in its original source owner.
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
open NaturalTrack GeometricSeedCospan ModelZigzagSequentialization SchemeNaturalSeed
variable (M₀ M₁ : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A₀ : Track laurent.op coefficient (M₀ ⋙ prespectrumFunctor))
    (A₁ : Track laurent.op coefficient (M₁ ⋙ prespectrumFunctor))
    (η : M₀ ⋙ prespectrumFunctor ⟶ M₁ ⋙ prespectrumFunctor) (hη : Equivariant A₀ A₁ η)

private theorem cast_at {E F : LoopPrespectrum.{w}} {f g f' g' : E ⟶ F}
    (H : Homotopy f g) (hf : f = f') (hg : g = g') (r : unitInterval) :
    (H.cast hf hg).at r = H.at r := rfl

private theorem finiteMap_congr (X : Scheme.{u}ᵒᵖ)
    (d e : ∀ i, vertex squareFunctor M₀ X i ⟶ vertex squareFunctor M₁ X i)
    (hd : ∀ i, current M₀ A₀ X i ≫ d (i + 1) = d i ≫ current M₁ A₁ X i)
    (he : ∀ i, current M₀ A₀ X i ≫ e (i + 1) = e i ≫ current M₁ A₁ X i)
    (h : d = e) : finiteMap M₀ A₀ X M₁ A₁ X d hd = finiteMap M₀ A₀ X M₁ A₁ X e he := by
  subst e
  rfl

/-- The exact original finite Bass image of the specified input natural transformation. -/
def originalFiniteInput (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    vertex squareFunctor M₀ X i ⟶ vertex squareFunctor M₁ X i :=
  ((strictDiagramIterate squareFunctor i).map η).app X

include hη in
/-- The existing original input-transition equation is the required actual finite square. -/
theorem originalFiniteInput_square (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    current M₀ A₀ X i ≫ originalFiniteInput M₀ M₁ η X (i + 1) =
      originalFiniteInput M₀ M₁ η X i ≫ current M₁ A₁ X i :=
  (congrArg (fun t ↦ t.app X) (currentInput_transition A₀ A₁ η hη i)).symm

/-- Original scheme maps agree with the same actual finite-input construction. -/
theorem schemeMap_eq_finiteMap {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    map M₀ A₀ g = finiteMap M₀ A₀ X M₀ A₀ Y (input M₀ g) (current_input M₀ A₀ g) := rfl

/-- The original equivariant input induces an actual natural map of ordinary presentations. -/
def ordinaryInputMap : diagram M₀ A₀ ⟶ diagram M₁ A₁ where
  app X := finiteMap M₀ A₀ X M₁ A₁ X (originalFiniteInput M₀ M₁ η X)
    (originalFiniteInput_square M₀ M₁ A₀ A₁ η hη X)
  naturality {X Y} g := by
    change map M₀ A₀ g ≫ _ = _ ≫ map M₁ A₁ g
    rw [schemeMap_eq_finiteMap, schemeMap_eq_finiteMap, finiteMap_comp, finiteMap_comp]
    congr 1
    funext i
    exact ((strictDiagramIterate squareFunctor i).map η).naturality g

/-- The actual original current input map commutes with the complete ordinary comparison. -/
theorem ordinaryInputMap_comparison :
    currentInputMap A₀ A₁ η hη ≫ comparisonNatTrans M₁ A₁ =
      comparisonNatTrans M₀ A₀ ≫ ordinaryInputMap M₀ M₁ A₀ A₁ η hη := by
  apply NatTrans.ext
  funext X
  exact comparison_finiteMap M₀ A₀ X M₁ A₁ X (originalFiniteInput M₀ M₁ η X)
    (originalFiniteInput_square M₀ M₁ A₀ A₁ η hη X)

variable (M₂ : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
    (A₂ : Track laurent.op coefficient (M₂ ⋙ prespectrumFunctor))
    (θ : M₁ ⋙ prespectrumFunctor ⟶ M₂ ⋙ prespectrumFunctor) (hθ : Equivariant A₁ A₂ θ)
    (N : DiagramNullHomotopy η θ)
    (hN : ∀ r, Equivariant A₀ A₂
      (diagramHomotopyAt (η := η ≫ θ)
        (θ := diagramZeroMap (M₀ ⋙ prespectrumFunctor) (M₂ ⋙ prespectrumFunctor))
        N.homotopy N.naturality r))

/-- The unchanged original finite diagram-null component. -/
def originalFiniteNull (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    Homotopy (originalFiniteInput M₀ M₁ η X i ≫ originalFiniteInput M₁ M₂ θ X i)
      (LoopPrespectrum.zeroHom _ _) :=
  (strictDiagramIterateNull squareFunctor N i).homotopy X

include hN in
/-- The existing original all-time equation discharges the finite same-null hypothesis. -/
theorem originalFiniteNull_transition (X : Scheme.{u}ᵒᵖ) (i n : ℕ) (r : unitInterval)
    (x : (vertex squareFunctor M₀ X i).space n) :
    (current M₂ A₂ X i).map n ((originalFiniteNull M₀ M₁ η M₂ θ N X i).level n (r, x)) =
      (originalFiniteNull M₀ M₁ η M₂ θ N X (i + 1)).level n
        (r, (current M₀ A₀ X i).map n x) :=
  currentNull_transition A₀ A₂ η θ N hN i X n r x

/-- The actual ordinary null is the same original finite null, with only endpoint casts. -/
def ordinaryInputNullHomotopy (X : Scheme.{u}ᵒᵖ) :
    Homotopy ((ordinaryInputMap M₀ M₁ A₀ A₁ η hη).app X ≫
      (ordinaryInputMap M₁ M₂ A₁ A₂ θ hθ).app X) (LoopPrespectrum.zeroHom _ _) :=
  ordinaryCompositeNull M₀ M₁ M₂ A₀ A₁ A₂ X X X
    (originalFiniteInput M₀ M₁ η X) (originalFiniteInput M₁ M₂ θ X)
    (originalFiniteInput_square M₀ M₁ A₀ A₁ η hη X)
    (originalFiniteInput_square M₁ M₂ A₁ A₂ θ hθ X)
    (originalFiniteNull M₀ M₁ η M₂ θ N X)
    (originalFiniteNull_transition M₀ M₁ A₀ η M₂ A₂ θ N hN X)

/-- Every ordinary null slice is the actual image of the original input diagram slice. -/
theorem ordinaryInputNullHomotopy_at (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (ordinaryInputNullHomotopy M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN X).at r =
      (ordinaryInputMap M₀ M₂ A₀ A₂
        (diagramHomotopyAt (η := η ≫ θ)
          (θ := diagramZeroMap (M₀ ⋙ prespectrumFunctor) (M₂ ⋙ prespectrumFunctor))
          N.homotopy N.naturality r) (hN r)).app X := by
  unfold ordinaryInputNullHomotopy ordinaryCompositeNull
  rw [cast_at, finiteHomotopy_at]
  unfold ordinaryInputMap
  refine finiteMap_congr M₀ M₂ A₀ A₂ X _ _
    (fun i ↦ by
      apply Topology.LoopPrespectrum.Hom.ext
      funext n
      ext x
      exact (originalFiniteNull_transition M₀ M₁ A₀ η M₂ A₂ θ N hN X i n r x).symm)
    (originalFiniteInput_square M₀ M₂ A₀ A₂ _ (hN r) X) ?_
  funext i
  exact strictDiagramIterateNull_at squareFunctor N i X r

/-- The specified original whole null descends as an actual scheme-natural diagram null. -/
def ordinaryInputNull : DiagramNullHomotopy (ordinaryInputMap M₀ M₁ A₀ A₁ η hη)
    (ordinaryInputMap M₁ M₂ A₁ A₂ θ hθ) where
  homotopy := ordinaryInputNullHomotopy M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN
  naturality {X Y} g n r x := by
    change ((diagram M₂ A₂).map g).map n
        (((ordinaryInputNullHomotopy M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN X).at r).map n x) =
      ((ordinaryInputNullHomotopy M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN Y).at r).map n
        (((diagram M₀ A₀).map g).map n x)
    rw [ordinaryInputNullHomotopy_at, ordinaryInputNullHomotopy_at]
    exact (congrArg (fun t ↦ t.map n x)
      ((ordinaryInputMap M₀ M₂ A₀ A₂ _ (hN r)).naturality g)).symm

/-- The actual ordinary comparison preserves every original current-input null time. -/
theorem ordinaryInputNull_comparison (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (q : ((currentTelescope A₀).obj X).space n) :
    (comparison M₂ A₂ X).map n
        (((currentInputNull A₀ A₁ A₂ η θ hη hθ N hN).homotopy X).level n (r, q)) =
      (((ordinaryInputNull M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN).homotopy X).level n
        (r, (comparison M₀ A₀ X).map n q)) :=
  comparison_originalNull M₀ M₁ M₂ A₀ A₁ A₂ X X X
    (originalFiniteInput M₀ M₁ η X) (originalFiniteInput M₁ M₂ θ X)
    (originalFiniteInput_square M₀ M₁ A₀ A₁ η hη X)
    (originalFiniteInput_square M₁ M₂ A₁ A₂ θ hθ X)
    (originalFiniteNull M₀ M₁ η M₂ θ N X)
    (originalFiniteNull_transition M₀ M₁ A₀ η M₂ A₂ θ N hN X) n r q

/-- Stability of the original current-input lift is equivalent to that of the same ordinary null. -/
theorem currentInputLift_stable_iff (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (homotopyFiberLift ((currentInputMap A₁ A₂ θ hθ).app X)
      ((currentInputMap A₀ A₁ η hη).app X)
      ((currentInputNull A₀ A₁ A₂ η θ hη hθ N hN).homotopy X)) ↔
    IsStableEquivalence (homotopyFiberLift ((ordinaryInputMap M₁ M₂ A₁ A₂ θ hθ).app X)
      ((ordinaryInputMap M₀ M₁ A₀ A₁ η hη).app X)
      ((ordinaryInputNull M₀ M₁ A₀ A₁ η hη M₂ A₂ θ hθ N hN).homotopy X)) :=
  sameNull_fiberLift_isStableEquivalence_iff M₀ M₁ M₂ A₀ A₁ A₂ X X X
    (originalFiniteInput M₀ M₁ η X) (originalFiniteInput M₁ M₂ θ X)
    (originalFiniteInput_square M₀ M₁ A₀ A₁ η hη X)
    (originalFiniteInput_square M₁ M₂ A₁ A₂ θ hθ X)
    (originalFiniteNull M₀ M₁ η M₂ θ N X)
    (originalFiniteNull_transition M₀ M₁ A₀ η M₂ A₂ θ N hN X)

end KTheory.Bass.SchemeTrackSequentialPresentation
