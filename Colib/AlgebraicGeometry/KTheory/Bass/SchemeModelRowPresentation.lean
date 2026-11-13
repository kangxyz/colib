/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCell
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowCurrentComparison

public import Colib.KTheory.Bass.ModelRowTelescopeComparison
public import Colib.KTheory.Bass.ModelRowBackwardNaturality
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeCurrentStageTelescope
public import Colib.Topology.Prespectrum.ZigzagSequentializationColimit

/-! # Original independent normalized-row presentation and whole current comparison -/
@[expose] public noncomputable section
open CategoryTheory Topology Opposite AlgebraicGeometry
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open CategoryTheory.Waldhausen.SmallWaldhausenCategory Topology.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeModelRowSeed
open NaturalTrack GeometricSeedCospan ModelRowZigzagSequentialization
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))

/-- Coefficient naturality is proved for the independent forward maps at every actual stage. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:101"
  "adaptation" "Original independent finite stages and whole current comparison."]
theorem forward_naturality (i : ℕ) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).map g ≫
      forward M unit hunit i Y =
    forward M unit hunit i X ≫
      (ModelDiagramRowStabilizedTarget.targetDiagram squareFunctor i M).map g := by
  let T := SchemeNaturalSeed.currentTransition
    (ofModelUnits laurent.op coefficient M unit hunit) i ≫
      ModelRowZigzagSequentialization.backwardNatTrans squareFunctor M i
  have hT (Z : Scheme.{u}ᵒᵖ) : T.app Z = forward M unit hunit i Z := by
    change (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) i).app Z ≫
        (ModelRowZigzagSequentialization.backwardNatTrans squareFunctor M i).app Z = _
    rw [ModelRowZigzagSequentialization.backwardNatTrans_app]
    exact (forward_eq_current M unit hunit i Z).symm
  have h := T.naturality g
  rw [hT, hT] at h
  exact h

/-- The components remain the independently constructed forward cells. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:120"
  "adaptation" "Original independent finite stages and whole current comparison."]
def forwardNatTrans (i : ℕ) :
    (strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor) ⟶
      ModelDiagramRowStabilizedTarget.targetDiagram squareFunctor i M where
  app X := forward M unit hunit i X
  naturality _ _ := forward_naturality M unit hunit i

/-- This whole factorization is proved after constructing the independent forward leg. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:127"
  "adaptation" "Original independent finite stages and whole current comparison."]
def factorization (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Topology.LoopPrespectrum.Homotopy (forward M unit hunit i X)
      ((SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor M X i) :=
  (Topology.LoopPrespectrum.Homotopy.refl (forward M unit hunit i X)).cast rfl
    (forward_eq_current M unit hunit i X)

/-- The proper-row presentation uses the independent forward cells and original backward legs. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:136"
  "adaptation" "Original independent finite stages and whole current comparison."]
def presentation (X : Scheme.{u}ᵒᵖ) : LoopPrespectrum.{w} :=
  Telescope.prespectrum
    (ZigzagSequentialization.stage
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun i => forward M unit hunit i X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X))
    (ZigzagSequentialization.transition
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun i => forward M unit hunit i X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X))

/-- The genuine original current telescope maps to the independent-cell row presentation. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:150"
  "adaptation" "Original independent finite stages and whole current comparison."]
def comparison (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentTelescope
      (ofModelUnits laurent.op coefficient M unit hunit)).obj X ⟶
        presentation M unit hunit X :=
  ZigzagSequentialization.telescopeMap
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun i => forward M unit hunit i X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X)
      (fun i => (SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X)
      (fun i => factorization M unit hunit i X)

/-- Actual finite growth proves the independent-cell presentation comparison stable. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowSeed.lean:164"
  "adaptation" "Original independent finite stages and whole current comparison."]
theorem comparison_stable (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (comparison M unit hunit X) :=
  ModelRowZigzagSequentialization.telescopeMap_stable squareFunctor M X
    (fun i => forward M unit hunit i X)
    (fun i => (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) i).app X)
    (fun i => factorization M unit hunit i X)

end KTheory.Bass.SchemeModelRowSeed
