/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.Topology.Prespectrum.ZigzagSequentializationNaturality
public import Colib.AlgebraicGeometry.KTheory.Bass.SchemeModelRowPresentation

/-!
# Actual finite maps of the independent-cell proper-row presentations

The two supplied original finite-map squares determine a genuine map of the
canonical sequentializations. The comparison square retains the full original
telescope cylinders, using the proved independent-forward factorization.
-/
@[expose] public section
noncomputable section
open Topology
open CategoryTheory.Waldhausen.SmallWaldhausenCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry Topology.LoopPrespectrum
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Functor.IdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace KTheory.Bass.SchemeModelRowSeed
open NaturalTrack GeometricSeedCospan ModelRowZigzagSequentialization
variable (M : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M.obj (laurent.op.obj X)).obj.Obj)
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).hom.toFunctor (unit X) (unit Y))
  (X : Scheme.{u}ᵒᵖ)
  (M' : Scheme.{u}ᵒᵖ ⥤ WideSubcategory preservesZero.{w})
  (unit' : ∀ X, 𝟭 (M'.obj (laurent.op.obj X)).obj.Obj ≅ 𝟭 (M'.obj (laurent.op.obj X)).obj.Obj)
  (hunit' : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M'.map (laurent.op.map g)).hom.toFunctor (unit' X) (unit' Y))
  (Y : Scheme.{u}ᵒᵖ)
  (d : ∀ i, vertex squareFunctor M X i ⟶ vertex squareFunctor M' Y i)
  (v : ∀ i, target squareFunctor M X i ⟶ target squareFunctor M' Y i)
  (hd : ∀ i, d i ≫
      (SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M' unit' hunit') i).app Y =
    (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
      d (i + 1))
  (hb : ∀ i, backward squareFunctor M X i ≫ v i =
    d (i + 1) ≫ backward squareFunctor M' Y i)

include hd hb in
/-- The independent forward square follows from the two original finite-map squares. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationMap.lean:50"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem finiteForward_square (i : ℕ) :
    forward M unit hunit i X ≫ v i = d i ≫ forward M' unit' hunit' i Y := by
  rw [forward_eq_current, forward_eq_current, Category.assoc, hb, ← Category.assoc,
    ← hd, Category.assoc]

/-- The actual finite maps determine the genuine proper-row presentation map. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationMap.lean:56"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def finiteMap : presentation M unit hunit X ⟶ presentation M' unit' hunit' Y :=
  ZigzagSequentialization.inducedTelescopeMap
    (vertex squareFunctor M X) (target squareFunctor M X)
    (fun i => forward M unit hunit i X) (backward squareFunctor M X)
    (vertex squareFunctor M' Y) (target squareFunctor M' Y)
    (fun i => forward M' unit' hunit' i Y) (backward squareFunctor M' Y)
    d v (finiteForward_square M unit hunit X M' unit' hunit' Y d v hd hb) hb

/-- The same finite maps act on the original current telescopes. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationMap.lean:65"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
def finiteCurrentMap :
    (SchemeNaturalSeed.currentTelescope
      (ofModelUnits laurent.op coefficient M unit hunit)).obj X ⟶
    (SchemeNaturalSeed.currentTelescope
      (ofModelUnits laurent.op coefficient M' unit' hunit')).obj Y :=
  Telescope.map (vertex squareFunctor M X)
    (fun i => (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) i).app X)
    (vertex squareFunctor M' Y)
    (fun i => (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M' unit' hunit') i).app Y) d hd

/-- Both original telescope maps and every comparison-cylinder time form a strict square. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/SchemeModelRowPresentationMap.lean:78"
  "adaptation" "Original normalized-row maps, whole nulls and connecting-map equations."]
theorem comparison_finiteMap :
    finiteCurrentMap M unit hunit X M' unit' hunit' Y d hd ≫
        comparison M' unit' hunit' Y =
      comparison M unit hunit X ≫ finiteMap M unit hunit X M' unit' hunit' Y d v hd hb := by
  apply ZigzagSequentialization.telescopeMap_naturality
  intro i n _t x
  exact congrArg (fun a => a.map n x)
    (finiteForward_square M unit hunit X M' unit' hunit' Y d v hd hb i)

end KTheory.Bass.SchemeModelRowSeed
