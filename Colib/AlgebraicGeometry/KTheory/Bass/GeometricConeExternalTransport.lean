/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.Bass.GeometricConeSchemeNaturality
public import Colib.AlgebraicGeometry.Scheme.IntegerBaseExternalTrack

/-!
# The original external-factor transport through two cone layers

The transport is exactly the original composite C(eta.inv) followed by eta.inv.
The inverse geometric move has its literal two-swap word. No action or
permutation-equivariance equation is supplied as a hypothesis.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Topology Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Topology.LoopPrespectrum Topology.LoopPrespectrum.StrictSquare
open scoped Topology unitInterval
universe u w
namespace KTheory.Bass.GeometricConeInterchange
variable {S T U : Scheme.{u}}

/-- The actual reverse two-swap move, in its literal order. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalTransport.lean:33"
  "adaptation" "Original two inverse index moves and all sixteen external transport cells."]
def externalInverse (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    (baseProductFunctor q).obj ((baseProductFunctor p).obj ((baseProductFunctor r).obj X)) ⟶
      (baseProductFunctor r).obj ((baseProductFunctor q).obj ((baseProductFunctor p).obj X)) :=
  (baseProductFunctor q).map (baseProductSwapMap r p X) ≫
    baseProductSwapMap r q ((baseProductFunctor p).obj X)

/-- The specified inverse word is the inverse of the original external move. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalTransport.lean:41"
  "adaptation" "Original two inverse index moves and all sixteen external transport cells."]
theorem externalInverse_eq_inv (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    externalInverse p q r X = inv (baseProductMoveExternal p q r X) := by
  let e := ((baseProductSwapIso q r).app ((baseProductFunctor p).obj X)) ≪≫
    (baseProductFunctor q).mapIso ((baseProductSwapIso p r).app X)
  change e.inv = inv e.hom
  exact IsIso.eq_inv_of_hom_inv_id e.hom_inv_id

/-- The opposite inverse word keeps the actual contravariant transport direction. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalTransport.lean:50"
  "adaptation" "Original two inverse index moves and all sixteen external transport cells."]
theorem externalInverse_op (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    (q : T ⟶ (Spec (.of (ULift.{u} ℤ))))
    (r : U ⟶ (Spec (.of (ULift.{u} ℤ)))) (X : Scheme.{u}) :
    (externalInverse p q r X).op = inv (baseProductMoveExternal p q r X).op := by
  rw [externalInverse_eq_inv]
  exact op_inv _

/-- The original two inverse index interchanges in their fixed recursive order. -/
@[colib_ref "quillen"
  "Quillen/KTheory/Bass/GeometricConeExternalTransport.lean:57"
  "adaptation" "Original two inverse index moves and all sixteen external transport cells."]
def externalTransport (r : U ⟶ (Spec (.of (ULift.{u} ℤ))))
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w}) :
    coneFunctor.obj (coneFunctor.obj ((baseProductFunctor r).op ⋙ F)) ⟶
      (baseProductFunctor r).op ⋙ coneFunctor.obj (coneFunctor.obj F) :=
  coneFunctor.map (eta r F).inv ≫ (eta r (coneFunctor.obj F)).inv

end KTheory.Bass.GeometricConeInterchange
