/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Scheme.IntegerBaseProductInterchange
public import Colib.AlgebraicGeometry.Scheme.QuasiCompactCategory

/-!
# Quasi-compact integer-base products and chart maps

Source: `Aglib/AlgebraicGeometry/Products/IntegerBase.lean` at
revision `2c34f185fa859e862661f939cd216b07bcccfb26`.
The original maps and proofs use the existing native full category of quasi-compact schemes.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.Products

/-- The actual product construction preserves quasi-compact objects when the fixed leg is qc. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Products/IntegerBase.lean:78"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
def qcBaseProductFunctor {S : AlgebraicGeometry.Scheme.{u}} (p : S ⟶ (Spec (.of (ULift.{u} ℤ))))
    [QuasiCompact p] :
    QuasiCompactSchemes.{u} ⥤ QuasiCompactSchemes.{u} where
  obj X := ⟨(baseProductFunctor p).obj X.obj, by
    dsimp [quasiCompactScheme, baseProductFunctor]
    infer_instance⟩
  map f := ⟨(baseProductFunctor p).map f.hom⟩
  map_id X := by apply ObjectProperty.hom_ext; exact (baseProductFunctor p).map_id _
  map_comp f g := by apply ObjectProperty.hom_ext; exact (baseProductFunctor p).map_comp _ _

/-- The induced map in the honest full category of quasi-compact schemes. -/
@[colib_ref "aglib"
  "Aglib/AlgebraicGeometry/Products/IntegerBase.lean:86"
  "adaptation" "Original native maps, full-subcategory lifts and chart equations."]
def qcBaseProductTransformation {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ (Spec (.of (ULift.{u} ℤ)))) (q : T ⟶ (Spec (.of (ULift.{u} ℤ)))) [QuasiCompact p]
    [QuasiCompact q]
    (f : S ⟶ T) (hf : f ≫ q = p) :
    qcBaseProductFunctor p ⟶ qcBaseProductFunctor q where
  app X := ⟨(baseProductTransformation p q f hf).app X.obj⟩
  naturality {X Y} g := by
    apply ObjectProperty.hom_ext
    exact (baseProductTransformation p q f hf).naturality g.hom


/-- The native interchange on the full subcategory of quasi-compact schemes. -/
def qcBaseProductSwapIso {S T : AlgebraicGeometry.Scheme.{u}}
    (p : S ⟶ Spec (.of (ULift.{u} ℤ))) (q : T ⟶ Spec (.of (ULift.{u} ℤ)))
    [QuasiCompact p] [QuasiCompact q] :
    qcBaseProductFunctor p ⋙ qcBaseProductFunctor q ≅
      qcBaseProductFunctor q ⋙ qcBaseProductFunctor p :=
  NatIso.ofComponents (fun X =>
    { hom := ⟨(baseProductSwapIso p q).hom.app X.obj⟩
      inv := ⟨(baseProductSwapIso p q).inv.app X.obj⟩
      hom_inv_id := by
        apply ObjectProperty.hom_ext
        exact ((baseProductSwapIso p q).app X.obj).hom_inv_id
      inv_hom_id := by
        apply ObjectProperty.hom_ext
        exact ((baseProductSwapIso p q).app X.obj).inv_hom_id })
    (fun f => by
      apply ObjectProperty.hom_ext
      exact (baseProductSwapIso p q).hom.naturality f.hom)


end AlgebraicGeometry.Scheme.Products
