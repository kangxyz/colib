/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Bass.TwoChart
public import Colib.Util.References

/-!
Source: `Quillen/KTheory/Bass/TwoChartMapIso.lean`,
revision `c561118b7795eb9780be9ed391c3251d6a4d0afd`.

# Pointwise isomorphisms of original Bass quotient maps

The original induced cokernel map is invertible at an object when the given
natural transformation is invertible at its polynomial and Laurent objects.
Two iterations need only the four chart components. No globally invertible
natural transformation or additive source functor is required.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace KTheory.Bass.TwoChart
variable {D : Type u} [Category.{w} D] {P L : D ⥤ D} (p m : P ⟶ L)

/-- Two pointwise chart isomorphisms make the original cokernel map invertible. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/TwoChartMapIso.lean:26"
  "adaptation" "Original cokernel maps from two or four pointwise chart isomorphisms."]
theorem isIso_contractionMap_app {F G : D ⥤ AddCommGrpCat.{v}} (α : F ⟶ G) (X : D)
    [IsIso (α.app (P.obj X))] [IsIso (α.app (L.obj X))] :
    IsIso ((contractionMap p m α).app X) := by
  let t := (polynomialDifferenceTransformation p m α).app X
  have : IsIso t.left := by
    change IsIso (biprod.mapIso (asIso (α.app (P.obj X)))
      (asIso (α.app (P.obj X)))).hom
    infer_instance
  have : IsIso t.right := by
    change IsIso (α.app (L.obj X))
    infer_instance
  have : IsIso t := Arrow.isIso_of_isIso_left_of_isIso_right t
  change IsIso ((coker AddCommGrpCat).map t)
  infer_instance

/-- Four actual chart isomorphisms suffice for the twice-induced original quotient map. -/
@[colib_ref "quillen" "Quillen/KTheory/Bass/TwoChartMapIso.lean:42"
  "adaptation" "Original cokernel maps from two or four pointwise chart isomorphisms."]
theorem isIso_doubleContractionMap_app {F G : D ⥤ AddCommGrpCat.{v}}
    (α : F ⟶ G) (X : D)
    [IsIso (α.app (P.obj (P.obj X)))] [IsIso (α.app (L.obj (P.obj X)))]
    [IsIso (α.app (P.obj (L.obj X)))] [IsIso (α.app (L.obj (L.obj X)))] :
    IsIso ((contractionMap p m (contractionMap p m α)).app X) := by
  have := isIso_contractionMap_app p m α (P.obj X)
  have := isIso_contractionMap_app p m α (L.obj X)
  exact isIso_contractionMap_app p m (contractionMap p m α) X

end KTheory.Bass.TwoChart
