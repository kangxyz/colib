/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Util.References

public import Colib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Original quasi-compact ambient open pairs
Only the original object property, full subcategory and compactness instance are selected.
The ambient category is the existing native open-pair category, not a perfect-complex model.
-/
@[expose] public section
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme
/-- The property that the ambient scheme of an open pair is quasi-compact; no quasi-compactness
condition is imposed on its open subscheme. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Morphisms/OpenImmersion/Pair/Basic.lean:37"
  "adaptation" "Original compact-ambient open-pair property on native open pairs."]
abbrev quasiCompactOpenPairProperty : ObjectProperty OpenPairs.{u} :=
  fun X => CompactSpace X.right

/-- The full category of open pairs with quasi-compact ambient scheme, retaining all commutative
squares between such pairs. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Morphisms/OpenImmersion/Pair/Basic.lean:42"
  "adaptation" "Original compact-ambient open-pair property on native open pairs."]
abbrev QuasiCompactOpenPairs := quasiCompactOpenPairProperty.{u}.FullSubcategory

/-- The original ambient compactness property supplies this instance. -/
@[colib_ref "quillen" "Quillen/Aglib/AlgebraicGeometry/Morphisms/OpenImmersion/Pair/Basic.lean:44"
  "adaptation" "Original compact-ambient open-pair property on native open pairs."]
instance quasiCompactOpenPairs_compactSpace (X : QuasiCompactOpenPairs.{u}) :
    CompactSpace ((𝟭 Scheme).obj X.obj.right) := X.property

end AlgebraicGeometry.Scheme
