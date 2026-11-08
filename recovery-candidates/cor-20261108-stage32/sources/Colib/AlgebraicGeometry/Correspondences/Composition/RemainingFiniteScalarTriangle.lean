/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Composition.RemainingFiniteResidueDegree

/-!
# Scalar germs for the actual whole finite model

The actual image-stalk algebra action on the whole finite coordinate ring is
`ΓSpecIso.inv` followed by the structure map on global sections. Taking its germ
at any model point is exactly the structure map on stalks following the same
`ΓSpecIso` and the base germ. This is the actual scalar triangle, directly from
native scheme germ naturality, before any localization-ring equivalence or
remaining Koszul list is transported.

No arbitrary algebra action, comparison witness, flat finite map, generic-point
hypothesis or reduced replacement is introduced. The closed-fibre specialization
and its comparison with the original ordered Z-list are subsequent steps.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
  (z : pullback (C := Scheme) f g) (w : pullback (C := Scheme) g h)
  (v : pullback (C := Scheme) h i)

/-- The canonical coordinate algebra followed by the actual germ is the literal
structure-stalk map after the base germ and the same native affine identification. -/
theorem correspondenceRemainingFiniteAlgebra_germ
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let R := correspondenceRemainingImageStalk f g h i z w v x
    let B := correspondenceRemainingFiniteRing f g h i z w v x
    let E := correspondenceRemainingFiniteModel f g h i z w v x
    let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
    ((E).presheaf.germ ⊤ q trivial).hom.comp (algebraMap R B) =
      (π.stalkMap q).hom.comp
        (((Spec R).presheaf.germ ⊤ (π q) trivial).hom.comp (Scheme.ΓSpecIso R).inv.hom) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  let R := correspondenceRemainingImageStalk f g h i z w v x
  let B := correspondenceRemainingFiniteRing f g h i z w v x
  let E := correspondenceRemainingFiniteModel f g h i z w v x
  let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
  have hα := correspondenceRemainingFiniteAlgebra_algebraMap f g h i z w v x
  ext a
  change (E).presheaf.germ ⊤ q trivial (algebraMap R B a) =
    π.stalkMap q ((Spec R).presheaf.germ ⊤ (π q) trivial ((Scheme.ΓSpecIso R).inv a))
  have ha : algebraMap R B a = π.appTop ((Scheme.ΓSpecIso R).inv a) :=
    congrArg (fun φ : R →+* B => φ a) hα
  rw [ha]
  exact (Scheme.Hom.germ_stalkMap_apply π ⊤ q trivial ((Scheme.ΓSpecIso R).inv a)).symm

/-- The unchanged ordered Z-list has the same actual stalk images along the two
canonical routes. No regularity hypothesis is needed for scalar compatibility. -/
theorem correspondenceRemainingFiniteAlgebra_germ_middleList
    (x : correspondenceLeftImageIncidence f g h i z w v)
    (q : correspondenceRemainingFiniteModel f g h i z w v x) {r : ℕ}
    (s : Fin r → (pullback (C := Scheme) h h).presheaf.stalk
      (correspondenceLeftImageMiddlePair f g h i z w v
        (correspondenceLeftImageIncidenceInclusion f g h i z w v x))) :
    let := correspondenceRemainingFiniteAlgebra f g h i z w v x
    let R := correspondenceRemainingImageStalk f g h i z w v x
    let B := correspondenceRemainingFiniteRing f g h i z w v x
    let E := correspondenceRemainingFiniteModel f g h i z w v x
    let π := correspondenceRemainingFiniteModelStructure f g h i z w v x
    let α := correspondenceRemainingImageMiddleStalkMap f g h i z w v x
    (fun j => (E).presheaf.germ ⊤ q trivial (algebraMap R B (α (s j)))) =
      (fun j => π.stalkMap q
        ((Spec R).presheaf.germ ⊤ (π q) trivial ((Scheme.ΓSpecIso R).inv (α (s j))))) := by
  let := correspondenceRemainingFiniteAlgebra f g h i z w v x
  exact congrArg (fun φ => fun j => φ
    (correspondenceRemainingImageMiddleStalkMap f g h i z w v x (s j)))
      (correspondenceRemainingFiniteAlgebra_germ f g h i z w v x q)

end Stacks.Chow
