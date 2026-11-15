/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.MotivicCohomology.TransferParameterUnderlying
public import Colib.AlgebraicGeometry.MotivicCohomology.Finite.EtaleChangeOfTopology

/-! # Change of topology on the original signed parameter comparison

This compares the two existing parameter maps after étale sheafification.
The target is the sheafification of Nisnevich torus sections, not an asserted
étale torus-sections or tensor comparison. The original target retains its
weight `q + 1` and its additional shift by one.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.PresheafWithTransfers

variable (k : Type u) [Field k]

/-- Étale sheafification preserves the comparison of the original signed
transfer parameter map with the ordinary motivic bonding map. No commutation
of sheafification with torus sections is asserted. -/
theorem motivicTransferParameterProduct_etale_underlying (q : ℕ) :
    let U := (SheafWithTransfers.toSheaf k).mapHomologicalComplex (.up ℤ)
    let E := (SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)
    let φ := NatIso.mapHomologicalComplex
      (SheafWithTransfers.torusSectionsToSheafIso k) (.up ℤ)
    E.map (U.map (motivicTransferParameterProduct k q)) ≫
      E.map (φ.hom.app ((motivicComplex k (q + 1))⟦(1 : ℤ)⟧)) =
        E.map (motivicSheafParameterProduct k q) := by
  intro U E φ
  exact (E.map_comp _ _).symm.trans
    (E.congr_map (motivicTransferParameterProduct_underlying k q))

/-- The topology-changed ordinary parameter map retains the exact native signed
shift formula: `s = -q`, `t = -(q+1)`, and `t + 1 = s`. The functor is left
outside the shifts; no extra commutation comparison is silently inserted. -/
theorem motivicSheafParameterProduct_etale_signed (q : ℕ) :
    let E := (SmoothSite.nisnevichToEtaleSheaf (Spec (CommRingCat.of k))
      AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)
    let F := torusParameterSheafFunctor k
    let H := F.mapHomologicalComplex (.up ℤ)
    let e := ComplexShape.embeddingUpIntLE 0
    let N := (AlgebraicSimplex.sheafifiedSingularChainsFunctor k
      (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k)))).obj
        ((toPresheaf k).obj (reducedTorus k (q + 1)))
    let s := -(q : ℤ)
    let t := -((q + 1 : ℕ) : ℤ)
    let hs : t + 1 = s := by dsimp [s, t]; omega
    let f := (e.extendFunctor _).map (sheafifiedReducedTorusSingularParameterProduct k q) ≫
      (Stacks.DerivedIndexing.mapExtendIso F e N).hom
    E.map (motivicSheafParameterProduct k q) =
      E.map (motivicSheafComplexOrdinaryShiftIso k q).hom ≫
        E.map ((shiftFunctor _ s).map f) ≫
        E.map ((H.commShiftIso s).inv.app (N.extend e)) ≫
        E.map (H.map ((shiftFunctorAdd' _ t 1 s hs).hom.app (N.extend e) ≫
          (shiftFunctor _ (1 : ℤ)).map
            (motivicSheafComplexOrdinaryShiftIso k (q + 1)).inv)) := by
  intro E F H e N s t hs f
  rw [motivicSheafParameterProduct_eq]
  simp only [E.map_comp]
  rfl

end AlgebraicGeometry.PresheafWithTransfers
