/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Properties.Discrete.ResidueFields
public import StacksFrontier.RingTheory.Smooth.GeometricallyReducedFibres
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure

/-!
Adapted from motivic@a6805c4a87cdfd7717dd7a94039246a167f15380,
`Motivic/Aglib/AlgebraicGeometry/Morphisms/Etale/Fibers/ResidueFieldMap.lean`, blob `25212e71687abf5cb30794b71b1dc6e19d4327be`.


# Étale residue-field maps

The actual residue-field map of an arbitrary étale scheme morphism is étale.
No closedness or rationality condition is imposed on the point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- The residue-field point of an étale fiber is an open immersion. -/
instance isOpenImmersion_asFiberHom_of_etale (f : X ⟶ Y) [Etale f] (x : X) :
    IsOpenImmersion (f.asFiberHom x) := by
  have : Etale (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (Etale (pullback.snd f (Y.fromSpecResidueField (f x))))
  have : Smooth (f.fiberToSpecResidueField (f x)) := inferInstance
  have : LocallyQuasiFinite f := by
    constructor
    intro U hU V hV e
    have h := f.etale_appLE hU hV e
    algebraize [(f.appLE U V e).hom]
    exact RingHom.quasiFinite_algebraMap.mpr inferInstance
  have : DiscreteTopology (f.fiber (f x)) := inferInstance
  have : IsReduced (f.fiber (f x)) := by
    have := AlgebraicGeometry.geometricallyReduced_of_smooth
      (f.fiberToSpecResidueField (f x))
    exact AlgebraicGeometry.GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian
      (f.fiberToSpecResidueField (f x))
  apply IsOpenImmersion.iff_isIso_stalkMap.mpr
  refine ⟨.of_continuous_injective_isOpenMap (f.asFiberHom x).continuous
    (f.asFiberHom x).isEmbedding.injective (fun _ _ ↦ isOpen_discrete _), ?_⟩
  intro z
  let : Field ((f.fiber (f x)).presheaf.stalk (f.asFiberHom x z)) :=
    (Scheme.isField_stalk_of_discrete _).toField
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨(f.asFiberHom x).stalkMap z |>.hom.injective,
    (f.asFiberHom x).stalkMap_surjective z⟩

/-- The literal induced map on residue-field spectra of an étale morphism is étale. -/
instance etale_specMap_residueFieldMap (f : X ⟶ Y) [Etale f] (x : X) :
    Etale (Spec.map (f.residueFieldMap x)) := by
  have : Etale (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (Etale (pullback.snd f (Y.fromSpecResidueField (f x))))
  rw [← f.asFiberHom_fiberToSpecResidueField x]
  infer_instance

end AlgebraicGeometry.Scheme.Hom

