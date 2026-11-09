/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectDerivedRoof
public import Colib.Algebra.Homology.DerivedCategory.RoofModelComparison
public import Colib.Util.References
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect

/-!
# Native perfect roofs for a quasi-compact open in a qcqs scheme

Restriction is the derived functor of ordinary degreewise restriction. The source perfect
complex is obtained from compact generation of the restriction kernel, then represented by a
native perfect complex. Its two derived maps admit a common chain-map representative without
changing their target complexes.

The compact roof is the first clause of Stacks 08EH in the qcqs setting supplied by compact
kernel generation (0A9A) and compact/perfect comparison (09M1). No tensor presentation,
supported-source refinement, strict App2 or K-theory equivalence is asserted.
-/

attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.ObjectProperty
open Stacks.Duality.OpenImmersion Stacks.Duality.SupportedGeneration
open Stacks.Duality.QcqsGeneration

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X U : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j]

/-- A derived map from a restricted native perfect complex to a restricted complex with
quasi-coherent cohomology has a native perfect roof on the ambient qcqs scheme. -/
theorem exists_isPerfectComplex_derived_roof_of_qcqs
    (K E : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
      (DerivedCategory.Q.obj E)).IsQuasicoherent)
    (α : (derivedRestrict j).obj (DerivedCategory.Q.obj K) ⟶
      (derivedRestrict j).obj (DerivedCategory.Q.obj E)) :
    ∃ (R : CochainComplex X.Modules ℤ)
      (s : DerivedCategory.Q.obj R ⟶ DerivedCategory.Q.obj K)
      (t : DerivedCategory.Q.obj R ⟶ DerivedCategory.Q.obj E),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
        IsIso ((derivedRestrict j).map s) ∧
        (derivedRestrict j).map t = (derivedRestrict j).map s ≫ α := by
  have : QuasiSeparatedSpace U := j.isOpenEmbedding.quasiSeparatedSpace
  have : AlgebraicGeometry.QuasiCompact j := inferInstance
  have hKp : RingedSpace.IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj K) :=
    ⟨K, hK, ⟨Iso.refl _⟩⟩
  let K' : Stacks.Duality.quasiCoherentDerivedCategory X :=
    ⟨DerivedCategory.Q.obj K,
      isQuasicoherentDerived_of_isPseudoCoherent X _ hKp.isPseudoCoherent⟩
  let E' : Stacks.Duality.quasiCoherentDerivedCategory X := ⟨DerivedCategory.Q.obj E, hE⟩
  have : IsCompactObject.{u} K' :=
    Stacks.Duality.isCompactObject_of_isPerfect K' hKp
  let α' : (restrictedDerivedRestrict j).obj K' ⟶
      (restrictedDerivedRestrict j).obj E' := ObjectProperty.homMk α
  obtain ⟨ι, G, hGc, hG0, hGdet⟩ := kernelDetected j
  obtain ⟨c, s, t, hc, hs, ht⟩ := exists_roof
    (restrictedDerivedRestrictAdjunction j) G hGc hG0 hGdet α'
  have hp : RingedSpace.IsPerfect (X := X.toRingedSpace) c.obj :=
    Stacks.Duality.isPerfect_of_isCompactObject c hc
  change ∃ R : CochainComplex X.Modules ℤ,
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      Nonempty (DerivedCategory.Q.obj R ≅ c.obj) at hp
  obtain ⟨R, hR, ⟨e⟩⟩ := hp
  let ιU := (DerivedCategoryB.derivedCategoryB (A := U.Modules)
    (SheafOfModules.isQuasicoherent U.ringCatSheaf)).ι
  have hs' : IsIso ((derivedRestrict j).map s.hom) :=
    ιU.map_isIso ((restrictedDerivedRestrict j).map s)
  refine ⟨R, e.hom ≫ s.hom, e.hom ≫ t.hom, hR, ?_, ?_⟩
  · rw [Functor.map_comp]
    infer_instance
  · change (derivedRestrict j).map (e.hom ≫ t.hom) =
      (derivedRestrict j).map (e.hom ≫ s.hom) ≫ α
    simp only [Functor.map_comp, Category.assoc]
    exact congrArg ((derivedRestrict j).map e.hom ≫ ·) (congrArg (fun f => f.hom) ht)

/-- The native qcqs roof with actual chain maps and the original restricted derived map.
This is a roof, not an outgoing strict approximation factorization. -/
theorem exists_isPerfectComplex_chainMap_roof_of_qcqs_small
    (K E : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
      (DerivedCategory.Q.obj E)).IsQuasicoherent)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :
    ∃ (R : CochainComplex X.Modules ℤ) (q : R ⟶ K) (a : R ⟶ E),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map a) := by
  let e := (restrictFunctor j).mapDerivedCategoryFactors
  obtain ⟨R, s, t, hR, hs, ht⟩ := exists_isPerfectComplex_derived_roof_of_qcqs j K E hK hE
    (e.hom.app K ≫ α ≫ e.inv.app E)
  refine exists_isPerfectComplex_chainMap_roof j hR s t α hs ?_
  rw [ht]
  simp [e, Category.assoc]

section AnyModel

universe d

/-- Every restricted derived morphism from a global native perfect complex to a complex with
quasi-coherent cohomology has an actual chain-map roof with native perfect source, for any
chosen derived-category model on the open. The denominator need only be a quasi-isomorphism
on the open. Neither target complex is replaced. -/
@[colib_tag "COL-0307",
  stacks 08EH "The first roof assertion, generalized to qcqs schemes through compact kernel \
    generation; no tensor presentation or supported-source clause"]
theorem exists_isPerfectComplex_chainMap_roof_of_qcqs
    [h : HasDerivedCategory.{d} U.Modules]
    (K E : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K)
    (hE : ∀ i : ℤ,
      ((HomologicalComplex.homologyFunctor X.Modules (ComplexShape.up ℤ) i).obj E).IsQuasicoherent)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :
    ∃ (R : CochainComplex X.Modules ℤ) (q : R ⟶ K) (a : R ⟶ E),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map a) := by
  let Q₁ := @DerivedCategory.Q U.Modules _ _ h
  let Q₂ := @DerivedCategory.Q U.Modules _ _ (Scheme.Modules.hasDerivedCategory U)
  let W := HomologicalComplex.quasiIso U.Modules (ComplexShape.up ℤ)
  let e := Localization.compUniqFunctor Q₁ Q₂ W
  let F := (Localization.uniq Q₁ Q₂ W).functor
  let r := (restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)
  let β := e.inv.app (r.obj K) ≫ F.map α ≫ e.hom.app (r.obj E)
  have hE' : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
      (DerivedCategory.Q.obj E)).IsQuasicoherent := fun i =>
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.homologyFunctorFactors X.Modules i).app E).symm (hE i)
  obtain ⟨R, q, a, hR, hq, ha⟩ :=
    exists_isPerfectComplex_chainMap_roof_of_qcqs_small j K E hK hE' β
  refine ⟨R, q, a, hR, hq, ?_⟩
  exact (DerivedCategory.comp_eq_iff_of_model h (Scheme.Modules.hasDerivedCategory U)
    (r.map q) (r.map a) α).2 ha

/-- The native analogue of the original global perfect roof theorem: both fixed target
complexes are perfect, and no cohomology or roof premise needs to be supplied. -/
theorem exists_isPerfectComplex_chainMap_roof_of_perfect
    [h : HasDerivedCategory.{d} U.Modules]
    (K E : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K)
    (hE : RingedSpace.IsPerfectComplex (X := X.toRingedSpace) E)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj E)) :
    ∃ (R : CochainComplex X.Modules ℤ) (q : R ⟶ K) (a : R ⟶ E),
      RingedSpace.IsPerfectComplex (X := X.toRingedSpace) R ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map a) := by
  have hp : RingedSpace.IsPerfect (X := X.toRingedSpace) (DerivedCategory.Q.obj E) :=
    ⟨E, hE, ⟨Iso.refl _⟩⟩
  have hEqc := isQuasicoherentDerived_of_isPseudoCoherent X _ hp.isPseudoCoherent
  exact exists_isPerfectComplex_chainMap_roof_of_qcqs j K E hK (fun i =>
    ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
      ((DerivedCategory.homologyFunctorFactors X.Modules i).app E) (hEqc i)) α

end AnyModel

end AlgebraicGeometry.Scheme.Modules
