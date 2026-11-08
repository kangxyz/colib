/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.SupportedDerivedLift
public import Colib.AlgebraicGeometry.Modules.SupportedUnionGeometry
public import Colib.AlgebraicGeometry.Modules.PerfectQcqsRoof

/-!
# Native supported perfect roofs on qcqs schemes

A local fraction extends on the union of the image open and the vanishing open. The
ordinary perfect roof theorem applies to the original global target complexes. Its
denominator is invertible on that union, so the source has the required support.
-/

attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u d

variable {U X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace U]
  (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

omit [CompactSpace U] in
/-- A supported global perfect source and any fixed global target with quasi-coherent
homology admit a supported perfect roof for every local derived arrow. Compactness of
the union neighborhood is the precise additional finiteness hypothesis. -/
theorem exists_perfectSupported_chainMap_roof_of_union_compact
    [HasDerivedCategory.{d} U.Modules]
    (hW : IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X))
    (A B : CochainComplex X.Modules ℤ) (hA : perfectSupported T.ι A)
    (hB : ∀ n : ℤ,
      ((HomologicalComplex.homologyFunctor X.Modules (.up ℤ) n).obj B).IsQuasicoherent)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj A) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj B)) :
    ∃ (R : CochainComplex X.Modules ℤ) (q : R ⟶ A) (a : R ⟶ B),
      perfectSupported T.ι R ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map a) := by
  let W := j.opensRange ⊔ T
  let i := W.ι
  let k := supportedUnionLift j T
  let r := (restrictFunctor i).mapHomologicalComplex (.up ℤ)
  let s := (restrictFunctor k).mapHomologicalComplex (.up ℤ)
  let e := supportedUnionRestrictIso j T
  let : CompactSpace W := isCompact_iff_compactSpace.mp hW
  let αk := DerivedCategory.Q.map (e.hom.app A) ≫ α ≫
    DerivedCategory.Q.map (e.inv.app B)
  obtain ⟨β, hβ⟩ := exists_supported_derived_lift k (i ⁻¹ᵁ T)
    (supportedUnionLift_cover j T) (r.obj A) (r.obj B)
    (perfectSupported_restrict i T hA) αk
  obtain ⟨R, q, a, hR, hq, ha⟩ :=
    exists_isPerfectComplex_chainMap_roof_of_qcqs i A B hA.1 hB β
  let := hq
  have he := restrict_derived_roof_equation k (r.map q) (r.map a) β ha
  rw [hβ] at he
  have hq' : QuasiIso ((r ⋙ s).map q) := by dsimp; infer_instance
  refine ⟨R, q, a, ⟨hR,
    restrictAcyclic_of_quasiIso_on_neighborhood T W le_sup_right q hq hA.2⟩, ?_, ?_⟩
  · exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso e (Arrow.mk q))).1 hq'
  · apply (cancel_epi (DerivedCategory.Q.map (e.hom.app R))).1
    have hn := congrArg DerivedCategory.Q.map (e.hom.naturality q)
    have hn' := congrArg DerivedCategory.Q.map (e.hom.naturality a)
    simp only [Functor.map_comp] at hn hn'
    rw [← Category.assoc, ← hn]
    have hh := congrArg (· ≫ DerivedCategory.Q.map (e.hom.app B)) he
    have hid : DerivedCategory.Q.map (e.inv.app B) ≫
        DerivedCategory.Q.map (e.hom.app B) = 𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app]
      exact DerivedCategory.Q.map_id _
    simp only [αk, Category.assoc, hid, Category.comp_id] at hh
    simpa only [Functor.comp_map, Category.assoc] using hh.trans hn'

/-- Compactness of the vanishing open suffices for the supported qcqs roof. -/
@[colib_tag "COL-0333"]
theorem exists_perfectSupported_chainMap_roof_of_qcqs
    [HasDerivedCategory.{d} U.Modules] (hT : IsCompact (T : Set X))
    (A B : CochainComplex X.Modules ℤ) (hA : perfectSupported T.ι A)
    (hB : ∀ n : ℤ,
      ((HomologicalComplex.homologyFunctor X.Modules (.up ℤ) n).obj B).IsQuasicoherent)
    (α : DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj A) ⟶
      DerivedCategory.Q.obj
        (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).obj B)) :
    ∃ (R : CochainComplex X.Modules ℤ) (q : R ⟶ A) (a : R ⟶ B),
      perfectSupported T.ι R ∧
      QuasiIso (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q) ∧
      DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map q) ≫ α =
        DerivedCategory.Q.map
          (((restrictFunctor j).mapHomologicalComplex (.up ℤ)).map a) :=
  exists_perfectSupported_chainMap_roof_of_union_compact j T
    (isCompact_supportedUnion j T hT) A B hA hB α

end AlgebraicGeometry.Scheme.Modules
