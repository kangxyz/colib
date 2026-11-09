/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedRestriction

/-!
# The union neighborhood for supported open restriction

The union of the image open and the vanishing open is an actual open subscheme.
Restriction compositions and support transport use the native module sheaves and their
homology stalks. No compactness is imposed on these transport statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)

/-- The original open immersion factors through its union with the vanishing open. -/
def supportedUnionLift : U ⟶ (j.opensRange ⊔ T).toScheme :=
  IsOpenImmersion.lift (j.opensRange ⊔ T).ι j (by
    rintro x ⟨y, rfl⟩
    exact ⟨⟨j y, Or.inl ⟨y, rfl⟩⟩, rfl⟩)

instance : IsOpenImmersion (supportedUnionLift j T) := by
  unfold supportedUnionLift
  infer_instance

@[reassoc (attr := simp)]
theorem supportedUnionLift_ι : supportedUnionLift j T ≫ (j.opensRange ⊔ T).ι = j :=
  IsOpenImmersion.lift_fac _ _ _

/-- The image of the factored immersion and the inverse-image vanishing open cover. -/
theorem supportedUnionLift_cover (x : (j.opensRange ⊔ T).toScheme) :
    x ∈ Set.range (supportedUnionLift j T) ∨ x ∈ (j.opensRange ⊔ T).ι ⁻¹ᵁ T := by
  rcases x.property with hx | hx
  · left
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, ?_⟩
    apply (j.opensRange ⊔ T).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, supportedUnionLift_ι]
    change j y = x.val
    exact hy
  · exact Or.inr hx

/-- The native complex restriction comparison for the actual union factorization. -/
def supportedUnionRestrictIso :
    (restrictFunctor (j.opensRange ⊔ T).ι).mapHomologicalComplex (.up ℤ) ⋙
        (restrictFunctor (supportedUnionLift j T)).mapHomologicalComplex (.up ℤ) ≅
      (restrictFunctor j).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso
    ((restrictFunctorComp (supportedUnionLift j T) (j.opensRange ⊔ T).ι).symm ≪≫
      restrictFunctorCongr (supportedUnionLift_ι j T)) (.up ℤ)

/-- Support can be detected after restricting to any open containing the vanishing open. -/
theorem restrictAcyclic_preimage_iff_of_le (W : X.Opens) (hTW : T ≤ W)
    (K : CochainComplex X.Modules ℤ) :
    (((restrictFunctor (W.ι ⁻¹ᵁ T).ι).mapHomologicalComplex (.up ℤ)).obj
        (((restrictFunctor W.ι).mapHomologicalComplex (.up ℤ)).obj K)).Acyclic ↔
      (((restrictFunctor T.ι).mapHomologicalComplex (.up ℤ)).obj K).Acyclic := by
  constructor
  · intro h
    rw [restrictAcyclic_iff_stalkHomology] at h ⊢
    intro n x
    let y : W := ⟨x.val, hTW x.property⟩
    have hy : y ∈ W.ι ⁻¹ᵁ T := x.property
    let e : (((restrictFunctor W.ι).mapHomologicalComplex (.up ℤ)).obj K).homology n ≅
        (restrictFunctor W.ι).obj (K.homology n) :=
      (K.sc n).mapHomologyIso (restrictFunctor W.ι)
    let F := toPresheaf W.toScheme ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    have hz : IsZero (F.obj ((restrictFunctor W.ι).obj (K.homology n))) :=
      ((F.mapIso e).isZero_iff).1 (h n ⟨y, hy⟩)
    exact (((restrictStalkNatIso W.ι y).app (K.homology n)).isZero_iff).1 hz
  · exact restrictAcyclic_preimage W.ι T K

/-- A denominator that is a quasi-isomorphism on a neighborhood of the vanishing open
transports the support of its target to its source. -/
theorem restrictAcyclic_of_quasiIso_on_neighborhood (W : X.Opens) (hTW : T ≤ W)
    {R A : CochainComplex X.Modules ℤ} (q : R ⟶ A)
    (hq : QuasiIso (((restrictFunctor W.ι).mapHomologicalComplex (.up ℤ)).map q))
    (hA : (((restrictFunctor T.ι).mapHomologicalComplex (.up ℤ)).obj A).Acyclic) :
    (((restrictFunctor T.ι).mapHomologicalComplex (.up ℤ)).obj R).Acyclic := by
  apply (restrictAcyclic_preimage_iff_of_le T W hTW R).1
  let := hq
  let r := (restrictFunctor (W.ι ⁻¹ᵁ T).ι).mapHomologicalComplex (.up ℤ)
  have hA' := restrictAcyclic_preimage W.ι T A hA
  intro n
  exact (exactAt_iff_of_quasiIsoAt
    (r.map (((restrictFunctor W.ι).mapHomologicalComplex (.up ℤ)).map q)) n).2 (hA' n)

/-- A compact original open and compact vanishing open have compact union. -/
theorem isCompact_supportedUnion [CompactSpace U] (hT : IsCompact (T : Set X)) :
    IsCompact ((j.opensRange ⊔ T : X.Opens) : Set X) :=
  (isCompact_range j.continuous).union hT

end AlgebraicGeometry.Scheme.Modules
