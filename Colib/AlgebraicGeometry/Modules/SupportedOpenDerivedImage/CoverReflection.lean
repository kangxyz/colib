/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.OpenDerivedImage.TwoOpenGlue
public import Colib.AlgebraicGeometry.Modules.SupportedOpenDerivedImage.Basic

/-! # Reflection of supported extension over a two-open cover -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {V X : Scheme.{u}} (j : V ⟶ X) [IsOpenImmersion j] (T Z : X.Opens)

local notation "I₀" => Functor.obj (TopologicalSpace.Opens.map (PresheafedSpace.Hom.base
  (LocallyRingedSpace.Hom.toHom (Scheme.Hom.toLRSHom j)))) T
local notation "U" => Scheme.Opens.toScheme T
local notation "i" => Scheme.Opens.ι T
local notation "b" => Scheme.Opens.ι I₀
local notation "a" => Scheme.Hom.resLE j T I₀ le_rfl
local notation:max "F[" f "]" => CategoryTheory.Functor.mapDerivedCategory (restrictFunctor f)
local notation:max "R[" f "]" => CategoryTheory.Functor.mapHomologicalComplex
  (restrictFunctor f) (ComplexShape.up ℤ)

local instance supportedCoverOverlapOpen : IsOpenImmersion a := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

omit [IsOpenImmersion j] in
/-- The two induced auxiliary opens on the overlap agree literally. -/
theorem coverAuxiliaryPreimage_eq : a ⁻¹ᵁ (i ⁻¹ᵁ Z) = b ⁻¹ᵁ (j ⁻¹ᵁ Z) := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, j.resLE_comp_ι]

set_option maxHeartbeats 500000 in
-- Homology is tested at the corresponding stalk of each original restriction.
/-- Acyclicity on the auxiliary open can be checked after its two inverse-image restrictions. -/
theorem restrictAcyclic_of_cover (hcover : ∀ x : X, x ∈ Set.range j.base ∨ x ∈ T)
    (P : CochainComplex X.Modules ℤ)
    (hU : perfectSupported (i ⁻¹ᵁ Z).ι (R[i].obj P))
    (hV : perfectSupported (j ⁻¹ᵁ Z).ι (R[j].obj P)) :
    (R[Z.ι].obj P).Acyclic := by
  rw [restrictAcyclic_iff_stalkHomology]
  intro n z
  have transport {Y : Scheme.{u}} (k : Y ⟶ X) [IsOpenImmersion k]
      (h : perfectSupported (k ⁻¹ᵁ Z).ι (R[k].obj P))
      (y : Y) (hy : k y = z.val) :
      IsZero ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (Z.ι z)).obj
        (P.homology n)) := by
    let e := (P.sc n).mapHomologyIso (restrictFunctor k)
    have hz : y ∈ k ⁻¹ᵁ Z := by change k y ∈ Z; rw [hy]; exact z.property
    have hw := (restrictAcyclic_iff_stalkHomology (k ⁻¹ᵁ Z).ι (R[k].obj P)).1 h.2 n ⟨y, hz⟩
    let S := toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y
    have hS : IsZero (S.obj ((restrictFunctor k).obj (P.homology n))) :=
      ((S.mapIso e).isZero_iff).1 hw
    have h' := (((restrictStalkNatIso k y).app (P.homology n)).isZero_iff).1 hS
    change IsZero ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (k y)).obj
      (P.homology n)) at h'
    rw [hy] at h'
    exact h'
  rcases hcover z.val with ⟨y, hy⟩ | hy
  · exact transport j hV y hy
  · exact transport i hU ⟨z.val, hy⟩ rfl

set_option maxHeartbeats 500000 in
-- The canonical restriction factors are compared on the actual modules of the intersection.
/-- Extension of a supported perfect complex is reflected on the actual overlap. -/
theorem complexObjects_cover_iff
    (hcover : ∀ x : X, x ∈ Set.range j.base ∨ x ∈ T)
    (E : CochainComplex (U).Modules ℤ) (hE : perfectSupported (i ⁻¹ᵁ Z).ι E) :
    complexObjects i Z E ↔ complexObjects b (j ⁻¹ᵁ Z) (R[a].obj E) := by
  constructor
  · rintro ⟨P, hP, ⟨e⟩⟩
    let f := (restrictFunctor i).mapDerivedCategoryFactors.app P
    let g := (restrictFunctor j).mapDerivedCategoryFactors.app P
    let ea := (restrictFunctor a).mapDerivedCategoryFactors
    let eb := (restrictFunctor b).mapDerivedCategoryFactors
    refine ⟨R[j].obj P, perfectSupported_restrict j Z hP, ⟨?_⟩⟩
    exact (eb.app (R[j].obj P)).symm ≪≫ F[b].mapIso g.symm ≪≫
      ((OpenDerivedImage.coverReflectionRestrictionIso j T).app (DerivedCategory.Q.obj P)).symm ≪≫
      F[a].mapIso (f ≪≫ e) ≪≫ ea.app E
  · rintro ⟨B, hB, ⟨e⟩⟩
    obtain ⟨P, hP, ⟨ei⟩, ⟨ej⟩⟩ :=
      OpenDerivedImage.exists_perfect_of_overlap_iso j T hcover E B hE.1 hB.1 e
    have hi := (perfectSupported_iff_of_derivedIso (i ⁻¹ᵁ Z).ι ei).2 hE
    have hj := (perfectSupported_iff_of_derivedIso (j ⁻¹ᵁ Z).ι ej).2 hB
    exact ⟨P, ⟨hP, restrictAcyclic_of_cover j T Z hcover P hi hj⟩, ⟨ei⟩⟩

end AlgebraicGeometry.Scheme.Modules.SupportedOpenDerivedImage
