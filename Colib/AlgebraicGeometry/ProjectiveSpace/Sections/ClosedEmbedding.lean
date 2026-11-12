/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveSpace.Sections.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemeBaseChange.PullbackSections

/-!
# Prescribed sections along a projective closed embedding

The canonical projection formula transports Serre lifting to the tensor product with the
pulled-back projective twist. All maps are native sheaf morphisms. The presentation is a
closed embedding, not an arbitrary finite morphism. The boundary is the original closed
subscheme, including its nilpotents. No regularity or flatness of zero schemes is asserted.

The proof follows the section-lifting strategy of the 2026-10-21 Motivic checkpoint,
`Aglib/AlgebraicGeometry/Cohomology/Projective/SectionLifting/FiniteMap.lean`, with the native
Stacks tensor, adjunction, and global-section maps.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistFunctor
open Stacks.AffineProjectionFormula

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] ProjectiveSpectrum.top AlgebraicGeometry.Proj
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensoring on the right by the pullback of the projective twist. -/
abbrev pullbackTwistFunctor (R : Type u) [CommRing R] (n : ℕ)
    {X : Scheme.{u}} (f : X ⟶ Proj (polyGrading R n)) (d : ℤ) : X.Modules ⥤ X.Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj
    ((pullback f).obj (twistingSheaf (polyGrading R n) d))

set_option maxHeartbeats 800000 in
-- The two native tensor presentations require substantial definitional comparison.
/-- Quotient sections of pulled-back twists lift uniformly along a projective closed
embedding. The map is the actual tensor of the quotient map, not a chosen presentation. -/
theorem exists_surjective_pullbackTwist_pushforward_evaluation_of_coherent_epi
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {X : Scheme.{u}} (f : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion f]
    {M N : X.Modules} [M.IsCoherent] [N.IsCoherent] (φ : M ⟶ N) [Epi φ] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d → Function.Surjective
      (Hom.app ((pushforward f).map ((pullbackTwistFunctor R n f d).map φ)) ⊤) := by
  obtain ⟨B, hB⟩ := exists_surjective_twisted_pushforward_evaluation_of_coherent_epi R n f φ
  refine ⟨B, fun d hd s => ?_⟩
  let E := twistingSheaf (polyGrading R n) d
  let eM := closedImmersionProjectionFormulaIso f M E
  let eN := closedImmersionProjectionFormulaIso f N E
  obtain ⟨t, ht⟩ := hB d hd (Hom.app eN.inv ⊤ s)
  refine ⟨Hom.app eM.hom ⊤ t, ?_⟩
  let M' : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace) := M
  let N' : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf X.toRingedSpace) := N
  let φ' : M' ⟶ N' := φ
  let E' : SheafOfModules.{u}
      (Stacks.RingedSpace.structureRingSheaf (Proj (polyGrading R n)).toRingedSpace) := E
  have hn := projectionFormulaMap_natural f.toLRSHom.toShHom φ' (𝟙 E')
  simp only [Functor.uncurry_obj_map] at hn
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hn
  have hh := congrArg (fun ψ => ψ.val.app (op ⊤) t) hn
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app] at hh
  change Hom.app eN.hom ⊤
      (((twistFunctor (polyGrading R n) d).map ((pushforward f).map φ)).val.app (op ⊤) t) =
    Hom.app ((pushforward f).map ((pullbackTwistFunctor R n f d).map φ)) ⊤
      (Hom.app eM.hom ⊤ t) at hh
  exact hh.symm.trans ((congrArg (fun z => Hom.app eN.hom ⊤ z) ht).trans (by
    have hi := congrArg (fun ψ => ψ.val.app (op ⊤) s) eN.inv_hom_id
    exact hi))


/-- Surjectivity of the tensorized closed-boundary unit implies surjectivity of the actual
restriction map of the tensor product, via the canonical projection formula. -/
theorem surjective_pullbackGlobalSections_tensor_of_surjective_tensor_unit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M H : X.Modules)
    (h : Function.Surjective (Hom.app
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj H).map
        ((pullbackPushforwardAdjunction i).unit.app M)) ⊤)) :
    Function.Surjective (pullbackGlobalSections i
      (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj H).obj M)) := by
  let T := ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj H).obj M
  let e := closedImmersionProjectionFormulaIso i ((pullback i).obj M) H
  let c := (Stacks.RingedSpace.comparisonNatTrans i.toLRSHom.toShHom).app (M, H)
  have hc : IsIso c := Stacks.RingedSpace.comparisonNatTrans_app_isIso _ _
  let q := (pushforward i).map c
  have : IsIso q := ((pushforward i).mapIso (@asIso _ _ _ _ c hc)).isIso_hom
  have hq := ConcreteCategory.bijective_of_isIso (Hom.app q ⊤)
  intro s
  obtain ⟨t, ht⟩ := h (Hom.app e.inv ⊤ (Hom.app q ⊤ s))
  refine ⟨t, ?_⟩
  rw [pullbackGlobalSections_eq_unit]
  apply hq.injective
  have hn := closedImmersionProjectionFormulaIso_hom_natural_unit i M H
  change _ = (pullbackPushforwardAdjunction i).unit.app T ≫ q at hn
  simp only [Functor.uncurry_obj_map] at hn
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at hn
  have hh := congrArg (fun ψ => Hom.app ψ ⊤ t) hn
  change Hom.app e.hom ⊤
    (Hom.app (((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.obj H).map
      ((pullbackPushforwardAdjunction i).unit.app M)) ⊤ t) = _ at hh
  rw [ht] at hh
  exact hh.symm.trans (by
    have hi := congrArg (fun ψ => ψ.val.app (op ⊤) (Hom.app q ⊤ s)) e.inv_hom_id
    exact hi)


/-- Prescribed values on the whole closed boundary lift to actual global sections after a
uniform twist bound, for a projective closed embedding over a noetherian base. -/
@[colib_tag "COL-1044", stacks 01YS
  "full closed-boundary section lifting via Serre vanishing and a projective closed embedding"]
theorem exists_surjective_pullbackGlobalSections_pullbackTwist
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {X Z : Scheme.{u}} (f : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion f]
    (i : Z ⟶ X) [IsClosedImmersion i] (M : X.Modules) [M.IsCoherent] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d → Function.Surjective
      (pullbackGlobalSections i ((pullbackTwistFunctor R n f d).obj M)) := by
  have : IsLocallyNoetherian X := isLocallyNoetherian_of_isClosedImmersion f
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have : ((pullback i).obj M).IsCoherent := isCoherent_pullback i M
  have : ((pushforward i).obj ((pullback i).obj M)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i _
  have : ((𝟭 X.Modules).obj M).IsCoherent := inferInstanceAs M.IsCoherent
  have : ((pullback i ⋙ pushforward i).obj M).IsCoherent :=
    inferInstanceAs ((pushforward i).obj ((pullback i).obj M)).IsCoherent
  have := Stacks.ClosedImmersion.epi_unit_app i M
  obtain ⟨B, hB⟩ := exists_surjective_pullbackTwist_pushforward_evaluation_of_coherent_epi
    R n f ((pullbackPushforwardAdjunction i).unit.app M)
  refine ⟨B, fun d hd => ?_⟩
  apply surjective_pullbackGlobalSections_tensor_of_surjective_tensor_unit
  have h := hB d hd
  change Function.Surjective
    (Hom.app ((pullbackTwistFunctor R n f d).map
      ((pullbackPushforwardAdjunction i).unit.app M)) (f ⁻¹ᵁ ⊤)) at h
  rw [Scheme.Hom.preimage_top] at h
  exact h

/-- Two coherent modules admit simultaneous prescribed full-boundary sections for every twist
past one common bound. The lifted global sections are produced, not assumed. -/
@[colib_tag "COL-1044", stacks 01YS
  "simultaneous full closed-boundary section lifting with a common Serre bound"]
theorem exists_prescribed_boundary_section_pair
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {X Z : Scheme.{u}} (f : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion f]
    (i : Z ⟶ X) [IsClosedImmersion i] (M N : X.Modules)
    [M.IsCoherent] [N.IsCoherent] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d →
      ∀ (s : Γ((pullback i).obj ((pullbackTwistFunctor R n f d).obj M), ⊤))
        (t : Γ((pullback i).obj ((pullbackTwistFunctor R n f d).obj N), ⊤)),
      ∃ (a : Γ((pullbackTwistFunctor R n f d).obj M, ⊤))
        (b : Γ((pullbackTwistFunctor R n f d).obj N, ⊤)),
        pullbackGlobalSections i _ a = s ∧ pullbackGlobalSections i _ b = t := by
  obtain ⟨BM, hM⟩ := exists_surjective_pullbackGlobalSections_pullbackTwist R n f i M
  obtain ⟨BN, hN⟩ := exists_surjective_pullbackGlobalSections_pullbackTwist R n f i N
  refine ⟨max BM BN, fun d hd s t => ?_⟩
  obtain ⟨a, ha⟩ := hM d (le_trans (le_max_left _ _) hd) s
  obtain ⟨b, hb⟩ := hN d (le_trans (le_max_right _ _) hd) t
  exact ⟨a, b, ha, hb⟩

/-- Frames on the full boundary produce two global sections whose boundary frame coordinates
are literally one. These equations include every nilpotent of the boundary. -/
@[colib_tag "COL-1044", stacks 01YS
  "literal boundary frame equations for the two sections produced by Serre lifting"]
theorem exists_boundary_framed_section_pair
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {X Z : Scheme.{u}} (f : X ⟶ Proj (polyGrading R n)) [IsClosedImmersion f]
    (i : Z ⟶ X) [IsClosedImmersion i] (M N : X.Modules)
    [M.IsCoherent] [N.IsCoherent] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d →
      ∀ (eM : (pullback i).obj ((pullbackTwistFunctor R n f d).obj M) ≅
          SheafOfModules.unit Z.ringCatSheaf)
        (eN : (pullback i).obj ((pullbackTwistFunctor R n f d).obj N) ≅
          SheafOfModules.unit Z.ringCatSheaf),
      ∃ (a : Γ((pullbackTwistFunctor R n f d).obj M, ⊤))
        (b : Γ((pullbackTwistFunctor R n f d).obj N, ⊤)),
        Hom.app eM.hom ⊤ (pullbackGlobalSections i _ a) = (1 : Γ(Z, ⊤)) ∧
        Hom.app eN.hom ⊤ (pullbackGlobalSections i _ b) = (1 : Γ(Z, ⊤)) := by
  obtain ⟨B, hB⟩ := exists_prescribed_boundary_section_pair R n f i M N
  refine ⟨B, fun d hd eM eN => ?_⟩
  obtain ⟨a, b, ha, hb⟩ := hB d hd
    (Hom.app eM.inv ⊤ (1 : Γ(Z, ⊤))) (Hom.app eN.inv ⊤ (1 : Γ(Z, ⊤)))
  refine ⟨a, b, ?_, ?_⟩
  · exact (congrArg (fun s => Hom.app eM.hom ⊤ s) ha).trans
      (congrArg (fun ψ => ψ.val.app (op ⊤) (1 : Γ(Z, ⊤))) eM.inv_hom_id)
  · exact (congrArg (fun s => Hom.app eN.hom ⊤ s) hb).trans
      (congrArg (fun ψ => ψ.val.app (op ⊤) (1 : Γ(Z, ⊤))) eN.inv_hom_id)

end AlgebraicGeometry.Scheme.Modules
