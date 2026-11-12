/-
Copyright (c) 2026 Colib and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.ProjectiveSpace.Sections.SerreLifting
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.SectionEpiAffine.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedPushforward.Coherent

/-!
# Twisted boundary lifting after a finite projective presentation

Affine direct image preserves epimorphisms of quasi-coherent modules. Consequently a finite
presentation over projective space carries a coherent quotient to a coherent quotient to which
Serre lifting applies. The boundary specialization uses the actual adjunction unit for the
whole closed subscheme, retaining its nonreduced structure.

The sections here belong to the twists of the direct images. Identifying these with sections
of the pulled-back twists requires the projection formula; no such identification or flatness
of section zero schemes is implicit in these statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjectiveCohomology (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistFunctor

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

namespace AlgebraicGeometry.Scheme.Modules

/-- An affine direct image preserves epimorphisms between quasi-coherent modules. -/
theorem epi_pushforward_map_of_isAffineHom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) [Epi φ] :
    Epi ((pushforward f).map φ) := by
  let p := (pushforward f).map φ
  let g := (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).map p.val
  have hg : TopCat.Presheaf.IsLocallySurjective g := by
    apply (TopCat.Presheaf.isLocallySurjective_iff g).mpr
    intro V s y hy
    obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWV⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy V.isOpen
    obtain ⟨t, ht⟩ := Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X φ
      (f ⁻¹ᵁ W) (hW.preimage f)
      (((pushforward f).obj N).val.map (homOfLE hWV).op s)
    exact ⟨W, hWV, ⟨t, ht⟩, hyW⟩
  have : Epi ((SheafOfModules.toSheaf Y.ringCatSheaf).map p) :=
    (CategoryTheory.Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u}
      ((SheafOfModules.toSheaf Y.ringCatSheaf).map p)).mp hg
  exact Functor.epi_of_epi_map (SheafOfModules.toSheaf Y.ringCatSheaf) inferInstance

/-- A coherent quotient has uniformly liftable twisted direct-image sections along a finite
map to projective space. The integer bound is produced by Serre vanishing. -/
theorem exists_surjective_twisted_pushforward_evaluation_of_coherent_epi
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {X : Scheme.{u}} (f : X ⟶ Proj (polyGrading R n)) [IsFinite f]
    {M N : X.Modules} [M.IsCoherent] [N.IsCoherent] (φ : M ⟶ N) [Epi φ] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d → Function.Surjective
      ((SheafOfModules.evaluation (projRingSheaf (polyGrading R n)) (op ⊤)).map
        ((twistFunctor (polyGrading R n) d).map ((pushforward f).map φ))).hom := by
  have : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  have : N.IsQuasicoherent := isQuasicoherent_of_isCoherent N
  have : Epi ((pushforward f).map φ) := epi_pushforward_map_of_isAffineHom f φ
  have : ((pushforward f).obj M).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite f M
  have : ((pushforward f).obj N).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite f N
  let F : SheafOfModules.{u} (projRingSheaf (polyGrading R n)) := (pushforward f).obj N
  let G : SheafOfModules.{u} (projRingSheaf (polyGrading R n)) := (pushforward f).obj M
  have : F.IsCoherent := inferInstanceAs ((pushforward f).obj N).IsCoherent
  have : G.IsCoherent := inferInstanceAs ((pushforward f).obj M).IsCoherent
  let ψ : G ⟶ F := (pushforward f).map φ
  have : Epi ψ := inferInstanceAs (Epi ((pushforward f).map φ))
  exact exists_surjective_twisted_evaluation_of_coherent_epi R n ψ

/-- Every section of the twisted direct image of the restriction to the full closed boundary
lifts, for every integer twist beyond one bound. No reduction of the boundary is taken. -/
theorem exists_surjective_twisted_boundary_pushforward_evaluation
    (R : Type u) [CommRing R] [IsNoetherianRing R] (n : ℕ)
    {X Z : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Proj (polyGrading R n)) [IsFinite f]
    (i : Z ⟶ X) [IsClosedImmersion i] (M : X.Modules) [M.IsCoherent] :
    ∃ B : ℤ, ∀ d : ℤ, B ≤ d → Function.Surjective
      ((SheafOfModules.evaluation (projRingSheaf (polyGrading R n)) (op ⊤)).map
        ((twistFunctor (polyGrading R n) d).map
          ((pushforward f).map ((pullbackPushforwardAdjunction i).unit.app M)))).hom := by
  have : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  have : ((pullback i).obj M).IsCoherent := isCoherent_pullback i M
  have : ((pushforward i).obj ((pullback i).obj M)).IsCoherent :=
    isCoherent_pushforward_of_isClosedImmersion i _
  have := Stacks.ClosedImmersion.epi_unit_app i M
  have : ((𝟭 X.Modules).obj M).IsCoherent := inferInstanceAs M.IsCoherent
  have : ((pullback i ⋙ pushforward i).obj M).IsCoherent :=
    inferInstanceAs ((pushforward i).obj ((pullback i).obj M)).IsCoherent
  exact exists_surjective_twisted_pushforward_evaluation_of_coherent_epi R n f
    ((pullbackPushforwardAdjunction i).unit.app M)

end AlgebraicGeometry.Scheme.Modules
