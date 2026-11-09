/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectSupportedRestriction

/-! # Native perfectness on an open cover

Perfectness descends along two actual open immersions covering a scheme. The proof uses
native Stacks local perfectness and the actual scheme restriction comparisons.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace AlgebraicGeometry.Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Perfectness on the source of an open immersion gives perfectness on its image open. -/
theorem Complex.isPerfectComplex_opensRange_of_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (K : CochainComplex X.Modules ℤ)
    (hK : RingedSpace.IsPerfectComplex (X := U.toRingedSpace)
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :
    RingedSpace.IsPerfectComplex (X := j.opensRange.toScheme.toRingedSpace)
      (((restrictFunctor j.opensRange.ι).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  let e : U ≅ j.opensRange.toScheme := IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by
    ext x
    simp)
  have he : e.inv ≫ j = j.opensRange.ι := IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
  have h := Complex.isPerfectComplex_restrictOpenImmersion e.inv _ hK
  exact h.of_iso ((NatIso.mapHomologicalComplex
    ((restrictFunctorComp e.inv j).symm ≪≫ restrictFunctorCongr he)
    (ComplexShape.up ℤ)).app K)

/-- Native perfectness is local on an arbitrary two-open cover, without compactness. -/
@[stacks 08CM "Native perfectness descended from the two actual restrictions"]
theorem Complex.isPerfectComplex_of_two_openImmersions {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    (K : CochainComplex X.Modules ℤ)
    (hU : RingedSpace.IsPerfectComplex (X := U.toRingedSpace)
      (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hV : RingedSpace.IsPerfectComplex (X := V.toRingedSpace)
      (((restrictFunctor k).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :
    RingedSpace.IsPerfectComplex (X := X.toRingedSpace) K := by
  apply RingedSpace.isPerfectComplex_of_forall_isPerfectComplex_restrict
  have descend (Y : Scheme.{u}) (f : Y ⟶ X) [IsOpenImmersion f]
      (hf : RingedSpace.IsPerfectComplex (X := Y.toRingedSpace)
        (((restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :
      RingedSpace.IsPerfectComplex (RingedSpace.restrictComplex K f.opensRange) := by
    have : (show StrictlyPerfect.OXMod.{u, u, u} X.toRingedSpace ⥤
        StrictlyPerfect.OXMod.{u, u, u}
          (X.toRingedSpace.restrict f.opensRange.isOpenEmbedding) from
          restrictFunctor f.opensRange.ι).PreservesZeroMorphisms :=
      ⟨fun _ _ => by ext _ _; rfl⟩
    have h := Complex.isPerfectComplex_opensRange_of_restrict f K hf
    exact h.of_iso ((NatIso.mapHomologicalComplex
      (RingedSpace.restrictModulesIsoRestrictFunctor X f.opensRange)
      (ComplexShape.up ℤ)).app K).symm
  intro x
  rcases hcover x with hx | hx
  · exact ⟨j.opensRange, hx, descend U j hU⟩
  · exact ⟨k.opensRange, hx, descend V k hV⟩

/-- A module-sheaf map is invertible if it is invertible on two covering open immersions. -/
theorem isIso_of_two_openImmersions {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((restrictFunctor j).map f)] [IsIso ((restrictFunctor k).map f)] : IsIso f := by
  let F := _root_.SheafOfModules.toSheaf X.ringCatSheaf
  have localIso {Y : Scheme.{u}} (a : Y ⟶ X) [IsOpenImmersion a]
      [IsIso ((restrictFunctor a).map f)] (y : Y) :
      IsIso ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (a y)).map f) := by
    let e := restrictStalkNatIso a y
    have : IsIso ((restrictFunctor a ⋙ toPresheaf Y ⋙
        TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map f) := by
      change IsIso ((toPresheaf Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((restrictFunctor a).map f))
      infer_instance
    have : IsIso (e.hom.app M ≫
        (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (a y)).map f) := by
      rw [← e.hom.naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (e.hom.app M) _
  have hs : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (F.map f).hom) := by
    intro x
    rcases hcover x with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · exact localIso j y
    · exact localIso k y
  have : IsIso (F.map f) :=
    TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (F.map f)
  have : IsIso ((toPresheaf X).map f) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map (F.map f)))
  exact isIso_of_reflects_iso f (toPresheaf X)

/-- Actual quasi-isomorphisms are detected on two covering open immersions. -/
theorem Complex.quasiIso_of_two_openImmersions {U V X : Scheme.{u}}
    (j : U ⟶ X) (k : V ⟶ X) [IsOpenImmersion j] [IsOpenImmersion k]
    (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range k)
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    [QuasiIso (((restrictFunctor j).mapHomologicalComplex (ComplexShape.up ℤ)).map f)]
    [QuasiIso (((restrictFunctor k).mapHomologicalComplex (ComplexShape.up ℤ)).map f)] :
    QuasiIso f := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have localIso {Y : Scheme.{u}} (a : Y ⟶ X) [IsOpenImmersion a]
      [QuasiIso (((restrictFunctor a).mapHomologicalComplex (ComplexShape.up ℤ)).map f)] :
      IsIso ((restrictFunctor a).map (HomologicalComplex.homologyMap f n)) := by
    have : IsIso (homologyMap
        (((restrictFunctor a).mapHomologicalComplex (ComplexShape.up ℤ)).map f) n) :=
      inferInstance
    exact (NatIso.isIso_map_iff
      (Stacks.PseudoCoherence.DerivedCharacterization.mapHomologicalComplexHomologyIso
        (restrictFunctor a) (ComplexShape.up ℤ) n) f).mp
        (show IsIso (homologyMap
          (((restrictFunctor a).mapHomologicalComplex (ComplexShape.up ℤ)).map f) n)
          from inferInstance)
  have := localIso j
  have := localIso k
  exact isIso_of_two_openImmersions j k hcover _

end AlgebraicGeometry.Scheme.Modules
