/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Homology.CochainComplex.BoundedAbove.RelativeProjectiveFactorization
public import Colib.Algebra.Category.ModuleCat.Sheaf.ProjectiveSheafification
public import Colib.AlgebraicGeometry.Modules.BoundedFlatPerfect
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.PresheafOfModulesProjectives

/-!
# Relative Flat Factorization of Actual Sheaf Complexes

Apply the native relative projective factorization to the underlying presheaf map. Exact
sheafification and its original counit give an actual commuting triangle with unchanged
endpoints. The first arrow has a bounded-above flat quotient and is an actual short exact
inclusion. The second arrow is a genuine quasi-isomorphism. Forgetting sheaves to presheaves
is used only to preserve zero terms; it is not assumed exact.

Adapted from `Quillen/Aglib/AlgebraicGeometry/Modules/Flat/RelativeFactorization.lean` at
`c561118b7795eb9780be9ed391c3251d6a4d0afd`, generalized from schemes to ringed spaces.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry StrictlyPerfect
open HomologicalComplex TopologicalSpace

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u, u})

/-- The actual sheafification counit, applied degreewise to a cochain complex. -/
def sheafificationCochainCounitIso (K : CochainComplex (OXMod.{u, u, u} X) ℤ) :
    ((PresheafOfModules.sheafification (𝟙 (structureSheafOfRings X).obj)).mapHomologicalComplex
      (.up ℤ)).obj
      (((SheafOfModules.forget (structureSheafOfRings X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafOfRings X).obj)).mapHomologicalComplex
        (.up ℤ)).obj K) ≅ K :=
  ((NatIso.mapHomologicalComplex
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafOfRings X).obj)).counit) (.up ℤ)) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app K

/-- The counit retains the original chain map, not merely its derived class. -/
@[reassoc]
theorem sheafificationCochainCounitIso_naturality
    {K L : CochainComplex (OXMod.{u, u, u} X) ℤ} (f : K ⟶ L) :
    ((PresheafOfModules.sheafification (𝟙 (structureSheafOfRings X).obj)).mapHomologicalComplex
      (.up ℤ)).map
      (((SheafOfModules.forget (structureSheafOfRings X) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheafOfRings X).obj)).mapHomologicalComplex
        (.up ℤ)).map f) ≫ (sheafificationCochainCounitIso X L).hom =
      (sheafificationCochainCounitIso X K).hom ≫ f := by
  exact ((NatIso.mapHomologicalComplex
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheafOfRings X).obj)).counit) (.up ℤ)) ≪≫
    Functor.mapHomologicalComplexIdIso _ (.up ℤ)).hom.naturality f

/-- Actual relative flat factorization with the explicit upper bound and strict triangle. -/
@[colib_tag "COL-0325",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/Flat/RelativeFactorization.lean:39-124"
    "adaptation" "Relative presheaf CM5a, exact sheafification and the unchanged counit triangle"]
theorem exists_boundedAbove_relative_flat_factorization
    {K L : CochainComplex (OXMod.{u, u, u} X) ℤ} (f : K ⟶ L) (b : ℤ)
    [K.IsStrictlyLE b] [L.IsStrictlyLE b]
    (hK : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (K.X n)) :
    ∃ (M Q : CochainComplex (OXMod.{u, u, u} X) ℤ) (i : K ⟶ M) (p : M ⟶ L)
      (q : M ⟶ Q) (w : i ≫ q = 0),
      QuasiIso p ∧ i ≫ p = f ∧ (ShortComplex.mk i q w).ShortExact ∧
      M.IsStrictlyLE (b + 1) ∧ Q.IsStrictlyLE (b + 1) ∧
      (∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (M.X n)) ∧
        ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (Q.X n) := by
  let R := SheafOfModules.forget (structureSheafOfRings X) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheafOfRings X).obj)
  let A := PresheafOfModules.sheafification (𝟙 (structureSheafOfRings X).obj)
  let RH : CochainComplex (OXMod.{u, u, u} X) ℤ ⥤
      CochainComplex (PresheafOfModules.{u} (structureSheafOfRings X).obj) ℤ :=
    R.mapHomologicalComplex (.up ℤ)
  let AH : CochainComplex (PresheafOfModules.{u} (structureSheafOfRings X).obj) ℤ ⥤
      CochainComplex (OXMod.{u, u, u} X) ℤ := A.mapHomologicalComplex (.up ℤ)
  have hR (T : CochainComplex (OXMod.{u, u, u} X) ℤ) [T.IsStrictlyLE b] :
      (RH.obj T).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact R.map_isZero (T.isZero_of_isStrictlyLE b n hn)
  have := hR K
  have := hR L
  obtain ⟨M₀, i₀, p₀, hbM₀, hp₀, hfac, hi₀⟩ :=
    CochainComplex.exists_boundedAbove_relative_projective_factorization (RH.map f) b
  have : Mono i₀ := HomologicalComplex.mono_of_mono_f _ (fun n => by
    let := (CochainComplex.splitMono_projective_cokernel_of_op_epiWithInjectiveKernel
      (i₀.f n) (hi₀ n)).1
    infer_instance)
  let Q₀ := cokernel i₀
  let S₀ := ShortComplex.mk i₀ (cokernel.π i₀) (cokernel.condition i₀)
  have hs₀ : S₀.ShortExact := { exact := ShortComplex.cokernelSequence_exact i₀ }
  have hQ₀ (n : ℤ) : Projective (Q₀.X n) :=
    CochainComplex.relative_factorization_projective_cokernel i₀ hi₀ n
  have hbQ₀ : Q₀.IsStrictlyLE (b + 1) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact IsZero.of_epi ((cokernel.π i₀).f n)
      (M₀.isZero_of_isStrictlyLE (b + 1) n hn)
  let M := AH.obj M₀
  let Q := AH.obj Q₀
  let eK := sheafificationCochainCounitIso X K
  let eL := sheafificationCochainCounitIso X L
  let i : K ⟶ M := eK.inv ≫ AH.map i₀
  let p : M ⟶ L := AH.map p₀ ≫ eL.hom
  let q : M ⟶ Q := AH.map (cokernel.π i₀)
  have w : i ≫ q = 0 := by
    dsimp [i, q]
    rw [Category.assoc, ← AH.map_comp, cokernel.condition, AH.map_zero, comp_zero]
  let S := ShortComplex.mk i q w
  have hS : S.ShortExact := by
    have hsA : (S₀.map AH).ShortExact := hs₀.map_of_exact AH
    apply ShortComplex.shortExact_of_iso (S₁ := S₀.map AH) (S₂ := S) _ hsA
    refine ShortComplex.isoMk (S₁ := S₀.map AH) (S₂ := S) eK (Iso.refl _) (Iso.refl _) ?_ ?_
    · dsimp [S₀, S, i]
      simp
    · dsimp [S₀, S, q]
      simp
  have hQ (n : ℤ) : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (Q.X n) :=
    PresheafOfModules.isFlat_sheafification_of_projective
      (Opens.grothendieckTopology X.carrier) X.sheaf (Q₀.X n)
  have hM (n : ℤ) : AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (M.X n) := by
    let E := HomologicalComplex.eval (OXMod.{u, u, u} X) (.up ℤ) n
    let : E.PreservesZeroMorphisms := { map_zero := by intros; rfl }
    exact Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_middle_of_shortExact
      X.sheaf (S.map E)
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n) (hK n) (hQ n)
  refine ⟨M, Q, i, p, q, w, ?_, ?_, hS, ?_, ?_, hM, hQ⟩
  · let : QuasiIso p₀ := hp₀
    have : QuasiIso (AH.map p₀) :=
      HomologicalComplex.quasiIso_map_of_preservesHomology p₀ A
    dsimp [p]
    infer_instance
  · dsimp [i, p]
    rw [Category.assoc, ← AH.map_comp_assoc, hfac]
    have hn := sheafificationCochainCounitIso_naturality X f
    change AH.map (RH.map f) ≫ eL.hom = eK.hom ≫ f at hn
    rw [hn]
    simp
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact A.map_isZero (M₀.isZero_of_isStrictlyLE (b + 1) n hn)
  · rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact A.map_isZero (Q₀.isZero_of_isStrictlyLE (b + 1) n hn)

end AlgebraicGeometry.RingedSpace
