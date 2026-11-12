/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.Algebra.Category.FGModuleCat.Localization
public import Colib.CategoryTheory.Pi.FiniteSupport
public import Mathlib.Algebra.Module.Torsion.PrimaryComponent
public import Mathlib.Algebra.Module.DedekindDomain
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Primary decomposition of finite torsion modules over a Dedekind domain

Adapted from `Quillen/Aglib/Algebra/Category/FGModuleCat/PrimaryDecomposition.lean`
at Quillen commit `c561118b7795eb9780be9ed391c3251d6a4d0afd`.
The native finite-module categories, primary components and canonical maps are retained.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits
open scoped nonZeroDivisors DirectSum ZeroObject

namespace FGModuleCat.PrimaryDecomposition

attribute [local instance] Abelian.hasFiniteBiproducts Classical.propDecidable

variable (R : Type u) [CommRing R]

/-- The existing localization-kernel category of actual finitely generated torsion modules. -/
abbrev TorsionModule :=
  (FGModuleCat.localizationTorsionProperty.{u, u} (nonZeroDivisors R)).FullSubcategory

/-- Vanishing at the total quotient ring is precisely the usual torsion condition. -/
theorem torsion_iff_isTorsion (M : FGModuleCat.{u} R) :
    FGModuleCat.localizationTorsionProperty (nonZeroDivisors R) M ↔ Module.IsTorsion R M := Iff.rfl

section Noetherian

variable [IsNoetherianRing R]

/-- An actual primary-component module is finite because the base ring is noetherian. -/
def componentModule (I : Ideal R) (M : FGModuleCat.{u} R) : FGModuleCat.{u} R :=
  FGModuleCat.of R (Ideal.primaryComponent M I)

/-- The original primary-component construction on actual finite modules and linear maps. -/
def componentFunctor (I : Ideal R) : FGModuleCat.{u} R ⥤ FGModuleCat.{u} R where
  obj := componentModule R I
  map f := FGModuleCat.ofHom (Ideal.primaryComponent.map I f.hom.hom)
  map_id M := by
    apply FGModuleCat.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    ext x
    rfl

@[simp]
theorem componentFunctor_map_apply (I : Ideal R) {M N : FGModuleCat.{u} R} (f : M ⟶ N)
    (x : Ideal.primaryComponent M I) :
    ((componentFunctor R I).map f).hom.hom x = Ideal.primaryComponent.map I f.hom.hom x := rfl

instance componentFunctor_additive (I : Ideal R) : (componentFunctor R I).Additive where
  map_add := by intros; apply FGModuleCat.hom_ext; ext x; rfl

/-- Inclusion of each primary component into the original finite module, with its actual map. -/
def componentInclusion (I : Ideal R) : componentFunctor R I ⟶ 𝟭 (FGModuleCat.{u} R) where
  app M := FGModuleCat.ofHom (Ideal.primaryComponent M I).subtype
  naturality M N f := by
    apply FGModuleCat.hom_ext
    ext x
    rfl

/-- The primary-component functor restricted to the original torsion category. -/
def torsionComponentFunctor (I : Ideal R) : TorsionModule R ⥤ FGModuleCat.{u} R :=
  (FGModuleCat.localizationTorsionProperty (nonZeroDivisors R)).ι ⋙ componentFunctor R I

instance torsionComponentFunctor_additive (I : Ideal R) :
    (torsionComponentFunctor R I).Additive := by
  dsimp [torsionComponentFunctor]
  infer_instance

/-- Finite modules killed by some power of the given ideal. -/
def primaryObjectProperty (I : Ideal R) : ObjectProperty (FGModuleCat.{u} R) :=
  fun M => ∃ n : ℕ, ∀ r ∈ I ^ n, ∀ m : M, r • m = 0

omit [IsNoetherianRing R] in
/-- The primary condition records an actual annihilating ideal power. -/
theorem primaryObjectProperty_iff_power_le_annihilator (I : Ideal R) (M : FGModuleCat.{u} R) :
    primaryObjectProperty R I M ↔ ∃ n : ℕ, I ^ n ≤ Module.annihilator R M := by
  simp only [primaryObjectProperty, IsConcreteLE.le_iff, Module.mem_annihilator]

/-- The full category of actual finite modules killed by an ideal power. -/
abbrev PrimaryModule (I : Ideal R) := (primaryObjectProperty R I).FullSubcategory

instance primaryObjectProperty_serre (I : Ideal R) : (primaryObjectProperty R I).IsSerreClass where
  exists_zero := by
    let Z : FGModuleCat.{u} R := 0
    have hz : IsZero Z := isZero_zero _
    have : Subsingleton Z := (ModuleCat.isZero_iff_subsingleton).1
      ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map_isZero hz)
    refine ⟨Z, hz, 0, ?_⟩
    intro r hr m
    exact Subsingleton.elim _ _
  prop_of_mono f hf h := by
    let := hf
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    intro r hr m
    have hf' := (ModuleCat.mono_iff_injective
      ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map f)).1 inferInstance
    apply hf'
    change f.hom.hom (r • m) = f.hom.hom 0
    rw [map_smul, hn r hr _, map_zero]
  prop_of_epi f hf h := by
    let := hf
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    intro r hr m
    have hf' := (ModuleCat.epi_iff_surjective
      ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map f)).1 inferInstance
    obtain ⟨x, rfl⟩ := hf' m
    change r • f.hom.hom x = 0
    rw [← map_smul, hn r hr x, map_zero]
  prop_X₂_of_shortExact {S} h h₁ h₃ := by
    obtain ⟨a, ha⟩ := (primaryObjectProperty_iff_power_le_annihilator R I _).1 h₁
    obtain ⟨b, hb⟩ := h₃
    apply (primaryObjectProperty_iff_power_le_annihilator R I _).2
    refine ⟨a + b, ?_⟩
    rw [pow_add]
    apply Ideal.mul_le.mpr
    intro r hr s hs
    rw [Module.mem_annihilator]
    intro m
    have hA := h.map_of_exact (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
    have hg : S.g.hom.hom (s • m) = 0 := by
      rw [map_smul]
      exact hb s hs _
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).1 hA.exact (s • m) hg
    change S.f.hom.hom x = s • m at hx
    calc
      (r * s) • m = r • (s • m) := mul_smul r s m
      _ = r • S.f.hom.hom x := by rw [hx]
      _ = S.f.hom.hom (r • x) := (map_smul S.f.hom.hom r x).symm
      _ = 0 := by rw [(Module.mem_annihilator.mp (ha hr)) x, map_zero]


/-- Finite generation gives one uniform ideal-power bound on the actual primary component. -/
theorem component_le_torsionBySet (I : Ideal R) (M : FGModuleCat.{u} R) :
    ∃ n : ℕ, Ideal.primaryComponent M I ≤ Submodule.torsionBySet R M (I ^ n : Ideal R) := by
  have hc : IsCompactElement (Ideal.primaryComponent M I) :=
    (Submodule.fg_iff_compact _).1 (IsNoetherian.noetherian _)
  obtain ⟨s, hs⟩ := hc.exists_finset_of_le_iSup
    (fun n : ℕ => Submodule.torsionBySet R M (I ^ n : Ideal R)) le_rfl
  refine ⟨s.sup id, hs.trans ?_⟩
  apply iSup_le
  intro n
  apply iSup_le
  intro hn
  exact Submodule.torsionBySet_le_torsionBySet_pow n (s.sup id) (Finset.le_sup (f := id) hn) I

/-- The actual primary component is an object of the ideal-power primary category. -/
theorem componentModule_primary (I : Ideal R) (M : FGModuleCat.{u} R) :
    primaryObjectProperty R I (componentModule R I M) := by
  obtain ⟨n, hn⟩ := component_le_torsionBySet R I M
  refine ⟨n, ?_⟩
  intro r hr x
  apply Subtype.ext
  exact (Submodule.mem_torsionBySet_iff _ _).1 (hn x.property) ⟨r, hr⟩

/-- The original primary-component functor with its actual primary-category codomain. -/
def componentToPrimary (I : Ideal R) : FGModuleCat.{u} R ⥤ PrimaryModule R I :=
  (primaryObjectProperty R I).lift (componentFunctor R I) (componentModule_primary R I)

instance componentToPrimary_additive (I : Ideal R) : (componentToPrimary R I).Additive := by
  dsimp [componentToPrimary]
  infer_instance

/-- Restrict the actual primary-category functor to the existing torsion category. -/
def torsionPrimaryFunctor (I : Ideal R) : TorsionModule R ⥤ PrimaryModule R I :=
  (FGModuleCat.localizationTorsionProperty R⁰).ι ⋙ componentToPrimary R I

instance torsionPrimaryFunctor_additive (I : Ideal R) : (torsionPrimaryFunctor R I).Additive := by
  dsimp [torsionPrimaryFunctor]
  infer_instance

end Noetherian

section Dedekind

variable [IsDedekindDomain R]

/-- Exact linear maps stay exact after taking primary components of a torsion source. -/
theorem primaryMap_exact {M₁ M₂ M₃ : Type u}
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (hM : Module.IsTorsion R M₁) (p : IsDedekindDomain.HeightOneSpectrum R)
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g) :
    Function.Exact (Ideal.primaryComponent.map p.asIdeal f)
      (Ideal.primaryComponent.map p.asIdeal g) := by
  let fk : M₁ →ₗ[R] g.ker := f.codRestrict g.ker (fun x => (h (f x)).2 ⟨x, rfl⟩)
  have hfk : Function.Surjective fk := by
    intro y
    obtain ⟨x, hx⟩ := (h y.val).1 y.property
    exact ⟨x, Subtype.ext hx⟩
  intro y
  constructor
  · intro hy
    have hy' : (y : M₂) ∈
        (Ideal.primaryComponent.map p.asIdeal g).ker.map
          (Ideal.primaryComponent M₂ p.asIdeal).subtype := ⟨y, hy, rfl⟩
    rw [Ideal.primaryComponent.map_ker_eq] at hy'
    obtain ⟨z, hz, hzy⟩ := hy'
    obtain ⟨x, hx⟩ := Ideal.primaryComponent.map_surjective hM p fk hfk ⟨z, hz⟩
    refine ⟨x, Subtype.ext ?_⟩
    exact (congrArg (fun t : Ideal.primaryComponent g.ker p.asIdeal =>
      (t : g.ker).val) hx).trans hzy
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact (h (f x.val)).2 ⟨x.val, rfl⟩

/-- The actual primary-component functor is exact on the actual torsion category. -/
def torsionComponentExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor (ExactCategory.abelianExactStructure
      (FGModuleCat.localizationTorsionProperty R⁰).FullSubcategory)
      (ExactCategory.abelianExactStructure (FGModuleCat.{u} R)) where
  toFunctor := torsionComponentFunctor R p.asIdeal
  map_conflation S hS := by
    let U := forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)
    let A :=
      (ObjectProperty.exactInclusion (FGModuleCat.localizationTorsionProperty R⁰)).map_conflation
        S hS
    have hA := A.map_of_exact U
    let T := (S.map (torsionComponentFunctor R p.asIdeal)).map U
    have hT : T.ShortExact := by
      apply ModuleCat.shortComplex_shortExact
      · exact primaryMap_exact R ((torsion_iff_isTorsion R S.X₁.obj).1 S.X₁.property) p
          S.f.hom.hom.hom S.g.hom.hom.hom
          ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hA.exact)
      · intro x y hxy
        apply Subtype.ext
        exact hA.moduleCat_injective_f (congrArg Subtype.val hxy)
      · exact Ideal.primaryComponent.map_surjective
          ((torsion_iff_isTorsion R S.X₂.obj).1 S.X₂.property) p S.g.hom.hom.hom
          hA.moduleCat_surjective_g
    exact
      { exact := U.reflects_exact_of_faithful _ hT.exact
        mono_f := U.mono_of_mono_map hT.mono_f
        epi_g := U.epi_of_epi_map hT.epi_g }

/-- Primary components are exact with values in the actual ideal-power primary category. -/
def torsionPrimaryExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor (ExactCategory.abelianExactStructure
      (FGModuleCat.localizationTorsionProperty R⁰).FullSubcategory)
      (ExactCategory.abelianExactStructure (primaryObjectProperty R p.asIdeal).FullSubcategory)
where
  toFunctor := torsionPrimaryFunctor R p.asIdeal
  map_conflation S hS := by
    let U := (primaryObjectProperty R p.asIdeal).ι
    have hA : ((S.map (torsionPrimaryFunctor R p.asIdeal)).map U).ShortExact :=
      (torsionComponentExactFunctor R p).map_conflation S hS
    exact
      { exact := U.reflects_exact_of_faithful _ hA.exact
        mono_f := U.mono_of_mono_map hA.mono_f
        epi_g := U.epi_of_epi_map hA.epi_g }

/-- The actual primary-component family, before recording its finite support. -/
def primaryFamilyFunctor : TorsionModule R ⥤
    (∀ p : IsDedekindDomain.HeightOneSpectrum R, PrimaryModule R p.asIdeal) :=
  Functor.pi' (fun p => torsionPrimaryFunctor R p.asIdeal)

instance primaryFamilyFunctor_additive : (primaryFamilyFunctor R).Additive where
  map_add := by
    intro M N f g
    funext p
    exact (torsionPrimaryFunctor R p.asIdeal).map_add

/-- Annihilator support controls the nonzero actual primary components. -/
theorem primaryComponent_eq_bot_of_not_dvd (M : FGModuleCat.{u} R)
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (hp : ¬ p.asIdeal ∣ (⊤ : Submodule R M).annihilator) :
    Ideal.primaryComponent M p.asIdeal = ⊥ := by
  have hc : IsCoprime p.asIdeal (⊤ : Submodule R M).annihilator := by
    rw [Ideal.isCoprime_iff_codisjoint]
    exact p.isMaximal.out.not_le_iff_codisjoint.mp (fun h => hp (Ideal.dvd_iff_le.mpr h))
  apply (Submodule.eq_bot_iff _).2
  intro x hx
  obtain ⟨n, hn⟩ := (Ideal.primaryComponent_mem M p.asIdeal x).1 hx
  have hd : Disjoint (Submodule.torsionBySet R M (p.asIdeal ^ n : Ideal R))
      (Submodule.torsionBySet R M (⊤ : Submodule R M).annihilator) :=
    Submodule.disjoint_torsionBySet_ideal (Ideal.pow_sup_eq_top hc.sup_eq)
  exact Submodule.disjoint_def.mp hd x hn
    ((Submodule.mem_torsionBySet_iff _ _).2
      (fun a => Submodule.mem_annihilator.mp a.property x Submodule.mem_top))

/-- A primary coordinate outside the annihilator factors is an actual zero module. -/
theorem componentModule_isZero_of_not_dvd (M : FGModuleCat.{u} R)
    (p : IsDedekindDomain.HeightOneSpectrum R)
    (hp : ¬ p.asIdeal ∣ (⊤ : Submodule R M).annihilator) :
    IsZero (componentModule R p.asIdeal M) := by
  have heq := primaryComponent_eq_bot_of_not_dvd R M p hp
  have : Subsingleton (Ideal.primaryComponent M p.asIdeal) := by
    rw [heq]
    infer_instance
  apply IsZero.of_full_of_faithful_of_isZero
    (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
  change IsZero (ModuleCat.of R (Ideal.primaryComponent M p.asIdeal))
  exact ModuleCat.isZero_of_subsingleton _

/-- Finite generation and torsion make the module annihilator a nonzero ideal. -/
theorem annihilator_ne_zero (M : TorsionModule R) :
    (⊤ : Submodule R M.obj).annihilator ≠ 0 := by
  obtain ⟨r, hr, hr'⟩ := Submodule.annihilator_top_inter_nonZeroDivisors
    ((torsion_iff_isTorsion R M.obj).1 M.property)
  intro h
  have hr0 : r = 0 := by simpa [h] using hr
  exact nonZeroDivisors.ne_zero hr' hr0

/-- The primary family has finite nonzero support, bounded by annihilator factors. -/
theorem primaryFamily_finiteSupport (M : TorsionModule R) :
    Pi.finiteObjectSupport
      (fun p : IsDedekindDomain.HeightOneSpectrum R => PrimaryModule R p.asIdeal)
      ((primaryFamilyFunctor R).obj M) := by
  apply (Ideal.finite_factors (annihilator_ne_zero R M)).subset
  intro p hp
  by_contra hpd
  apply hp
  apply IsZero.of_full_of_faithful_of_isZero (primaryObjectProperty R p.asIdeal).ι
  exact componentModule_isZero_of_not_dvd R M.obj p hpd

/-- Canonical primary components with finite support recorded in the existing family category. -/
def finitePrimaryFunctor : TorsionModule R ⥤
    Pi.FiniteCategoryFamily
      (fun p : IsDedekindDomain.HeightOneSpectrum R => PrimaryModule R p.asIdeal) :=
  (Pi.finiteObjectSupport _).lift (primaryFamilyFunctor R) (primaryFamily_finiteSupport R)

instance finitePrimaryFunctor_additive : (finitePrimaryFunctor R).Additive := by
  dsimp [finitePrimaryFunctor]
  infer_instance

/-- The primary splitting functor is exact on the actual torsion category. -/
def finitePrimaryExactFunctor : ExactCategory.ExactFunctor
    (ExactCategory.abelianExactStructure
      (FGModuleCat.localizationTorsionProperty R⁰).FullSubcategory)
    (Pi.finiteCategoryExactStructure
      (fun p : IsDedekindDomain.HeightOneSpectrum R => PrimaryModule R p.asIdeal)) where
  toFunctor := finitePrimaryFunctor R
  map_conflation S hS := by
    let U := (Pi.finiteObjectSupport
      (fun p : IsDedekindDomain.HeightOneSpectrum R => PrimaryModule R p.asIdeal)).ι
    have hA : ((S.map (finitePrimaryFunctor R)).map U).ShortExact := by
      apply Pi.shortExact_pi_of
      intro p
      exact (torsionPrimaryExactFunctor R p).map_conflation S hS
    exact
      { exact := U.reflects_exact_of_faithful _ hA.exact
        mono_f := U.mono_of_mono_map hA.mono_f
        epi_g := U.epi_of_epi_map hA.epi_g }

/-- The original primary-coordinate functor is literally finite-family evaluation. -/
theorem finitePrimaryFunctor_comp_evaluation (p : IsDedekindDomain.HeightOneSpectrum R) :
    finitePrimaryFunctor R ⋙ (Pi.finiteCategoryEvaluation
      (fun q : IsDedekindDomain.HeightOneSpectrum R => PrimaryModule R q.asIdeal) p).toFunctor =
      torsionPrimaryFunctor R p.asIdeal := rfl

/-- The sum of the actual primary submodules is an internal direct sum. -/
theorem isInternalPrimaryComponents (M : TorsionModule R) :
    DirectSum.IsInternal (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      Ideal.primaryComponent M.obj p.asIdeal) := by
  classical
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (Ideal.iSupIndep_primaryComponent R M.obj)
    (Ideal.iSup_primaryComponent_eq_top ((torsion_iff_isTorsion R M.obj).1 M.property))

/-- Canonical summation of the actual primary inclusions, as a linear equivalence. -/
def primarySumLinearEquiv (M : TorsionModule R) :
    (⨁ p : IsDedekindDomain.HeightOneSpectrum R, Ideal.primaryComponent M.obj p.asIdeal) ≃ₗ[R]
      M.obj := by
  classical
  exact LinearEquiv.ofBijective (DirectSum.coeLinearMap
    (fun p : IsDedekindDomain.HeightOneSpectrum R => Ideal.primaryComponent M.obj p.asIdeal))
    (isInternalPrimaryComponents R M)

/-- The canonical sum of primary components remains finitely generated. -/
instance primarySum_finite (M : TorsionModule R) : Module.Finite R
    (⨁ p : IsDedekindDomain.HeightOneSpectrum R, Ideal.primaryComponent M.obj p.asIdeal) :=
  Module.Finite.equiv (primarySumLinearEquiv R M).symm

/-- The actual finite module given by the canonical sum of primary components. -/
abbrev primarySumModule (M : TorsionModule R) : FGModuleCat.{u} R :=
  FGModuleCat.of R
    (⨁ p : IsDedekindDomain.HeightOneSpectrum R, Ideal.primaryComponent M.obj p.asIdeal)

/-- The canonical direct-sum object and the actual componentwise linear maps. -/
def primarySumFunctor : TorsionModule R ⥤ FGModuleCat.{u} R where
  obj := primarySumModule R
  map f := ObjectProperty.homMk (ModuleCat.ofHom (DFinsupp.mapRange.linearMap
    (fun p : IsDedekindDomain.HeightOneSpectrum R =>
      Ideal.primaryComponent.map p.asIdeal f.hom.hom.hom)))
  map_id M := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro p
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply DFinsupp.ext
    intro p
    rfl

/-- Canonical summation of primary inclusions recovers the original finite torsion module. -/
def primarySumIso : primarySumFunctor R ≅ (FGModuleCat.localizationTorsionProperty R⁰).ι :=
  NatIso.ofComponents (fun M => (primarySumLinearEquiv R M).toFGModuleCatIso) (by
    intro M N f
    apply FGModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro p
    ext x
    change DirectSum.coeLinearMap
        (fun q : IsDedekindDomain.HeightOneSpectrum R => Ideal.primaryComponent N.obj q.asIdeal)
        (DirectSum.lmap
          (fun q : IsDedekindDomain.HeightOneSpectrum R =>
            Ideal.primaryComponent.map q.asIdeal f.hom.hom.hom)
          (DirectSum.lof R _
            (fun q : IsDedekindDomain.HeightOneSpectrum R =>
              Ideal.primaryComponent M.obj q.asIdeal) p x)) =
      f.hom.hom.hom (DirectSum.coeLinearMap
        (fun q : IsDedekindDomain.HeightOneSpectrum R => Ideal.primaryComponent M.obj q.asIdeal)
        (DirectSum.lof R _
          (fun q : IsDedekindDomain.HeightOneSpectrum R =>
            Ideal.primaryComponent M.obj q.asIdeal) p x))
    simp only [DirectSum.lmap_lof, DirectSum.coeLinearMap_lof,
      Ideal.primaryComponent.map_apply_coe])


/-- A module killed by a prime-ideal power is an object of the original torsion category. -/
theorem primaryObjectProperty_le_torsion (p : IsDedekindDomain.HeightOneSpectrum R) :
    primaryObjectProperty R p.asIdeal ≤ FGModuleCat.localizationTorsionProperty R⁰ := by
  intro M hM
  rw [torsion_iff_isTorsion]
  obtain ⟨n, hn⟩ := hM
  have hpn : p.asIdeal ^ n ≠ ⊥ := pow_ne_zero n p.ne_bot
  obtain ⟨r, hr, hr0⟩ := (Submodule.ne_bot_iff _).mp hpn
  intro m
  exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr0⟩, hn r hr m⟩

/-- Literal inclusion of a primary module into the actual finitely generated torsion category. -/
def primaryToTorsion (p : IsDedekindDomain.HeightOneSpectrum R) :
    PrimaryModule R p.asIdeal ⥤ TorsionModule R :=
  ObjectProperty.ιOfLE (primaryObjectProperty_le_torsion R p)

instance primaryToTorsion_additive (p : IsDedekindDomain.HeightOneSpectrum R) :
    (primaryToTorsion R p).Additive where
  map_add := by intros; rfl

/-- The actual primary-to-torsion inclusion is exact. -/
def primaryToTorsionExactFunctor (p : IsDedekindDomain.HeightOneSpectrum R) :
    ExactCategory.ExactFunctor
      (ExactCategory.abelianExactStructure (primaryObjectProperty R p.asIdeal).FullSubcategory)
      (ExactCategory.abelianExactStructure
      (FGModuleCat.localizationTorsionProperty R⁰).FullSubcategory)
where
  toFunctor := primaryToTorsion R p
  map_conflation S hS := by
    let U := (FGModuleCat.localizationTorsionProperty R⁰).ι
    have hA : ((S.map (primaryToTorsion R p)).map U).ShortExact :=
      (ObjectProperty.exactInclusion (primaryObjectProperty R p.asIdeal)).map_conflation
        S hS
    exact
      { exact := U.reflects_exact_of_faithful _ hA.exact
        mono_f := U.mono_of_mono_map hA.mono_f
        epi_g := U.epi_of_epi_map hA.epi_g }

/-- A primary module has no component at another height-one prime. -/
theorem primaryComponent_eq_bot_of_ne (p q : IsDedekindDomain.HeightOneSpectrum R)
    (h : p ≠ q) (M : PrimaryModule R q.asIdeal) :
    Ideal.primaryComponent M.obj p.asIdeal = ⊥ := by
  apply (Submodule.eq_bot_iff _).2
  intro x hx
  obtain ⟨a, ha⟩ := (Ideal.primaryComponent_mem M.obj p.asIdeal x).1 hx
  obtain ⟨b, hb⟩ := M.property
  have hd := Submodule.disjoint_torsionBySet_ideal (M := M.obj)
    (p.isCoprime_pow_of_ne q h a b).sup_eq
  exact Submodule.disjoint_def.mp hd x ha
    ((Submodule.mem_torsionBySet_iff _ _).2 (fun r => hb r r.property x))

/-- The actual linear maps underlying a morphism of primary-component families. -/
def primaryHomFamily {M N : TorsionModule R}
    (f : (finitePrimaryFunctor R).obj M ⟶ (finitePrimaryFunctor R).obj N)
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    Ideal.primaryComponent M.obj p.asIdeal →ₗ[R] Ideal.primaryComponent N.obj p.asIdeal :=
  (f.hom p).hom.hom.hom

/-- Reconstruct an actual torsion-module map by summing its prescribed primary-coordinate maps. -/
def reconstructHom {M N : TorsionModule R}
    (f : (finitePrimaryFunctor R).obj M ⟶ (finitePrimaryFunctor R).obj N) : M ⟶ N :=
  ObjectProperty.homMk (FGModuleCat.ofHom ((primarySumLinearEquiv R N).toLinearMap.comp
    ((DirectSum.lmap (primaryHomFamily R f)).comp (primarySumLinearEquiv R M).symm.toLinearMap)))

/-- Reconstruction recovers each originally prescribed actual primary-coordinate map. -/
theorem finitePrimary_map_reconstruct {M N : TorsionModule R}
    (f : (finitePrimaryFunctor R).obj M ⟶ (finitePrimaryFunctor R).obj N) :
    (finitePrimaryFunctor R).map (reconstructHom R f) = f := by
  apply ObjectProperty.hom_ext
  funext p
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Ideal.primaryComponent M.obj p.asIdeal at x
  apply Subtype.ext
  change (primarySumLinearEquiv R N)
      (DirectSum.lmap (primaryHomFamily R f) ((primarySumLinearEquiv R M).symm x.val)) =
    ((f.hom p).hom.hom.hom x).val
  have hx : (primarySumLinearEquiv R M).symm x.val = DirectSum.lof R _
      (fun q : IsDedekindDomain.HeightOneSpectrum R =>
        Ideal.primaryComponent M.obj q.asIdeal) p x := by
    apply (primarySumLinearEquiv R M).injective
    rw [LinearEquiv.apply_symm_apply]
    change x.val = DirectSum.coeLinearMap
      (fun q : IsDedekindDomain.HeightOneSpectrum R => Ideal.primaryComponent M.obj q.asIdeal)
      (DirectSum.lof R _
        (fun q : IsDedekindDomain.HeightOneSpectrum R =>
          Ideal.primaryComponent M.obj q.asIdeal) p x)
    exact (DirectSum.coeLinearMap_lof
      (fun q : IsDedekindDomain.HeightOneSpectrum R =>
        Ideal.primaryComponent M.obj q.asIdeal) p x).symm
  rw [hx, DirectSum.lmap_lof]
  change DirectSum.coeLinearMap
    (fun q : IsDedekindDomain.HeightOneSpectrum R => Ideal.primaryComponent N.obj q.asIdeal)
    (DirectSum.lof R _
      (fun q : IsDedekindDomain.HeightOneSpectrum R =>
        Ideal.primaryComponent N.obj q.asIdeal) p (primaryHomFamily R f p x)) = _
  exact DirectSum.coeLinearMap_lof _ p _

instance finitePrimaryFunctor_faithful : (finitePrimaryFunctor R).Faithful where
  map_injective {M N} {f g} h := by
    have hsum : (primarySumFunctor R).map f = (primarySumFunctor R).map g := by
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (⨁ p : IsDedekindDomain.HeightOneSpectrum R,
        Ideal.primaryComponent M.obj p.asIdeal) at x
      apply DFinsupp.ext
      intro p
      exact congrArg (fun k : (finitePrimaryFunctor R).obj M ⟶ (finitePrimaryFunctor R).obj N =>
        (k.hom p).hom.hom.hom (x p)) h
    apply (FGModuleCat.localizationTorsionProperty R⁰).ι.map_injective
    apply (cancel_epi ((primarySumIso R).hom.app M)).1
    rw [← (primarySumIso R).hom.naturality f, ← (primarySumIso R).hom.naturality g, hsum]

instance finitePrimaryFunctor_full : (finitePrimaryFunctor R).Full where
  map_surjective f := ⟨reconstructHom R f, finitePrimary_map_reconstruct R f⟩

/-- The actual finite-support primary-component functor is fully faithful. -/
def fullyFaithfulFinitePrimary : (finitePrimaryFunctor R).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful _

/-- The canonical finite-support family of actual prime-power primary modules. -/
abbrev FinitePrimaryFamily := Pi.FiniteCategoryFamily
  (fun p : IsDedekindDomain.HeightOneSpectrum R => PrimaryModule R p.asIdeal)

/-- The actual product carrier of a finite-support primary family. -/
abbrev familyProductCarrier (N : FinitePrimaryFamily R) :=
  ∀ p : IsDedekindDomain.HeightOneSpectrum R, (N.obj p).obj

/-- The finite set of nonzero coordinates of an actual primary family. -/
def familySupport (N : FinitePrimaryFamily R) : Finset (IsDedekindDomain.HeightOneSpectrum R) :=
  N.property.toFinset

omit [IsDedekindDomain R] in
/-- Coordinates outside the recorded finite support are arbitrary zero objects. -/
theorem family_isZero_of_not_mem (N : FinitePrimaryFamily R)
    (p : IsDedekindDomain.HeightOneSpectrum R) (hp : p ∉ familySupport R N) : IsZero (N.obj p) := by
  by_contra h
  exact hp (N.property.mem_toFinset.mpr h)

omit [IsDedekindDomain R] in
/-- A zero object of a primary category has a subsingleton actual module carrier. -/
theorem primaryModule_subsingleton (I : Ideal R) (M : PrimaryModule R I) (hM : IsZero M) :
    Subsingleton M.obj :=
  ModuleCat.isZero_iff_subsingleton.1
    ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).map_isZero
      ((primaryObjectProperty R I).ι.map_isZero hM))

instance familyProduct_finite (N : FinitePrimaryFamily R) :
    Module.Finite R (familyProductCarrier R N) := by
  let s := familySupport R N
  let f : familyProductCarrier R N →ₗ[R] (∀ p : s, (N.obj p.1).obj) :=
    LinearMap.pi (fun p => LinearMap.proj p.1)
  have hf : Function.Injective f := by
    intro x y hxy
    funext p
    by_cases hp : p ∈ s
    · exact congrFun hxy ⟨p, hp⟩
    · have hz := primaryModule_subsingleton R p.asIdeal (N.obj p)
        (family_isZero_of_not_mem R N p hp)
      exact @Subsingleton.elim _ hz (x p) (y p)
  exact Module.Finite.of_injective f hf

/-- A prime-power primary module is torsion over the actual Dedekind domain. -/
theorem primaryModule_isTorsion (p : IsDedekindDomain.HeightOneSpectrum R)
    (M : PrimaryModule R p.asIdeal) : Module.IsTorsion R M.obj :=
  (torsion_iff_isTorsion R M.obj).1 (primaryObjectProperty_le_torsion R p _ M.property)

/-- The finite-support product of primary modules is torsion as an actual module. -/
theorem familyProduct_isTorsion (N : FinitePrimaryFamily R) :
    Module.IsTorsion R (familyProductCarrier R N) := by
  intro x
  have ht (p : familySupport R N) : ∃ r : R⁰, (r : R) • x p.1 = 0 :=
    primaryModule_isTorsion R p.1 (N.obj p.1) (x := x p.1)
  choose r hr using ht
  refine ⟨∏ p : familySupport R N, r p, ?_⟩
  funext p
  by_cases hp : p ∈ familySupport R N
  · let j : familySupport R N := ⟨p, hp⟩
    change (↑(∏ q : familySupport R N, r q) : R) • x p = 0
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j)]
    simp only [Submonoid.coe_mul, mul_smul]
    have hj : (r j : R) • x p = 0 := hr j
    change (↑(∏ q ∈ Finset.univ.erase j, r q) : R) • ((r j : R) • x p) = 0
    rw [hj, smul_zero]
  · have hz := primaryModule_subsingleton R p.asIdeal (N.obj p)
      (family_isZero_of_not_mem R N p hp)
    exact @Subsingleton.elim _ hz _ _

/-- The actual module built from an arbitrary finite-support primary family. -/
abbrev familyProductModule (N : FinitePrimaryFamily R) : FGModuleCat.{u} R :=
  FGModuleCat.of R (familyProductCarrier R N)

/-- A finite primary family gives an actual object of the original torsion category. -/
def familyProductTorsion (N : FinitePrimaryFamily R) : TorsionModule R :=
  ⟨familyProductModule R N, (torsion_iff_isTorsion R _).2 (familyProduct_isTorsion R N)⟩

/-- The original product projection restricted to its actual primary component. -/
def familyPrimaryProjection (N : FinitePrimaryFamily R)
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    Ideal.primaryComponent (familyProductCarrier R N) p.asIdeal →ₗ[R] (N.obj p).obj :=
  (LinearMap.proj p).domRestrict _

/-- A primary vector in the product is determined by its coordinate at that prime. -/
theorem familyPrimaryProjection_injective (N : FinitePrimaryFamily R)
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    Function.Injective (familyPrimaryProjection R N p) := by
  intro x y hxy
  change x.val p = y.val p at hxy
  apply Subtype.ext
  funext q
  by_cases hq : q = p
  · subst q
    exact hxy
  · have hbot := primaryComponent_eq_bot_of_ne R p q (Ne.symm hq) (N.obj q)
    have hx : x.val q ∈ Ideal.primaryComponent (N.obj q).obj p.asIdeal :=
      Ideal.primaryComponent_map_mem p.asIdeal (LinearMap.proj q) x
    have hy : y.val q ∈ Ideal.primaryComponent (N.obj q).obj p.asIdeal :=
      Ideal.primaryComponent_map_mem p.asIdeal (LinearMap.proj q) y
    have hx0 : x.val q = 0 := by simpa [hbot] using hx
    have hy0 : y.val q = 0 := by simpa [hbot] using hy
    exact hx0.trans hy0.symm

omit [IsDedekindDomain R] in
/-- Every primary coordinate is recovered by the actual restricted projection. -/
theorem familyPrimaryProjection_surjective (N : FinitePrimaryFamily R)
    (p : IsDedekindDomain.HeightOneSpectrum R) :
    Function.Surjective (familyPrimaryProjection R N p) := by
  intro z
  obtain ⟨n, hn⟩ := (N.obj p).property
  let x : familyProductCarrier R N := Pi.single p z
  have hx : x ∈ Ideal.primaryComponent (familyProductCarrier R N) p.asIdeal := by
    apply (Ideal.primaryComponent_mem _ _ _).2
    refine ⟨n, (Submodule.mem_torsionBySet_iff _ _).2 ?_⟩
    intro r
    funext q
    by_cases hq : q = p
    · subst q
      simpa [x] using hn r r.property z
    · simp [x, hq]
  refine ⟨⟨x, hx⟩, ?_⟩
  change x p = z
  simp [x]

/-- Every actual finite-support primary family comes from an actual finite torsion module. -/
instance finitePrimaryFunctor_essSurj : (finitePrimaryFunctor R).EssSurj where
  mem_essImage N := by
    refine ⟨familyProductTorsion R N, ⟨?_⟩⟩
    apply (Pi.finiteObjectSupport _).isoMk
    apply Pi.isoMk
    intro p
    apply (primaryObjectProperty R p.asIdeal).isoMk
    exact (LinearEquiv.ofBijective (familyPrimaryProjection R N p)
      ⟨familyPrimaryProjection_injective R N p,
        familyPrimaryProjection_surjective R N p⟩).toFGModuleCatIso

instance finitePrimaryFunctor_isEquivalence : (finitePrimaryFunctor R).IsEquivalence := {}

/-- The original torsion category splits into the actual finite family of primary categories. -/
def finitePrimaryEquivalence : TorsionModule R ≌ FinitePrimaryFamily R :=
  (finitePrimaryFunctor R).asEquivalence

@[simp]
theorem finitePrimaryEquivalence_functor :
    (finitePrimaryEquivalence R).functor = finitePrimaryFunctor R := rfl

/-- The inverse of the primary equivalence is exact for the same standard abelian structures. -/
def finitePrimaryInverseExactFunctor : ExactCategory.ExactFunctor
    (Pi.finiteCategoryExactStructure
      (fun p : IsDedekindDomain.HeightOneSpectrum R => PrimaryModule R p.asIdeal))
    (ExactCategory.abelianExactStructure
      (FGModuleCat.localizationTorsionProperty R⁰).FullSubcategory) := by
  let e := finitePrimaryEquivalence R
  have : e.functor.Additive := by
    change (finitePrimaryFunctor R).Additive
    infer_instance
  exact
    { toFunctor := e.inverse
      additive := e.inverse_additive
      map_conflation := fun _ hS => hS.map_of_exact e.inverse }

omit [IsDedekindDomain R] in
/-- The primary component of an actual ideal-power primary module is the whole module. -/
theorem primaryComponent_eq_top (I : Ideal R) (M : PrimaryModule R I) :
    Ideal.primaryComponent M.obj I = ⊤ := by
  obtain ⟨n, hn⟩ := M.property
  apply top_unique
  intro x _
  exact (Ideal.primaryComponent_mem M.obj I x).2
    ⟨n, (Submodule.mem_torsionBySet_iff _ _).2 (fun r => hn r r.property x)⟩

/-- On its primary category the actual component inclusion is an isomorphism. -/
def primaryIdentityIsoApp (I : Ideal R) (M : PrimaryModule R I) :
    ((primaryObjectProperty R I).ι ⋙ componentToPrimary R I).obj M ≅ M := by
  apply (primaryObjectProperty R I).isoMk
  apply LinearEquiv.toFGModuleCatIso
  apply LinearEquiv.ofBijective (Ideal.primaryComponent M.obj I).subtype
  refine ⟨Subtype.val_injective, ?_⟩
  intro x
  refine ⟨⟨x, ?_⟩, rfl⟩
  rw [primaryComponent_eq_top R I M]
  trivial

/-- The component inclusion canonically identifies a primary category with its own component. -/
def primaryIdentityIso (I : Ideal R) :
    (primaryObjectProperty R I).ι ⋙ componentToPrimary R I ≅ 𝟭 (PrimaryModule R I) :=
  NatIso.ofComponents (primaryIdentityIsoApp R I) (by
    intro M N f
    apply ObjectProperty.hom_ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl)

/-- The primary-to-torsion inclusion is recovered by its original primary coordinate. -/
def primaryInclusionComponentIso (p : IsDedekindDomain.HeightOneSpectrum R) :
    primaryToTorsion R p ⋙ torsionPrimaryFunctor R p.asIdeal ≅ 𝟭 (PrimaryModule R p.asIdeal) :=
  primaryIdentityIso R p.asIdeal

/-- Inclusion of a primary module has an actual zero component at every other prime. -/
theorem primaryInclusionOtherComponent_isZero (p q : IsDedekindDomain.HeightOneSpectrum R)
    (h : p ≠ q) (M : PrimaryModule R p.asIdeal) :
    IsZero ((primaryToTorsion R p ⋙ torsionPrimaryFunctor R q.asIdeal).obj M) := by
  have hb := primaryComponent_eq_bot_of_ne R q p (Ne.symm h) M
  have : Subsingleton (Ideal.primaryComponent M.obj q.asIdeal) := by
    rw [hb]
    infer_instance
  apply IsZero.of_full_of_faithful_of_isZero (primaryObjectProperty R q.asIdeal).ι
  apply IsZero.of_full_of_faithful_of_isZero (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R))
  change IsZero (ModuleCat.of R (Ideal.primaryComponent M.obj q.asIdeal))
  exact ModuleCat.isZero_of_subsingleton _

/-- Other primary coordinates on an included primary category are canonically zero. -/
def primaryInclusionOtherComponentIso (p q : IsDedekindDomain.HeightOneSpectrum R) (h : p ≠ q) :
    primaryToTorsion R p ⋙ torsionPrimaryFunctor R q.asIdeal ≅
      (0 : PrimaryModule R p.asIdeal ⥤ PrimaryModule R q.asIdeal) :=
  NatIso.ofComponents
    (fun M => (primaryInclusionOtherComponent_isZero R p q h M).iso (Functor.zero_obj M)) (by
      intro M N f
      exact (primaryInclusionOtherComponent_isZero R p q h M).eq_of_src _ _)

end Dedekind

end FGModuleCat.PrimaryDecomposition
