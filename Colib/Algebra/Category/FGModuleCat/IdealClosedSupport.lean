/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.ExactCategory.Abelian
public import Colib.CategoryTheory.ExactCategory.Functor.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Finite modules on an ideal closed subscheme

The actual quotient restriction identifies finite quotient modules with finite modules
annihilated by the ideal. This generalizes the native principal closed-support construction;
its role in the Quillen Dedekind proof is the original quotient restriction, not a new model.
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FGModuleCat.IdealSupport

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The coordinate ring of the principal closed subscheme defined by `I`. -/
abbrev ClosedRing := R ⧸ I

/-- Finite modules annihilated by `I`, rather than merely by a power of `I`. -/
def killedBy : ObjectProperty (FGModuleCat.{v} R) := fun M ↦ ∀ r ∈ I, ∀ m : M, r • m = 0

/-- The annihilation predicate is the ideal containment in the module annihilator. -/
theorem killedBy_iff_le_annihilator (M : FGModuleCat.{v} R) :
    killedBy I M ↔ I ≤ Module.annihilator R M := by
  simp only [killedBy, IsConcreteLE.le_iff, Module.mem_annihilator]

/-- Actual restriction of scalars along the principal quotient map, on finite modules. -/
def closedRestriction : FGModuleCat.{v} (ClosedRing I) ⥤ FGModuleCat.{v} R :=
  (ModuleCat.isFG R).lift
    (forget₂ (FGModuleCat.{v} (ClosedRing I)) (ModuleCat.{v} (ClosedRing I)) ⋙
      ModuleCat.restrictScalars (Ideal.Quotient.mk (I))) (fun M ↦ by
    change Module.Finite R ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I))).obj
      M.obj)
    let N := (ModuleCat.restrictScalars (Ideal.Quotient.mk (I))).obj M.obj
    have : Module.Finite (ClosedRing I) N := M.property
    have : IsScalarTower R (ClosedRing I) N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    exact Module.Finite.trans (ClosedRing I) N)

@[simp]
theorem closedRestriction_obj_obj (M : FGModuleCat.{v} (ClosedRing I)) :
    ((closedRestriction I).obj M).obj =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I))).obj M.obj := rfl

@[simp]
theorem closedRestriction_map_hom {M N : FGModuleCat.{v} (ClosedRing I)} (g : M ⟶ N) :
    ((closedRestriction I).map g).hom =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I))).map g.hom := rfl

/-- Forgetting finite generation leaves the literal native restriction-of-scalars functor. -/
theorem closedRestriction_comp_forget :
    closedRestriction.{u, v} I ⋙ forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) =
      forget₂ (FGModuleCat.{v} (ClosedRing I)) (ModuleCat.{v} (ClosedRing I)) ⋙
        ModuleCat.restrictScalars (Ideal.Quotient.mk (I)) := rfl

/-- Every quotient-ring module is annihilated by the defining element. -/
theorem closedRestriction_killed (M : FGModuleCat.{v} (ClosedRing I)) :
    killedBy I ((closedRestriction I).obj M) := by
  intro r hr m
  change M at m
  change (Ideal.Quotient.mk I r) • (m : M) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]

/-- Restriction of scalars with codomain restricted to the actual annihilated objects. -/
def closedToKilled : FGModuleCat.{v} (ClosedRing I) ⥤ (killedBy I).FullSubcategory :=
  (killedBy I).lift (closedRestriction I) (closedRestriction_killed I)

/-- The annihilated-object factorization retains the actual restriction functor. -/
theorem closedToKilled_comp_inclusion :
    closedToKilled.{u, v} I ⋙ (killedBy I).ι = closedRestriction I := rfl

/-- Quotient-map surjectivity recovers quotient-ring linearity from `R`-linearity. -/
def fullyFaithfulClosedRestriction : (closedRestriction.{u, v} I).FullyFaithful where
  preimage {M N} g := FGModuleCat.ofHom
    { toFun := g.hom.hom
      map_add' := g.hom.hom.map_add
      map_smul' := by
        intro a m
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact g.hom.hom.map_smul s m }

instance closedRestriction_full : (closedRestriction.{u, v} I).Full :=
  (fullyFaithfulClosedRestriction I).full

instance closedRestriction_faithful : (closedRestriction.{u, v} I).Faithful :=
  (fullyFaithfulClosedRestriction I).faithful

instance closedToKilled_full : (closedToKilled.{u, v} I).Full := by
  constructor
  intro M N g
  obtain ⟨h, hh⟩ := (closedRestriction I).map_surjective g.hom
  exact ⟨h, ObjectProperty.hom_ext _ hh⟩

instance closedToKilled_faithful : (closedToKilled.{u, v} I).Faithful where
  map_injective h := (closedRestriction I).map_injective (congrArg (fun k ↦ k.hom) h)

/-- Every finite annihilated `R`-module has its genuine quotient-ring module structure. -/
instance closedToKilled_essSurj : (closedToKilled.{u, v} I).EssSurj where
  mem_essImage M := by
    have hM : Module.IsTorsionBySet R M.obj I := fun m r ↦ M.property r.val r.property m
    let : Module (ClosedRing I) M.obj := hM.module
    let : IsScalarTower R (ClosedRing I) M.obj :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let : Module.Finite (ClosedRing I) M.obj :=
      Module.Finite.of_restrictScalars_finite R (ClosedRing I) M.obj
    refine ⟨FGModuleCat.of (ClosedRing I) M.obj, ⟨?_⟩⟩
    apply ObjectProperty.isoMk
    apply ObjectProperty.isoMk
    exact (LinearEquiv.refl R M.obj).toModuleIso

instance closedToKilled_isEquivalence : (closedToKilled.{u, v} I).IsEquivalence := {}

/-- The actual quotient-ring restriction equivalence onto exactly the `I`-killed objects. -/
def closedEquivalence : FGModuleCat.{v} (ClosedRing I) ≌ (killedBy I).FullSubcategory :=
  (closedToKilled I).asEquivalence

/-- The quotient equivalence followed by the full inclusion is actual restriction of scalars. -/
theorem closedEquivalence_comp_inclusion :
    (closedEquivalence.{u, v} I).functor ⋙ (killedBy I).ι = closedRestriction I := rfl

/-- A finite module belongs to the essential image precisely when `I` kills it. -/
theorem closedRestriction_essImage_iff (M : FGModuleCat.{v} R) :
    (closedRestriction I).essImage M ↔ killedBy I M := by
  constructor
  · rintro ⟨N, ⟨e⟩⟩ r hr m
    obtain ⟨n, rfl⟩ := (isoToLinearEquiv e).surjective m
    simpa only [map_smul, map_zero] using
      congrArg (isoToLinearEquiv e) (closedRestriction_killed I N r hr n)
  · intro hM
    obtain ⟨N, ⟨e⟩⟩ :=
      Functor.EssSurj.mem_essImage (closedToKilled I) ⟨M, hM⟩
    exact ⟨N, ⟨(killedBy I).ι.mapIso e⟩⟩

/-- The essential-image object property is exactly annihilation by `I`. -/
theorem closedRestriction_essImage :
    (closedRestriction.{u, v} I).essImage = killedBy I := by
  funext M
  exact propext (closedRestriction_essImage_iff I M)

instance killedBy_isClosedUnderIsomorphisms :
    (killedBy.{u, v} I).IsClosedUnderIsomorphisms := by
  rw [← closedRestriction_essImage]
  infer_instance

instance closedRestriction_additive : (closedRestriction.{u, v} I).Additive where
  map_add := by intros; apply FGModuleCat.hom_ext; rfl

instance closedToKilled_additive : (closedToKilled.{u, v} I).Additive where
  map_add := by intros; apply ObjectProperty.hom_ext; apply FGModuleCat.hom_ext; rfl

instance closedRestriction_preservesFiniteColimits :
    PreservesFiniteColimits (closedRestriction.{u, v} I) := by
  have : PreservesFiniteColimits
      (closedRestriction I ⋙ forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)) := by
    rw [closedRestriction_comp_forget]
    exact comp_preservesFiniteColimits
      (forget₂ (FGModuleCat.{v} (ClosedRing I)) (ModuleCat.{v} (ClosedRing I)))
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I)))
  exact preservesFiniteColimits_of_reflects_of_preserves (closedRestriction I)
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R))

variable [IsNoetherianRing R]

instance closedRestriction_preservesFiniteLimits :
    PreservesFiniteLimits (closedRestriction.{u, v} I) := by
  have : PreservesFiniteLimits
      (closedRestriction I ⋙ forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)) := by
    rw [closedRestriction_comp_forget]
    exact comp_preservesFiniteLimits
      (forget₂ (FGModuleCat.{v} (ClosedRing I)) (ModuleCat.{v} (ClosedRing I)))
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (I)))
  exact preservesFiniteLimits_of_reflects_of_preserves (closedRestriction I)
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R))

/-- The genuine principal closed restriction is exact for the standard abelian structures. -/
def closedRestrictionExact :
    ExactFunctor (abelianExactStructure (FGModuleCat.{v} (ClosedRing I)))
      (abelianExactStructure (FGModuleCat.{v} R)) where
  toFunctor := closedRestriction I
  map_conflation _ h := h.map_of_exact _

@[simp]
theorem closedRestrictionExact_toFunctor :
    (closedRestrictionExact.{u, v} I).toFunctor = closedRestriction I := rfl

end FGModuleCat.IdealSupport
