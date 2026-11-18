/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology
public import Colib.CategoryTheory.Sites.RelativeCohomology.BoundaryNaturality
public import StacksFrontier.CategoryTheory.Abelian.ExtAdjunctionAcyclic
import all Colib.AlgebraicGeometry.SheavesWithTransfers.Zariski.Cohomology.ChangeOfTopology

/-!
# Change of topology for the original relative cohomology groups

Exact inverse image carries the free representing sheaves and their relative
cokernel to the corresponding objects for the finer topology. The comparison
applies inverse image to Ext and then uses the counit on the coefficient sheaf.
Naturality of the actual short exact presentations gives compatibility with
the signed boundary.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w t v u

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J K : GrothendieckTopology C)

set_option hygiene false in
set_option quotPrecheck false in
local notation "A" => AddCommGrpCat.{max v t}

variable [HasSheafify J A] [HasSheafify K A]
  {L : Sheaf J A ⥤ Sheaf K A} {R : Sheaf K A ⥤ Sheaf J A}
  [L.Additive] [PreservesFiniteColimits L]

variable (e : freeYoneda.{t} J ⋙ L ≅ freeYoneda.{t} K)
variable {U X : C} (j : U ⟶ X)

/-- Exact inverse image carries the original relative cokernel to the original finer cokernel. -/
def relativeRefinementSourceIso : L.obj (relativeSource J j) ≅ relativeSource K j :=
  PreservesCokernel.iso L ((freeYoneda.{t} J).map j) ≪≫
    cokernel.mapIso _ _ (e.app U) (e.app X) (e.hom.naturality j)

/-- The cokernel comparison identifies the actual quotient maps. -/
@[reassoc]
theorem relativeRefinementSourceIso_π :
    L.map (relativeSourceπ J j) ≫ (relativeRefinementSourceIso J K e j).hom =
      e.hom.app X ≫ relativeSourceπ K j := by
  let f := (freeYoneda.{t} J).map j
  let f' := (freeYoneda.{t} K).map j
  change L.map (cokernel.π f) ≫
    (PreservesCokernel.iso L f ≪≫
      cokernel.mapIso (L.map f) f' (e.app U) (e.app X) (e.hom.naturality j)).hom =
    e.hom.app X ≫ cokernel.π f'
  simp only [Iso.trans_hom, PreservesCokernel.π_iso_hom_assoc,
    cokernel.mapIso_hom, cokernel.map, cokernel.π_desc, Iso.app_hom]

private def relativeRefinementPresentationMap :
    (relativePresentation J j).map L ⟶ relativePresentation K j where
  τ₁ := e.hom.app U
  τ₂ := e.hom.app X
  τ₃ := (relativeRefinementSourceIso J K e j).hom
  comm₁₂ := (e.hom.naturality j).symm
  comm₂₃ := (relativeRefinementSourceIso_π J K e j).symm

variable {V Y : C} (j' : V ⟶ Y) (a : U ⟶ V) (b : X ⟶ Y)
  (h : j ≫ b = a ≫ j')

/-- The source comparison commutes with the actual map of relative cokernels. -/
theorem relativeRefinementSourceIso_naturality :
    L.map (relativeSourceMap J j j' a b h) ≫ (relativeRefinementSourceIso J K e j').hom =
      (relativeRefinementSourceIso J K e j).hom ≫ relativeSourceMap K j j' a b h := by
  have hπ : Epi (relativeSourceπ K j) := by
    change Epi (cokernel.π ((freeYoneda.{t} K).map j))
    infer_instance
  have hπL : Epi (L.map (relativeSourceπ J j)) := by
    have : Epi (L.map (relativeSourceπ J j) ≫ (relativeRefinementSourceIso J K e j).hom) := by
      rw [relativeRefinementSourceIso_π]
      infer_instance
    exact (epi_comp_iff_of_isIso (L.map (relativeSourceπ J j))
      (relativeRefinementSourceIso J K e j).hom).mp this
  apply (cancel_epi (L.map (relativeSourceπ J j))).mp
  calc
    _ = L.map (relativeSourceπ J j ≫ relativeSourceMap J j j' a b h) ≫
        (relativeRefinementSourceIso J K e j').hom := by rw [Functor.map_comp_assoc]
    _ = L.map ((freeYoneda.{t} J).map b) ≫ e.hom.app Y ≫ relativeSourceπ K j' := by
      rw [relativeSourceπ_naturality, Functor.map_comp_assoc, relativeRefinementSourceIso_π]
    _ = e.hom.app X ≫ (freeYoneda.{t} K).map b ≫ relativeSourceπ K j' := by
      exact (reassoc_of% (e.hom.naturality b)) (relativeSourceπ K j')
    _ = _ := by rw [← relativeSourceπ_naturality K j j' a b h, relativeRefinementSourceIso_π_assoc]

variable (adj : L ⊣ R) [PreservesFiniteLimits L] [HasExt.{w} (Sheaf J A)] [HasExt.{w} (Sheaf K A)]

private def refinementExtMap {B : Sheaf J A} {B' : Sheaf K A}
    (i : L.obj B ≅ B') (F : Sheaf K A) (n : ℕ) :
    Ext.{w} B (R.obj F) n →+ Ext.{w} B' F n :=
  ((Ext.mk₀ i.inv).precomp F (zero_add n)).comp (Stacks.ExtAdjunction.extMap adj B F n)

private theorem refinementExtMap_apply {B : Sheaf J A} {B' : Sheaf K A}
    (i : L.obj B ≅ B') (F : Sheaf K A) (n : ℕ) (x : Ext.{w} B (R.obj F) n) :
    refinementExtMap J K adj i F n x =
      (Ext.mk₀ i.inv).comp
        ((x.mapExactFunctor L).comp (Ext.mk₀ (adj.counit.app F)) (add_zero n)) (zero_add n) :=
  rfl

private theorem refinementExtMap_precomp {B D : Sheaf J A} {B' D' : Sheaf K A}
    (i : L.obj B ≅ B') (i' : L.obj D ≅ D') (f : D ⟶ B) (g : D' ⟶ B')
    (hfg : L.map f ≫ i.hom = i'.hom ≫ g)
    (F : Sheaf K A) (n : ℕ) (x : Ext.{w} B (R.obj F) n) :
    refinementExtMap J K adj i' F n ((Ext.mk₀ f).comp x (zero_add n)) =
      (Ext.mk₀ g).comp (refinementExtMap J K adj i F n x) (zero_add n) := by
  have hi : i'.inv ≫ L.map f = g ≫ i.inv := by
    apply (cancel_mono i.hom).mp
    simp [Category.assoc, hfg]
  simp only [refinementExtMap_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀_assoc, hi]

private theorem refinementExtMap_postcomp {B : Sheaf J A} {B' : Sheaf K A}
    (i : L.obj B ≅ B') {F G : Sheaf K A} (f : F ⟶ G)
    (n : ℕ) (x : Ext.{w} B (R.obj F) n) :
    refinementExtMap J K adj i G n (x.comp (Ext.mk₀ (R.map f)) (add_zero n)) =
      (refinementExtMap J K adj i F n x).comp (Ext.mk₀ f) (add_zero n) := by
  change (Ext.mk₀ i.inv).comp
    (Stacks.ExtAdjunction.extMap adj B G n (x.comp (Ext.mk₀ (R.map f)) (add_zero n)))
      (zero_add n) =
    ((Ext.mk₀ i.inv).comp (Stacks.ExtAdjunction.extMap adj B F n x) (zero_add n)).comp
      (Ext.mk₀ f) (add_zero n)
  rw [Stacks.ExtAdjunction.extMap_naturality_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- Ordinary cohomology comparison given by exact inverse image and the counit, evaluated at
the actual free representing sheaf. -/
@[no_expose]
def refinementCohomologyComparisonAt (F : Sheaf K A) (n : ℕ) (T : C) :
    (cohomologyPresheaf.{w, t} (R.obj F) n).obj (op T) ⟶
      (cohomologyPresheaf.{w, t} F n).obj (op T) := by
  change AddCommGrpCat.of (Ext.{w} ((freeYoneda.{t} J).obj T) (R.obj F) n) ⟶
    AddCommGrpCat.of (Ext.{w} ((freeYoneda.{t} K).obj T) F n)
  exact AddCommGrpCat.ofHom (refinementExtMap.{w, t} J K adj (e.app T) F n)

/-- The canonical comparison of relative cohomology using the existing relative sources. -/
@[no_expose]
def relativeRefinementComparison (F : Sheaf K A) (n : ℕ) :
    relativeH.{w, t} J j (R.obj F) n ⟶ relativeH.{w, t} K j F n := by
  change AddCommGrpCat.of (Ext.{w} (relativeSource.{t} J j) (R.obj F) n) ⟶
    AddCommGrpCat.of (Ext.{w} (relativeSource.{t} K j) F n)
  exact AddCommGrpCat.ofHom
    (refinementExtMap.{w, t} J K adj (relativeRefinementSourceIso J K e j) F n)

/-- The relative comparison commutes with the existing relative restriction on pairs. -/
theorem relativeRefinementComparison_restriction (F : Sheaf K A) (n : ℕ) :
    relativeRestriction.{w, t} J j j' a b h (R.obj F) n ≫
        relativeRefinementComparison.{w, t} J K e j adj F n =
      relativeRefinementComparison.{w, t} J K e j' adj F n ≫
        relativeRestriction.{w, t} K j j' a b h F n := by
  ext x
  exact refinementExtMap_precomp.{w, t} J K adj _ _ _ _
    (relativeRefinementSourceIso_naturality J K e j j' a b h) F n x

/-- The relative comparison commutes with the existing coefficient maps. -/
theorem relativeRefinementComparison_coefficient {F G : Sheaf K A} (f : F ⟶ G) (n : ℕ) :
    relativeCoefficientMap.{w, t} J j (R.map f) n ≫
        relativeRefinementComparison.{w, t} J K e j adj G n =
      relativeRefinementComparison.{w, t} J K e j adj F n ≫
        relativeCoefficientMap.{w, t} K j f n := by
  ext x
  exact refinementExtMap_postcomp.{w, t} J K adj (relativeRefinementSourceIso J K e j) f n x

/-- The relative comparison commutes with forgetting the support condition. -/
theorem relativeRefinementComparison_forget (F : Sheaf K A) (n : ℕ) :
    relativeForget.{w, t} J j (R.obj F) n ≫
        refinementCohomologyComparisonAt.{w, t} J K e adj F n X =
      relativeRefinementComparison.{w, t} J K e j adj F n ≫ relativeForget.{w, t} K j F n := by
  ext x
  exact refinementExtMap_precomp.{w, t} J K adj (relativeRefinementSourceIso J K e j) (e.app X)
    (relativeSourceπ J j) (relativeSourceπ K j) (relativeRefinementSourceIso_π J K e j) F n x

section Boundary

variable [Mono j]

private theorem relativeRefinementExtClass :
    (Ext.mk₀ (relativeRefinementSourceIso J K e j).inv).comp
        ((relativeExtClass J j).mapExactFunctor L) (zero_add 1) =
      (relativeExtClass K j).comp (Ext.mk₀ (e.inv.app U)) (add_zero 1) := by
  have hn := ShortComplex.ShortExact.extClass_naturality
    ((relativePresentation_shortExact J j).map_of_exact L)
    (relativePresentation_shortExact K j) (relativeRefinementPresentationMap J K e j)
  rw [← Ext.mapExactFunctor_extClass] at hn
  change ((relativeExtClass J j).mapExactFunctor L).comp (Ext.mk₀ (e.hom.app U))
      (add_zero 1) =
    (Ext.mk₀ (relativeRefinementSourceIso J K e j).hom).comp (relativeExtClass K j) (zero_add 1)
    at hn
  apply (Stacks.ExtAdjunction.postcomp_mk₀_bijective_of_isIso (e.hom.app U) 1).injective
  change ((Ext.mk₀ (relativeRefinementSourceIso J K e j).inv).comp
      ((relativeExtClass J j).mapExactFunctor L) (zero_add 1)).comp (Ext.mk₀ (e.hom.app U))
      (add_zero 1) =
    ((relativeExtClass K j).comp (Ext.mk₀ (e.inv.app U)) (add_zero 1)).comp
      (Ext.mk₀ (e.hom.app U)) (add_zero 1)
  rw [Ext.comp_assoc_of_third_deg_zero, hn, Ext.mk₀_comp_mk₀_assoc, Iso.inv_hom_id,
    Ext.mk₀_id_comp, Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.inv_hom_id_app,
    Ext.comp_mk₀_id]

private theorem relativeRefinementComparison_connecting (F : Sheaf K A) (n : ℕ)
    (x : (cohomologyPresheaf.{w, t} (R.obj F) n).obj (op U)) :
    relativeRefinementComparison.{w, t} J K e j adj F (n + 1)
        (relativeConnecting.{w, t} J j (R.obj F) n x) =
      relativeConnecting.{w, t} K j F n
        (refinementCohomologyComparisonAt.{w, t} J K e adj F n U x) := by
  change Ext.{w} ((freeYoneda.{t} J).obj U) (R.obj F) n at x
  change refinementExtMap.{w, t} J K adj (relativeRefinementSourceIso J K e j) F (n + 1)
      ((relativeExtClass J j).comp x (Nat.add_comm 1 n)) =
    (relativeExtClass K j).comp (refinementExtMap.{w, t} J K adj (e.app U) F n x) (Nat.add_comm 1 n)
  simp only [refinementExtMap_apply, Ext.mapExactFunctor_comp, Ext.comp_assoc_of_third_deg_zero]
  rw [← Ext.comp_assoc _ _ _ (zero_add 1) (Nat.add_comm 1 n) (by omega),
    relativeRefinementExtClass J K e j, Ext.comp_assoc_of_second_deg_zero]
  rfl

/-- The comparison preserves the original signed localization boundary in every degree. -/
theorem relativeRefinementComparison_boundary (F : Sheaf K A) (n : ℕ) :
    relativeBoundary.{w, t} J j (R.obj F) n ≫
        relativeRefinementComparison.{w, t} J K e j adj F (n + 1) =
      refinementCohomologyComparisonAt.{w, t} J K e adj F n U ≫
        relativeBoundary.{w, t} K j F n := by
  ext x
  simp only [ConcreteCategory.comp_apply, relativeBoundary_apply, Units.smul_def, map_zsmul]
  rw [relativeRefinementComparison_connecting]

end Boundary

variable [R.Additive] [PreservesFiniteLimits R] [EnoughInjectives (Sheaf K A)]

/-- A coefficient with vanishing higher direct images gives an isomorphism on relative
cohomology, using the adjunction comparison on the original relative source. -/
theorem isIso_relativeRefinementComparison (F : Sheaf K A) (n : ℕ)
    (hF : ∀ p : ℕ, 0 < p → IsZero ((R.rightDerived p).obj F)) :
    IsIso (relativeRefinementComparison.{w, t} J K e j adj F n) := by
  let := HasDerivedCategory.standard (Sheaf J A)
  let := HasDerivedCategory.standard (Sheaf K A)
  have hMap : Function.Bijective
      (Stacks.ExtAdjunction.extMap adj (relativeSource J j) F n :
        Ext.{w} (relativeSource J j) (R.obj F) n → Ext.{w} (L.obj (relativeSource J j)) F n) :=
    Stacks.ExtAdjunction.extMap_bijective_of_acyclicClass adj R.rightAcyclic
      (fun I hI ↦ have := hI; Functor.rightAcyclic_of_injective R I)
      Stacks.ExtAdjunction.rightAcyclic_shortExact_map_of_injective
      (relativeSource J j) F ((Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat R F).2 hF) n
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  change Function.Bijective (refinementExtMap.{w, t} J K adj
    (relativeRefinementSourceIso J K e j) F n)
  exact (Stacks.ExtAdjunction.precomp_mk₀_bijective_of_isIso
    (relativeRefinementSourceIso J K e j).inv n).comp hMap

end Stacks.Cohomology.FreeYonedaUnivLE

namespace Stacks.Cohomology.FreeYonedaUnivLE

variable {C : Type u} [Category.{v} C] (J K : GrothendieckTopology C)
  [(𝟭 C).IsContinuous J K]

set_option hygiene false in
set_option quotPrecheck false in
local notation "Ab" => AddCommGrpCat.{max u v t}

variable [HasSheafify J Ab] [HasSheafify K Ab]

/-- Finer sheafification carries each original free representing sheaf to the finer one. -/
@[no_expose]
def refinementFreeYonedaIso :
    freeYoneda.{max u t} J ⋙ (sheafToPresheaf J Ab ⋙ presheafToSheaf K Ab) ≅
      freeYoneda.{max u t} K :=
  Functor.isoWhiskerLeft
    (uliftYoneda.{max u t} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free)
    (((sheafificationAdjunction J Ab).comp (coarseningAdjunction.{t} J K)).leftAdjointUniq
      (sheafificationAdjunction K Ab))


set_option quotPrecheck false in
local notation "P" => (𝟭 C).sheafPushforwardContinuous Ab J K
local notation "L" => sheafToPresheaf J Ab ⋙ presheafToSheaf K Ab

/-- The exact finer sheafification adjunction used by the cohomology comparison. -/
@[no_expose]
def refinementSheafAdjunction : L ⊣ P :=
  coarseningAdjunction.{t} J K

variable [HasExt.{max u v t} (Sheaf J Ab)] [HasExt.{max u v t} (Sheaf K Ab)]

/-- The exact-refinement map on cohomology of a represented object. -/
abbrev cohomologyChangeOfTopologyViaRefinementAt (F : Sheaf K Ab) (n : ℕ) (X : C) :=
  letI := (refinementSheafAdjunction.{t} J K).isLeftAdjoint
  letI : (L).Additive := Functor.additive_of_preserves_binary_products _
  refinementCohomologyComparisonAt.{max u v t, max u t} J K (refinementFreeYonedaIso.{t} J K)
    (refinementSheafAdjunction.{t} J K) F n X

variable {U X : C} (j : U ⟶ X)

/-- The exact-refinement map on the original relative Ext groups. -/
abbrev relativeCohomologyChangeOfTopology (F : Sheaf K Ab) (n : ℕ) :=
  letI := (refinementSheafAdjunction.{t} J K).isLeftAdjoint
  letI : (L).Additive := Functor.additive_of_preserves_binary_products _
  relativeRefinementComparison.{max u v t, max u t} J K (refinementFreeYonedaIso.{t} J K) j
    (refinementSheafAdjunction.{t} J K) F n

/-- The exact-refinement map commutes with the existing forget-support map. -/
theorem relativeCohomologyChangeOfTopology_forget (F : Sheaf K Ab) (n : ℕ) :
    relativeForget.{max u v t, max u t} J j ((P).obj F) n ≫
        cohomologyChangeOfTopologyViaRefinementAt.{t} J K F n X =
      relativeCohomologyChangeOfTopology.{t} J K j F n ≫
        relativeForget.{max u v t, max u t} K j F n :=
  letI := (refinementSheafAdjunction.{t} J K).isLeftAdjoint
  letI : (L).Additive := Functor.additive_of_preserves_binary_products _
  relativeRefinementComparison_forget.{max u v t, max u t} J K
    (refinementFreeYonedaIso.{t} J K) j (refinementSheafAdjunction.{t} J K) F n

/-- The exact-refinement map is natural in the coefficients. -/
theorem relativeCohomologyChangeOfTopology_coefficient {F G : Sheaf K Ab}
    (f : F ⟶ G) (n : ℕ) :
    relativeCoefficientMap.{max u v t, max u t} J j ((P).map f) n ≫
        relativeCohomologyChangeOfTopology.{t} J K j G n =
      relativeCohomologyChangeOfTopology.{t} J K j F n ≫
        relativeCoefficientMap.{max u v t, max u t} K j f n :=
  letI := (refinementSheafAdjunction.{t} J K).isLeftAdjoint
  letI : (L).Additive := Functor.additive_of_preserves_binary_products _
  relativeRefinementComparison_coefficient.{max u v t, max u t} J K
    (refinementFreeYonedaIso.{t} J K) j (refinementSheafAdjunction.{t} J K) f n

/-- The exact-refinement map is natural in the square of site morphisms. -/
theorem relativeCohomologyChangeOfTopology_restriction {V Y : C}
    (j' : V ⟶ Y) (a : U ⟶ V) (b : X ⟶ Y) (h : j ≫ b = a ≫ j')
    (F : Sheaf K Ab) (n : ℕ) :
    relativeRestriction.{max u v t, max u t} J j j' a b h ((P).obj F) n ≫
        relativeCohomologyChangeOfTopology.{t} J K j F n =
      relativeCohomologyChangeOfTopology.{t} J K j' F n ≫
        relativeRestriction.{max u v t, max u t} K j j' a b h F n :=
  letI := (refinementSheafAdjunction.{t} J K).isLeftAdjoint
  letI : (L).Additive := Functor.additive_of_preserves_binary_products _
  relativeRefinementComparison_restriction.{max u v t, max u t} J K
    (refinementFreeYonedaIso.{t} J K) j j' a b h (refinementSheafAdjunction.{t} J K) F n

/-- The exact-refinement map commutes with the original signed localization boundary. -/
theorem relativeCohomologyChangeOfTopology_boundary [Mono j] (F : Sheaf K Ab) (n : ℕ) :
    relativeBoundary.{max u v t, max u t} J j ((P).obj F) n ≫
        relativeCohomologyChangeOfTopology.{t} J K j F (n + 1) =
      cohomologyChangeOfTopologyViaRefinementAt.{t} J K F n U ≫
        relativeBoundary.{max u v t, max u t} K j F n :=
  letI := (refinementSheafAdjunction.{t} J K).isLeftAdjoint
  letI : (L).Additive := Functor.additive_of_preserves_binary_products _
  relativeRefinementComparison_boundary.{max u v t, max u t} J K
    (refinementFreeYonedaIso.{t} J K) j (refinementSheafAdjunction.{t} J K) F n

variable [EnoughInjectives (Sheaf K Ab)]

/-- Vanishing of higher direct images gives the relative change-of-topology isomorphism. -/
theorem isIso_relativeCohomologyChangeOfTopology (F : Sheaf K Ab) (n : ℕ)
    (hF : ∀ p : ℕ, 0 < p → IsZero (((P).rightDerived p).obj F)) :
    IsIso (relativeCohomologyChangeOfTopology.{t} J K j F n) := by
  let := (refinementSheafAdjunction.{t} J K).isLeftAdjoint
  let : (L).Additive := Functor.additive_of_preserves_binary_products _
  let := coarsening_preservesFiniteLimits.{t} J K
  exact isIso_relativeRefinementComparison.{max u v t, max u t} J K
    (refinementFreeYonedaIso.{t} J K) j (refinementSheafAdjunction.{t} J K) F n hF

end Stacks.Cohomology.FreeYonedaUnivLE

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open Stacks.Cohomology.FreeYonedaUnivLE

variable (k : Type u) [Field k]

local notation "B" => Spec (CommRingCat.of k)
local notation "J" => SmoothSite.zariskiTopology B
local notation "K" => SmoothSite.nisnevichTopology B
set_option hygiene false in
set_option quotPrecheck false in
local notation "P" => SmoothSite.nisnevichToZariskiSheaf B AddCommGrpCat.{u + 1}

/-- The exact-refinement map on ordinary Ext cohomology at a smooth scheme. -/
abbrev zariskiRefinementCohomologyComparisonAt (F : SheafWithTransfers.{u + 1} k) (n : ℕ)
    (T : SmoothSite B) :=
  cohomologyChangeOfTopologyViaRefinementAt.{u + 1} J K ((toSheaf k).obj F) n T

/-- The canonical Zariski-to-Nisnevich map on the original relative Ext groups. -/
abbrev zariskiRelativeCohomologyComparison {U X : SmoothSite B} (j : U ⟶ X)
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :=
  relativeCohomologyChangeOfTopology.{u + 1} (C := SmoothSite B) J K (U := U) (X := X) j
    ((toSheaf k).obj F) n

/-- Comparison commutes with the actual forget-support map. -/
theorem zariskiRelativeCohomologyComparison_forget {U X : SmoothSite B} (j : U ⟶ X)
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    let FNis := (toSheaf k).obj F
    let FZar := (P).obj FNis
    let forgetZar := relativeForget.{u + 1, u + 1} J j FZar n
    let forgetNis := relativeForget.{u + 1, u + 1} K j FNis n
    let compareAt := zariskiRefinementCohomologyComparisonAt k F n X
    let compareRelative := zariskiRelativeCohomologyComparison k j F n
    forgetZar ≫ compareAt = compareRelative ≫ forgetNis :=
  relativeCohomologyChangeOfTopology_forget.{u + 1} (C := SmoothSite B) J K (U := U) (X := X) j
    ((toSheaf k).obj F) n

/-- Comparison commutes with the existing coefficient maps on relative Ext. -/
theorem zariskiRelativeCohomologyComparison_coefficient {U X : SmoothSite B} (j : U ⟶ X)
    {F G : SheafWithTransfers.{u + 1} k} (f : F ⟶ G) (n : ℕ) :
    let fNis := (toSheaf k).map f
    let mapZar := relativeCoefficientMap.{u + 1, u + 1} J j ((P).map fNis) n
    let mapNis := relativeCoefficientMap.{u + 1, u + 1} K j fNis n
    let compareF := zariskiRelativeCohomologyComparison k j F n
    let compareG := zariskiRelativeCohomologyComparison k j G n
    mapZar ≫ compareG = compareF ≫ mapNis :=
  relativeCohomologyChangeOfTopology_coefficient.{u + 1} (C := SmoothSite B) J K (U := U) (X := X) j
    ((toSheaf k).map f) n

/-- Comparison commutes with restriction along a square of smooth-site morphisms. -/
theorem zariskiRelativeCohomologyComparison_restriction {U X : SmoothSite B} (j : U ⟶ X)
    {V Y : SmoothSite B}
    (j' : V ⟶ Y) (a : U ⟶ V) (b : X ⟶ Y) (h : j ≫ b = a ≫ j')
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    let FNis := (toSheaf k).obj F
    let FZar := (P).obj FNis
    let restrictZar := relativeRestriction.{u + 1, u + 1} J j j' a b h FZar n
    let restrictNis := relativeRestriction.{u + 1, u + 1} K j j' a b h FNis n
    let compareHere := zariskiRelativeCohomologyComparison k j F n
    let compareThere := zariskiRelativeCohomologyComparison k j' F n
    restrictZar ≫ compareHere = compareThere ≫ restrictNis :=
  relativeCohomologyChangeOfTopology_restriction.{u + 1} (C := SmoothSite B) J K
    (U := U) (X := X) j (V := V) (Y := Y) j' a b h ((toSheaf k).obj F) n

/-- Comparison commutes with the actual signed boundary of the localization sequence.
For an open immersion the scheme map is a monomorphism. -/
theorem zariskiRelativeCohomologyComparison_boundary {U X : SmoothSite B} (j : U ⟶ X) [Mono j]
    (F : SheafWithTransfers.{u + 1} k) (n : ℕ) :
    let FNis := (toSheaf k).obj F
    let FZar := (P).obj FNis
    let boundaryZar := relativeBoundary.{u + 1, u + 1} J j FZar n
    let boundaryNis := relativeBoundary.{u + 1, u + 1} K j FNis n
    let compareAt := zariskiRefinementCohomologyComparisonAt k F n U
    let compareRelative := zariskiRelativeCohomologyComparison k j F (n + 1)
    boundaryZar ≫ compareRelative = compareAt ≫ boundaryNis :=
  relativeCohomologyChangeOfTopology_boundary.{u + 1} (C := SmoothSite B) J K (U := U) (X := X) j
    ((toSheaf k).obj F) n

/-- Relative Ext is unchanged by refining the smooth Zariski topology to Nisnevich for
homotopy-invariant transfer coefficients over a perfect field. -/
@[colib_tag "COL-1308", colib_ref "MVW2006" "Proposition 13.9" "ingredient"
  "Positive higher direct image vanishing for the underlying homotopy-invariant coefficient"]
theorem isIso_zariskiRelativeCohomologyComparison {U X : SmoothSite B} (j : U ⟶ X)
    [PerfectField k]
    (F : SheafWithTransfers.{u + 1} k) (hF : F.obj.IsA1Invariant) (n : ℕ) :
    IsIso (C := AddCommGrpCat.{u + 1}) (zariskiRelativeCohomologyComparison k j F n) :=
  isIso_relativeCohomologyChangeOfTopology.{u + 1} (C := SmoothSite B) J K (U := U) (X := X) j
    ((toSheaf k).obj F) n (by
    intro p hp
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    refine isZero_rightDerived_changeOfTopology_of_isZero_sheafify_cohomology.{u + 1}
      J K ((toSheaf k).obj F) (m + 1) ?_
    let := SmoothSite.wEqualsLocallyBijective_addCommGrpCat J
    exact Presheaf.isZero_sheafify_of_locally_zero J
      (cohomologyPresheaf.{u + 1, u + 1} ((toSheaf k).obj F) (m + 1))
      (zeroSieve_mem_zariskiTopology_succ_of_perfect k F hF m))

end AlgebraicGeometry.SheafWithTransfers
