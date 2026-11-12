/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.ParameterFunctor
public import Colib.AlgebraicGeometry.SheavesWithTransfers.TorusSectionsFunctor
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Sheafification
import Colib.AlgebraicGeometry.PresheavesWithTransfers.LocalVanishing.Torus
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Image
import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness
import Colib.CategoryTheory.Sites.SheafifyLocallyZero

/-!
# Nisnevich sheafification of torus sections

The canonical comparison extends the original sheafification unit evaluated
on the torus product. For an A¹-invariant transfer presheaf, the kernel and
cokernel of that unit remain locally zero after the actual torus reindexing.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SheafWithTransfers

open _root_.AlgebraicGeometry.Scheme
open SmoothSite.Contraction PresheafWithTransfers

variable (k : Type u) [Field k]

local notation "A" => nisnevichSheafify k
local notation "B" => torusSectionsFunctor k
local notation "J" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))
local notation "Gₘ" => SmoothSite.multiplicativeGroupObject (Spec (CommRingCat.of k))
local notation "T" => withParameterFunctor Gₘ

/-- The canonical comparison evaluates the original sheafification unit on
the actual torus product. -/
def torusSectionsSheafificationComparison (P : PresheafWithTransfers.{u + 1} k) :
    (A).obj (torusSections P) ⟶ (B).obj ((A).obj P) :=
  nisnevichSheafifyLift k ((T).map (toNisnevichSheafify k P))

@[reassoc (attr := simp)]
theorem torusSectionsSheafificationComparison_unit (P : PresheafWithTransfers.{u + 1} k) :
    toNisnevichSheafify k (torusSections P) ≫
      (torusSectionsSheafificationComparison k P).hom =
        (T).map (toNisnevichSheafify k P) :=
  toNisnevichSheafify_lift k _

/-- The same comparison is natural for the actual coefficient maps. -/
@[reassoc]
theorem torusSectionsSheafificationComparison_naturality
    {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q) :
    (A).map ((T).map f) ≫ torusSectionsSheafificationComparison k Q =
      torusSectionsSheafificationComparison k P ≫ (B).map ((A).map f) := by
  apply nisnevichSheafify_hom_ext k
  change toNisnevichSheafify k (torusSections P) ≫
      (((A).map ((T).map f)).hom ≫ (torusSectionsSheafificationComparison k Q).hom) =
    toNisnevichSheafify k (torusSections P) ≫
      ((torusSectionsSheafificationComparison k P).hom ≫ (T).map (((A).map f).hom))
  rw [← Category.assoc, ← toNisnevichSheafify_naturality k, Category.assoc]
  change (T).map f ≫ toNisnevichSheafify k (torusSections Q) ≫
      (torusSectionsSheafificationComparison k Q).hom =
    toNisnevichSheafify k (torusSections P) ≫
      (torusSectionsSheafificationComparison k P).hom ≫ (T).map (((A).map f).hom)
  rw [torusSectionsSheafificationComparison_unit k Q,
    torusSectionsSheafificationComparison_unit_assoc k P,
    ← Functor.map_comp, ← Functor.map_comp, toNisnevichSheafify_naturality k f]

private theorem isA1Invariant_of_mono_app {P Q : PresheafWithTransfers.{u + 1} k} (f : P ⟶ Q)
    [∀ X : Cor k, Mono (f.hom.app (op X))] (hQ : Q.IsA1Invariant) :
    P.IsA1Invariant := by
  intro X
  let R := CommRingCat.of k
  let P₀ := (toPresheaf k).obj P
  let Q₀ := (toPresheaf k).obj Q
  let φ := (toPresheaf k).map f
  let p := A1.projectionPullback R P₀ X
  let s := A1.sectionPullback R P₀ X 0
  have hs : s ≫ p = 𝟙 _ := by
    let Y := affineLineCylinder.obj X
    let : Mono (φ.app (op Y)) := inferInstanceAs (Mono (f.hom.app (op (Cor.mk Y))))
    apply (cancel_mono (φ.app (op Y))).mp
    have hn := φ.naturality (nativeAffineSection R X 0).op
    have hm := φ.naturality ((projection (SmoothSite.additiveGroupObject (Spec R))).app X).op
    change s ≫ φ.app (op X) = φ.app (op Y) ≫ A1.sectionPullback R Q₀ X 0 at hn
    change p ≫ φ.app (op Y) = φ.app (op X) ≫ A1.projectionPullback R Q₀ X at hm
    rw [Category.assoc, hm, ← Category.assoc, hn, Category.assoc,
      A1.sectionPullback_projectionPullback R Q₀ hQ X 0, Category.comp_id, Category.id_comp]
  exact ⟨⟨s, A1.projectionPullback_sectionPullback R P₀ X 0, hs⟩⟩

private theorem isZero_sheafify_torusSections_of_isZero
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant)
    (h : IsZero ((A).obj P)) : IsZero ((A).obj (torusSections P)) := by
  let P₀ : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1} := (toPresheaf k).obj P
  let f : P₀ ⟶ (toPresheaf k).obj ((A).obj P).obj :=
    (toPresheaf k).map (toNisnevichSheafify k P)
  let : Presheaf.IsLocallyInjective J f := isLocallyInjective_toNisnevichSheafify k P
  have hLocal (X : SmoothSite (Spec (.of k))) (s : P.sections (Cor.mk X)) :
      Presheaf.equalizerSieve (F := P₀) s 0 ∈ J X := by
    let E := SheafWithTransfers.forget k ⋙ toPresheaf.{u + 1} k ⋙
      (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op X)
    let hsub : Subsingleton (((toPresheaf k).obj ((A).obj P).obj).obj (op X)) :=
      AddCommGrpCat.subsingleton_of_isZero (E.map_isZero h)
    exact Presheaf.equalizerSieve_mem J f (X := op X) s 0
      (@Subsingleton.elim _ hsub _ _)
  let Q₀ : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    (toPresheaf k).obj (torusSections P)
  have hz := Presheaf.isZero_sheafify_of_locally_zero J Q₀
    (fun X s => torus_zeroSieve_mem_of_locally_zero P hP hLocal X s)
  have hG := hz.of_iso ((nisnevichSheafificationUnderlyingIso k).app (torusSections P)).symm
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (toSheaf k).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact (IsZero.iff_id_eq_zero _).mp hG

set_option maxHeartbeats 600000 in
-- The signed sheafification and reindexing preserve both kernel and cokernel comparisons.
/-- The canonical comparison is invertible for A¹-invariant transfer presheaves. -/
theorem isIso_torusSectionsSheafificationComparison
    (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    IsIso (torusSectionsSheafificationComparison k P) := by
  let η := toNisnevichSheafify k P
  let adj := nisnevichSheafificationAdjunction k
  let ε := adj.counit.app ((A).obj P)
  let : IsIso ε := inferInstanceAs (IsIso (adj.counit.app ((A).obj P)))
  have hη : adj.unit.app P = η := nisnevichSheafificationAdjunction_unit_app k P
  have htri : (A).map η ≫ ε = 𝟙 _ := by
    rw [← hη]
    exact adj.left_triangle_components P
  let : IsIso ((A).map η ≫ ε) := htri.symm ▸ inferInstance
  let : IsIso ((A).map η) := IsIso.of_isIso_comp_right _ ε
  let E (X : Cor k) := PresheafWithTransfers.forget ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj (op X)
  let (X : Cor k) : Mono ((kernel.ι η).hom.app (op X)) :=
    inferInstanceAs (Mono ((E X).map (kernel.ι η)))
  let (X : Cor k) : Epi ((cokernel.π η).hom.app (op X)) :=
    inferInstanceAs (Epi ((E X).map (cokernel.π η)))
  have hK : (kernel η).IsA1Invariant := isA1Invariant_of_mono_app k (kernel.ι η) hP
  have hC : (cokernel η).IsA1Invariant :=
    isA1Invariant_of_epi_app (cokernel.π η) (nisnevichSheafify_isA1Invariant P hP)
  let : Mono ((A).map η) := IsIso.mono_of_iso ((A).map η)
  let : Epi ((A).map η) := IsIso.epi_of_iso ((A).map η)
  have hzK : IsZero ((A).obj (kernel η)) :=
    (isZero_kernel_of_mono ((A).map η)).of_iso (PreservesKernel.iso A η)
  have hzC : IsZero ((A).obj (cokernel η)) :=
    (isZero_cokernel_of_epi ((A).map η)).of_iso (PreservesCokernel.iso A η)
  let S := T ⋙ A
  have hk : IsZero (kernel (S.map η)) :=
    (isZero_sheafify_torusSections_of_isZero k _ hK hzK).of_iso (PreservesKernel.iso S η).symm
  have hc : IsZero (cokernel (S.map η)) :=
    (isZero_sheafify_torusSections_of_isZero k _ hC hzC).of_iso (PreservesCokernel.iso S η).symm
  let : Mono (S.map η) := Abelian.mono_of_kernel_ι_eq_zero _ (hk.eq_zero_of_src _)
  let : Epi (S.map η) := Abelian.epi_of_cokernel_π_eq_zero _ (hc.eq_zero_of_tgt _)
  let : IsIso (S.map η) := isIso_of_mono_of_epi _
  let Q := (B).obj ((A).obj P)
  have he : S.map η ≫ adj.counit.app Q = torusSectionsSheafificationComparison k P := by
    apply nisnevichSheafifyLift_unique k
    change toNisnevichSheafify k (torusSections P) ≫
      (((A).map ((T).map η)).hom ≫ (adj.counit.app Q).hom) = (T).map η
    rw [← Category.assoc, ← toNisnevichSheafify_naturality k, Category.assoc]
    have ht : toNisnevichSheafify k Q.obj ≫ (adj.counit.app Q).hom = 𝟙 Q.obj := by
      rw [← nisnevichSheafificationAdjunction_unit_app k Q.obj]
      exact adj.right_triangle_components Q
    let τ : (T).obj P ⟶ Q.obj := (T).map η
    change τ ≫ (toNisnevichSheafify k Q.obj ≫ (adj.counit.app Q).hom) = τ
    exact (congrArg (τ ≫ ·) ht).trans (Category.comp_id τ)
  rw [← he]
  exact IsIso.comp_isIso' (inferInstance : IsIso (S.map η))
    (inferInstance : IsIso (adj.counit.app Q))

/-- The torus sections of the actual Nisnevich sheafification are the
sheafification of the original torus sections. -/
def torusSectionsSheafificationIso (P : PresheafWithTransfers.{u + 1} k) (hP : P.IsA1Invariant) :
    (A).obj (torusSections P) ≅ (B).obj ((A).obj P) := by
  let := isIso_torusSectionsSheafificationComparison k P hP
  exact asIso (torusSectionsSheafificationComparison k P)

end AlgebraicGeometry.SheafWithTransfers
