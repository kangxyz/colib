/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.PresheavesWithTransfers.A1Invariant.ObjectProperty
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.PerfectField
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Exactness
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.HomotopyInvariance
import Colib.AlgebraicGeometry.PresheavesWithTransfers.Sheafification.Image
import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.StrictA1.DegreeZero
import Colib.AlgebraicGeometry.SheavesWithTransfers.EnoughInjectives
import Colib.AlgebraicGeometry.SheavesWithTransfers.UnderlyingExactness
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four

/-!
# The weak Serre property of A¹-invariant transfer sheaves

The ordinary transfer-presheaf kernel and cokernel retain A¹-invariance.
Exact Nisnevich sheafification gives the sheaf cokernel. For extensions
the literal affine projection gives a map of the original Ext sequences,
with the connecting map given by composition with the extension class.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme SmoothSite.Contraction
open Stacks.Cohomology.FreeYonedaUnivLE
open scoped ZeroObject

universe u v

namespace AlgebraicGeometry.SheafWithTransfers

open PresheafWithTransfers

variable (k : Type u) [Field k]

/-- The original A¹-invariance condition on Nisnevich transfer sheaves. -/
abbrev a1InvariantSheafProperty : ObjectProperty (SheafWithTransfers.{u + 1} k) :=
  (a1InvariantProperty k).inverseImage (SheafWithTransfers.forget k)

private theorem a1Invariant_kernel {F G : SheafWithTransfers.{u + 1} k}
    (f : F ⟶ G) (hF : F.obj.IsA1Invariant) : (kernel f).obj.IsA1Invariant := by
  intro X
  let R := CommRingCat.of k
  let V : SheafWithTransfers.{u + 1} k ⥤
      (SmoothSite (Spec R))ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    SheafWithTransfers.forget k ⋙ toPresheaf k
  let P := V.obj (kernel f)
  let Q := V.obj F
  let i := V.map (kernel.ι f)
  let Y := affineLineCylinder.obj X
  let p := A1.projectionPullback R P X
  let s := A1.sectionPullback R P X 0
  let : Mono (i.app (op Y)) :=
    Functor.map_mono (V ⋙ (CategoryTheory.evaluation _ _).obj (op Y)) (kernel.ι f)
  have hs : s ≫ p = 𝟙 _ := by
    apply (cancel_mono (i.app (op Y))).mp
    have hn := i.naturality (nativeAffineSection R X 0).op
    have hm := i.naturality ((projection (SmoothSite.additiveGroupObject (Spec R))).app X).op
    change s ≫ i.app (op X) = i.app (op Y) ≫ A1.sectionPullback R Q X 0 at hn
    change p ≫ i.app (op Y) = i.app (op X) ≫ A1.projectionPullback R Q X at hm
    rw [Category.assoc, hm, ← Category.assoc, hn, Category.assoc,
      A1.sectionPullback_projectionPullback R Q hF X 0, Category.comp_id, Category.id_comp]
  exact ⟨⟨s, A1.projectionPullback_sectionPullback R P X 0, hs⟩⟩

private theorem a1Invariant_cokernel {F G : SheafWithTransfers.{u + 1} k}
    (f : F ⟶ G) (hG : G.obj.IsA1Invariant) : (cokernel f).obj.IsA1Invariant := by
  let A := nisnevichSheafify k
  let U := SheafWithTransfers.forget.{u + 1} k
  let V : PresheafWithTransfers.{u + 1} k ⥤ (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
    PresheafWithTransfers.forget
  let g := U.map f
  let p := cokernel.π g
  have hp : Epi (V.map p) := Functor.map_epi V p
  let (X : Cor k) : Epi (p.hom.app (op X)) :=
    (NatTrans.epi_iff_epi_app _).1 hp (op X)
  have hP : (cokernel g).IsA1Invariant := isA1Invariant_of_epi_app p hG
  let ε := asIso (nisnevichSheafificationAdjunction k).counit
  let e : A.obj (cokernel g) ≅ cokernel f :=
    PreservesCokernel.iso A g ≪≫ cokernel.mapIso (A.map g) f (ε.app F) (ε.app G)
      (ε.hom.naturality f)
  exact (nisnevichSheafify_isA1Invariant _ hP).of_iso (U.mapIso e)

section ExtSequence

variable {A : Type*} [Category* A] [Abelian A] [HasExt.{v} A]
  {E : ShortComplex A} (hE : E.ShortExact)

private abbrev extPrecomp {U V F : A} (f : V ⟶ U) (n : ℕ) :
    AddCommGrpCat.of (Abelian.Ext.{v} U F n) ⟶ AddCommGrpCat.of (Abelian.Ext.{v} V F n) :=
  AddCommGrpCat.ofHom ((Abelian.Ext.mk₀ f).precomp F (zero_add n))

private abbrev extPostcomp {U F G : A} {a b c : ℕ} (x : Abelian.Ext.{v} F G b)
    (h : a + b = c) :
    AddCommGrpCat.of (Abelian.Ext.{v} U F a) ⟶ AddCommGrpCat.of (Abelian.Ext.{v} U G c) :=
  AddCommGrpCat.ofHom (x.postcomp U h)

private theorem extPrecomp_postcomp {U V F G : A} (f : V ⟶ U) {a b c : ℕ}
    (x : Abelian.Ext.{v} F G b) (h : a + b = c) :
    extPostcomp (U := U) x h ≫ extPrecomp f c =
      extPrecomp f a ≫ extPostcomp (U := V) x h := by
  ext y
  exact (Abelian.Ext.comp_assoc (Abelian.Ext.mk₀ f) y x (zero_add a) h (by omega)).symm

include hE in
private theorem isIso_extPrecomp_zero_X₂ {U V : A} (f : V ⟶ U)
    (h₁ : IsIso (extPrecomp (F := E.X₁) f 0))
    (h₃ : IsIso (extPrecomp (F := E.X₃) f 0))
    (h₄ : IsIso (extPrecomp (F := E.X₁) f 1)) :
    IsIso (extPrecomp (F := E.X₂) f 0) := by
  let L := ComposableArrows.mk₄ (0 : (0 : AddCommGrpCat.{v}) ⟶ _)
    (extPostcomp (U := U) (Abelian.Ext.mk₀ E.f) (add_zero 0))
    (extPostcomp (U := U) (Abelian.Ext.mk₀ E.g) (add_zero 0))
    (extPostcomp (U := U) hE.extClass (zero_add 1))
  let R := ComposableArrows.mk₄ (0 : (0 : AddCommGrpCat.{v}) ⟶ _)
    (extPostcomp (U := V) (Abelian.Ext.mk₀ E.f) (add_zero 0))
    (extPostcomp (U := V) (Abelian.Ext.mk₀ E.g) (add_zero 0))
    (extPostcomp (U := V) hE.extClass (zero_add 1))
  let φ : L ⟶ R := ComposableArrows.homMk₄ (𝟙 _)
    (extPrecomp f 0) (extPrecomp f 0) (extPrecomp f 0) (extPrecomp f 1)
    (by change (0 : (0 : AddCommGrpCat.{v}) ⟶ _) ≫ _ = 𝟙 _ ≫ 0; rw [zero_comp, comp_zero])
    (extPrecomp_postcomp f (Abelian.Ext.mk₀ E.f) (add_zero 0))
    (extPrecomp_postcomp f (Abelian.Ext.mk₀ E.g) (add_zero 0))
    (extPrecomp_postcomp f hE.extClass (zero_add 1))
  have exactSeq (W : A) :
      (ComposableArrows.mk₄ (0 : (0 : AddCommGrpCat.{v}) ⟶ _)
        (extPostcomp (U := W) (Abelian.Ext.mk₀ E.f) (add_zero 0))
        (extPostcomp (U := W) (Abelian.Ext.mk₀ E.g) (add_zero 0))
        (extPostcomp (U := W) hE.extClass (zero_add 1))).Exact := by
    let q := extPostcomp (U := W) (Abelian.Ext.mk₀ E.f) (add_zero 0)
    let : Mono E.f := hE.mono_f
    let : Mono q := Abelian.Ext.mono_postcomp_mk₀_of_mono W E.f
    have h₀ : (ShortComplex.mk (0 : (0 : AddCommGrpCat.{v}) ⟶ _) q zero_comp).Exact :=
      (ShortComplex.exact_iff_mono _ rfl).2 inferInstance
    have h₁ := Abelian.Ext.covariant_sequence_exact₂' W hE 0
    have h₂ := Abelian.Ext.covariant_sequence_exact₃' W hE 0 1 (zero_add 1)
    exact ComposableArrows.exact_of_δ₀ h₀.exact_toComposableArrows
      (ComposableArrows.exact_of_δ₀ h₁.exact_toComposableArrows h₂.exact_toComposableArrows)
  exact Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono (exactSeq U) (exactSeq V) φ
    (by change Epi (𝟙 (0 : AddCommGrpCat.{v})); infer_instance) h₁ h₃
    (by
      change Mono (extPrecomp (F := E.X₁) f 1)
      let := h₄
      infer_instance)

end ExtSequence

variable [PerfectField k]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

private theorem a1Invariant_extension {E : ShortComplex (SheafWithTransfers.{u + 1} k)}
    (hE : E.ShortExact) (h₁ : E.X₁.obj.IsA1Invariant) (h₃ : E.X₃.obj.IsA1Invariant) :
    E.X₂.obj.IsA1Invariant := by
  apply (degreeZero_isInvariant_iff E.X₂).mp
  intro X
  let J := SmoothSite.nisnevichTopology (Spec (.of k))
  let e := E.map (toSheaf k)
  let he : e.ShortExact := hE.map_of_exact (toSheaf k)
  let p := (projection (SmoothSite.additiveGroupObject (Spec (.of k)))).app X
  let f := (freeYoneda.{u + 1} J).map p
  exact isIso_extPrecomp_zero_X₂ he f
    (degreeZero_isInvariant E.X₁ h₁ X)
    (degreeZero_isInvariant E.X₃ h₃ X)
    (isStrictA1Invariant_of_perfect E.X₁ h₁ 1 X)

/-- Over a perfect field the A¹-invariant transfer sheaves form a weak
Serre subcategory of the actual abelian category of transfer sheaves. -/
theorem a1InvariantSheafProperty_isWeakSerreClass :
    (a1InvariantSheafProperty k).IsWeakSerreClass where
  exists_zero := (a1InvariantSheafProperty k).exists_prop_of_containsZero
  of_iso e h := h.of_iso ((SheafWithTransfers.forget k).mapIso e)
  kernels_le := by
    rintro _ ⟨f, c, hc, hF, _⟩
    exact (a1Invariant_kernel k f hF).of_iso
      ((SheafWithTransfers.forget k).mapIso ((kernelIsKernel f).conePointUniqueUpToIso hc))
  cokernels_le := by
    rintro _ ⟨f, c, hc, _, hG⟩
    exact (a1Invariant_cokernel k f hG).of_iso
      ((SheafWithTransfers.forget k).mapIso ((cokernelIsCokernel f).coconePointUniqueUpToIso hc))
  prop_X₂_of_shortExact hE h₁ h₃ := a1Invariant_extension k hE h₁ h₃

end AlgebraicGeometry.SheafWithTransfers
