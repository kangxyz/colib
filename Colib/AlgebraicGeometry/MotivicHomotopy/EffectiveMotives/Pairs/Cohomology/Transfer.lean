/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.OpenSequence
public import Colib.AlgebraicGeometry.SheavesWithTransfers.Cohomology.OrdinaryComparison
public import Colib.CategoryTheory.Sites.RelativeCohomology.BoundaryNaturality
import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
import Mathlib.Algebra.FiveLemma

/-!
# Transfer Ext for an ordinary open pair

The ordinary section-source maps give a map from the free abelian sheaf
presentation of an open pair to its underlying transfer presentation.
The induced relative Ext comparison is an isomorphism, with the original
restriction, coefficient, and connecting maps.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry.Scheme Stacks.Cohomology.FreeYonedaUnivLE

universe u w

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

section ExtComparison

universe v

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasExt.{w} C] [HasExt.{v} D]

private theorem extComparison_precomp (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] {A B : C} {A' B' : D}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A' ⟶ G.obj A) (b : B' ⟶ G.obj B)
    (h : g ≫ b = a ≫ G.map f) {F : C} (n : ℕ) (x : Ext.{w} B F n) :
    (Ext.mk₀.{v} g).comp ((Ext.mk₀ b).comp (x.mapExactFunctor G) (zero_add n)) (zero_add n) =
      (Ext.mk₀.{v} a).comp
        (((Ext.mk₀ f).comp x (zero_add n)).mapExactFunctor G) (zero_add n) := by
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, ← Ext.comp_assoc_of_second_deg_zero,
    ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, h]

private theorem extComparison_connecting (G : C ⥤ D) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {S : ShortComplex C} {T : ShortComplex D} (hS : S.ShortExact) (hT : T.ShortExact)
    (f : T ⟶ S.map G) {F : C} (n : ℕ) (x : Ext.{w} S.X₁ F n) :
    hT.extClass.comp ((Ext.mk₀.{v} f.τ₁).comp (x.mapExactFunctor G) (zero_add n))
        (Nat.add_comm 1 n) =
      (Ext.mk₀.{v} f.τ₃).comp ((hS.extClass.comp x (Nat.add_comm 1 n)).mapExactFunctor G)
        (zero_add (n + 1)) := by
  have h := ShortComplex.ShortExact.extClass_naturality.{v} hT (hS.map_of_exact G) f
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass,
    ← Ext.comp_assoc _ _ _ (add_zero 1) (zero_add n) (by omega), h,
    Ext.comp_assoc _ _ _ (zero_add 1) (Nat.add_comm 1 n) (by omega)]

private theorem extComparison_bijective {S : ShortComplex C} {T : ShortComplex D}
    (hS : S.ShortExact) (hT : T.ShortExact) (F : C) (G : D)
    (c₁ : ∀ n, Ext.{w} S.X₁ F n →+ Ext.{v} T.X₁ G n)
    (c₂ : ∀ n, Ext.{w} S.X₂ F n →+ Ext.{v} T.X₂ G n)
    (c₃ : ∀ n, Ext.{w} S.X₃ F n →+ Ext.{v} T.X₃ G n)
    (h₀ : ∀ n, ((Ext.mk₀.{v} T.g).precomp G (zero_add n)).comp (c₃ n) =
      (c₂ n).comp ((Ext.mk₀.{w} S.g).precomp F (zero_add n)))
    (h₁ : ∀ n, ((Ext.mk₀.{v} T.f).precomp G (zero_add n)).comp (c₂ n) =
      (c₁ n).comp ((Ext.mk₀.{w} S.f).precomp F (zero_add n)))
    (h₂ : ∀ n, (hT.extClass.precomp G (Nat.add_comm 1 n)).comp (c₁ n) =
      (c₃ (n + 1)).comp (hS.extClass.precomp F (Nat.add_comm 1 n)))
    (b₁ : ∀ n, Function.Bijective (c₁ n)) (b₂ : ∀ n, Function.Bijective (c₂ n)) (n : ℕ) :
    Function.Bijective (c₃ n) := by
  let s₀ (n : ℕ) := (Ext.mk₀.{w} S.g).precomp F (zero_add n)
  let s₁ (n : ℕ) := (Ext.mk₀.{w} S.f).precomp F (zero_add n)
  let s₂ (n : ℕ) : Ext.{w} S.X₁ F n →+ Ext.{w} S.X₃ F (n + 1) :=
    hS.extClass.precomp F (Nat.add_comm 1 n)
  let t₀ (n : ℕ) := (Ext.mk₀.{v} T.g).precomp G (zero_add n)
  let t₁ (n : ℕ) := (Ext.mk₀.{v} T.f).precomp G (zero_add n)
  let t₂ (n : ℕ) : Ext.{v} T.X₁ G n →+ Ext.{v} T.X₃ G (n + 1) :=
    hT.extClass.precomp G (Nat.add_comm 1 n)
  have hs n : Function.Exact (s₀ n) (s₁ n) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp (Ext.contravariant_sequence_exact₂' hS F n)
  have ht n : Function.Exact (t₀ n) (t₁ n) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp (Ext.contravariant_sequence_exact₂' hT G n)
  cases n with
  | zero =>
    let : Epi S.g := hS.epi_g
    let : Epi T.g := hT.epi_g
    exact AddMonoidHom.bijective_of_bijective_of_injective_of_left_exact
      (s₀ 0) (s₁ 0) (t₀ 0) (t₁ 0) (c₃ 0) (c₂ 0) (c₁ 0) (h₀ 0) (h₁ 0) (hs 0) (ht 0)
      (b₂ 0) (b₁ 0).injective (Ext.precomp_mk₀_injective_of_epi F S.g)
      (Ext.precomp_mk₀_injective_of_epi G T.g)
  | succ n =>
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective
      (s₁ n) (s₂ n) (s₀ (n + 1)) (s₁ (n + 1)) (t₁ n) (t₂ n) (t₀ (n + 1)) (t₁ (n + 1))
      (c₂ n) (c₁ n) (c₃ (n + 1)) (c₂ (n + 1)) (c₁ (n + 1))
      (h₁ n) (h₂ n) (h₀ (n + 1)) (h₁ (n + 1))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.contravariant_sequence_exact₁' hS F n (n + 1) (Nat.add_comm 1 n)))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.contravariant_sequence_exact₃' hS F n (n + 1) (Nat.add_comm 1 n)))
      (hs (n + 1))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.contravariant_sequence_exact₁' hT G n (n + 1) (Nat.add_comm 1 n)))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.contravariant_sequence_exact₃' hT G n (n + 1) (Nat.add_comm 1 n)))
      (ht (n + 1)) (b₂ n).surjective (b₁ n) (b₂ (n + 1)) (b₁ (n + 1)).injective

end ExtComparison

variable (k : Type u) [Field k]

local notation "J" => SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))
set_option hygiene false in
set_option quotPrecheck false in
local notation "NST" => SheafWithTransfers.{u + 1} k
set_option hygiene false in
set_option quotPrecheck false in
local notation "Ord" => Sheaf J AddCommGrpCat.{u + 1}
set_option hygiene false in
set_option quotPrecheck false in
local notation "T" => toSheaf.{u + 1} k
local notation "R" => smoothTransferRepresentable k
local notation "Q" => transferPairCokernelFunctor k
set_option hygiene false in
set_option quotPrecheck false in
local notation "O" => relativeSourceFunctor.{u + 1} J
local notation "p" => transferPairProjection k

/-- Fix the standard additive sheafification on the ordinary smooth Nisnevich site. -/
local instance ordinaryPairHasSheafify : HasSheafify J AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u + 1} J

variable {U X : SmoothSite (Spec (.of k))} (j : U ⟶ X)

set_option Elab.async false in
private theorem ordinaryToTransferPairSource_condition :
    (freeYoneda.{u + 1} J).map j ≫
      ordinaryToTransferSource k X ≫ (T).map ((p).app (Arrow.mk j)) = 0 := by
  let r := (R).map j
  let q := (p).app (Arrow.mk j)
  have h : (freeYoneda.{u + 1} J).map j ≫ ordinaryToTransferSource k X =
      ordinaryToTransferSource k U ≫ (T).map r := ordinaryToTransferSource_naturality k j
  have hz : r ≫ q = 0 := (transferPairSequence k (Arrow.mk j)).zero
  change _ ≫ ordinaryToTransferSource k X ≫ (T).map q = 0
  rw [← Category.assoc, h, Category.assoc, ← (T).map_comp, hz, (T).map_zero, comp_zero]

/-- The map between the actual ordinary and transfer cokernel sources. -/
@[no_expose]
def ordinaryToTransferPairSource :
    relativeSource.{u + 1} J j ⟶ (T).obj (transferPairCokernel k j) :=
  cokernel.desc ((freeYoneda.{u + 1} J).map j)
    (ordinaryToTransferSource k X ≫ (T).map ((p).app (Arrow.mk j)))
    (ordinaryToTransferPairSource_condition k j)

/-- The relative source comparison descends the specified ambient section-source map. -/
@[reassoc]
theorem ordinaryToTransferPairSource_π :
    relativeSourceπ.{u + 1} J j ≫ ordinaryToTransferPairSource k j =
      ordinaryToTransferSource k X ≫ (T).map ((p).app (Arrow.mk j)) :=
  cokernel.π_desc _ _ _

set_option maxHeartbeats 500000 in
-- Resolve the two literal free-Yoneda cokernel projections at their common source.
/-- The relative source comparison commutes with the original maps of pairs. -/
@[reassoc]
theorem ordinaryToTransferPairSource_naturality {V Y : SmoothSite (Spec (.of k))} {j' : V ⟶ Y}
    (a : Arrow.mk j ⟶ Arrow.mk j') :
    (O).map a ≫ ordinaryToTransferPairSource k j' =
      ordinaryToTransferPairSource k j ≫ (T).map ((Q).map a) := by
  apply (cancel_epi (relativeSourceπ.{u + 1} J j)).mp
  have h : relativeSourceπ.{u + 1} J j ≫ (O).map a =
      (freeYoneda.{u + 1} J).map a.right ≫ relativeSourceπ.{u + 1} J j' :=
    relativeSourceFunctor_π_naturality.{u + 1} J a
  let F := freeYoneda.{u + 1} J
  have ha : F.map a.right ≫ ordinaryToTransferSource k Y =
      ordinaryToTransferSource k X ≫ (T).map ((R).map a.right) :=
    ordinaryToTransferSource_naturality k a.right
  have hp : (R).map a.right ≫ (p).app (Arrow.mk j') =
      (p).app (Arrow.mk j) ≫ (Q).map a := (p).naturality a
  calc
    _ = (F.map a.right ≫ relativeSourceπ.{u + 1} J j') ≫ ordinaryToTransferPairSource k j' :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ ordinaryToTransferPairSource k j') h)
    _ = (F.map a.right ≫ ordinaryToTransferSource k Y) ≫ (T).map ((p).app (Arrow.mk j')) :=
      (Category.assoc _ _ _).trans
        ((congrArg (F.map a.right ≫ ·) (ordinaryToTransferPairSource_π k j')).trans
          (Category.assoc _ _ _).symm)
    _ = ordinaryToTransferSource k X ≫ (T).map
        ((R).map a.right ≫ (p).app (Arrow.mk j')) := by
      rw [ha, Category.assoc, (T).map_comp]
    _ = ordinaryToTransferSource k X ≫ (T).map
        ((p).app (Arrow.mk j) ≫ (Q).map a) := by rw [hp]
    _ = _ := by
      rw [(T).map_comp, ← ordinaryToTransferPairSource_π_assoc k j]

private def ordinaryToTransferPairPresentation :
    (relativePresentation.{u + 1} J j : ShortComplex Ord) ⟶
      (transferPairSequence k (Arrow.mk j)).map T where
  τ₁ := ordinaryToTransferSource k U
  τ₂ := ordinaryToTransferSource k X
  τ₃ := ordinaryToTransferPairSource k j
  comm₁₂ := (ordinaryToTransferSource_naturality k j).symm
  comm₂₃ := (ordinaryToTransferPairSource_π k j).symm

variable [HasExt.{w} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Forget transfers, then pull back along the original comparison of the two pair sources. -/
def transferPairExtComparison (F : NST) (n : ℕ) :
    Ext.{w} (transferPairCokernel k j) F n →+ relativeH.{u + 1, u + 1} J j ((T).obj F) n :=
  ((Ext.mk₀ (ordinaryToTransferPairSource k j)).precomp ((T).obj F) (zero_add n)).comp
    ((T).mapExtAddHom _ F n)

set_option maxHeartbeats 500000 in
-- Identify the transfer ambient projection with the degree-zero source of ordinary cohomology.
/-- Forgetting the support condition uses the actual ambient quotient. -/
theorem transferPairExtComparison_forget (F : NST) (n : ℕ)
    (x : Ext.{w} (transferPairCokernel k j) F n) :
    relativeForget.{u + 1, u + 1} J j ((T).obj F) n (transferPairExtComparison k j F n x) =
      transferExtComparison.{w, u + 1, u} k X F n
        ((Ext.mk₀ ((p).app (Arrow.mk j))).comp x (zero_add n)) := by
  exact extComparison_precomp (T) ((p).app (Arrow.mk j)) (relativeSourceπ.{u + 1} J j)
    (ordinaryToTransferSource k X) (ordinaryToTransferPairSource k j)
    (ordinaryToTransferPairSource_π k j) n x

private theorem transferPairExtComparison_apply (F : NST) (n : ℕ)
    (x : Ext.{w} (transferPairCokernel k j) F n) :
    transferPairExtComparison k j F n x =
      (Ext.mk₀.{u + 1} (ordinaryToTransferPairSource k j)).comp
        (x.mapExactFunctor T) (zero_add n) := rfl

set_option maxHeartbeats 1200000 in
-- Identify Ext classes across the two literal pair cokernels and their exact-functor comparison.
/-- Relative comparison commutes with restriction along an original arrow of pairs. -/
theorem transferPairExtComparison_precomp {V Y : SmoothSite (Spec (.of k))} {j' : V ⟶ Y}
    (a : Arrow.mk j ⟶ Arrow.mk j') (F : NST) (n : ℕ)
    (x : Ext.{w} (transferPairCokernel k j') F n) :
    ((relativeCohomologyFunctor.{u + 1, u + 1} J n).obj ((T).obj F)).map a.op
      (transferPairExtComparison k j' F n x) =
    transferPairExtComparison k j F n ((Ext.mk₀ ((Q).map a)).comp x (zero_add n)) := by
  let AOrd := relativeSource.{u + 1} J j
  let BOrd := relativeSource.{u + 1} J j'
  let y : Ext.{w} (transferPairCokernel k j) F n :=
    (Ext.mk₀ ((Q).map a)).comp x (zero_add n)
  let rOrd : Ext.{u + 1} AOrd BOrd 0 := Ext.mk₀ ((O).map a)
  let z : Ext.{u + 1} BOrd ((T).obj F) n := transferPairExtComparison k j' F n x
  have hOrd := relativeCohomologyFunctor_obj_map_apply.{u + 1, u + 1} J ((T).obj F) n a z
  have hSource := transferPairExtComparison_apply k j' F n x
  have hMap := congrArg (fun q : Ext.{u + 1} BOrd ((T).obj F) n =>
    rOrd.comp q (zero_add n)) hSource
  have hStart := hOrd.trans hMap
  have hTarget := transferPairExtComparison_apply k j F n y
  have h := ordinaryToTransferPairSource_naturality k j (j' := j') a
  have hExt := extComparison_precomp.{w, u + 1} (T) ((Q).map a) ((O).map a)
    (ordinaryToTransferPairSource k j) (ordinaryToTransferPairSource k j') h n x
  have hFinal := hStart.trans (hExt.trans hTarget.symm)
  exact hFinal

/-- Relative comparison commutes with the original coefficient action. -/
theorem transferPairExtComparison_postcomp {F G : NST} (a : F ⟶ G) (n : ℕ)
    (x : Ext.{w} (transferPairCokernel k j) F n) :
    relativeCoefficientMap.{u + 1, u + 1} J j ((T).map a) n (transferPairExtComparison k j F n x) =
      transferPairExtComparison k j G n (x.comp (Ext.mk₀ a) (add_zero n)) := by
  change ((Ext.mk₀ (ordinaryToTransferPairSource k j)).comp (x.mapExactFunctor T)
      (zero_add n)).comp (Ext.mk₀ ((T).map a)) (add_zero n) =
    (Ext.mk₀ (ordinaryToTransferPairSource k j)).comp
      ((x.comp (Ext.mk₀ a) (add_zero n)).mapExactFunctor T) (zero_add n)
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

variable [IsOpenImmersion j.left]

/-- The underlying smooth-site arrow of an open immersion is mono. -/
local instance openPairMono : Mono j :=
  (SmoothSite.forgetScheme _).mono_of_mono_map (IsOpenImmersion.mono j.left)

local notation "hₜ" => transferPairSequence_shortExact k j
set_option hygiene false in
set_option quotPrecheck false in
local notation "hₒ" => relativePresentation_shortExact.{u + 1} J j

set_option maxHeartbeats 500000 in
-- Identify the projections of both actual presentations with the extension-class source maps.
/-- Relative comparison intertwines the actual extension classes. -/
theorem transferPairExtComparison_connecting (F : NST) (n : ℕ)
    (x : Ext.{w} ((R).obj U) F n) :
    relativeConnecting.{u + 1, u + 1} J j ((T).obj F) n
      (transferExtComparison.{w, u + 1, u} k U F n x) =
      transferPairExtComparison k j F (n + 1) ((hₜ).extClass.comp x (Nat.add_comm 1 n)) := by
  exact extComparison_connecting (T) hₜ hₒ (ordinaryToTransferPairPresentation k j) n x

set_option maxHeartbeats 500000 in
-- Instantiate the abstract five lemma on the actual free and transfer presentations.
/-- The genuine comparison is bijective by the Ext rows of the two presentations. -/
theorem transferPairExtComparison_bijective (F : NST) (n : ℕ) :
    Function.Bijective (transferPairExtComparison k j F n :
      Ext.{w} (transferPairCokernel k j) F n →+ _) := by
  apply extComparison_bijective hₜ hₒ F ((T).obj F)
    (transferExtComparison.{w, u + 1, u} k U F)
    (transferExtComparison.{w, u + 1, u} k X F)
    (transferPairExtComparison k j F) _ _ _ _ _ n
  · intro d
    exact AddMonoidHom.ext (transferPairExtComparison_forget k j F d)
  · intro d
    exact AddMonoidHom.ext
      (fun x => (transferExtEquiv_naturality_graph.{w, u + 1, u} k j F d x).symm)
  · intro d
    exact AddMonoidHom.ext (transferPairExtComparison_connecting k j F d)
  · intro d
    exact (transferExtEquiv.{w, u + 1, u} k U F d).bijective
  · intro d
    exact (transferExtEquiv.{w, u + 1, u} k X F d).bijective

/-- Ordinary relative Ext identifies with Ext from the actual transfer cokernel. -/
def transferPairExtEquiv (F : NST) (n : ℕ) :
    Ext.{w} (transferPairCokernel k j) F n ≃+ relativeH.{u + 1, u + 1} J j ((T).obj F) n :=
  AddEquiv.ofBijective _ (transferPairExtComparison_bijective k j F n)

end AlgebraicGeometry.MotivicHomotopy
