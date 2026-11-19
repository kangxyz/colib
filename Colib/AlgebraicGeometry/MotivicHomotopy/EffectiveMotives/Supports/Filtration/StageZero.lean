/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Comparison
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Supports.Filtration.Restriction

/-! # The natural stage-zero comparison for the coniveau tower -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme Opposite Order TopologicalSpace

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local instance] specializationOrder

private theorem projectedComparison_naturality {S N D : Type*}
    [Category* S] [Category* N] [Category* D]
    (R : S ⥤ N) (E : N ⥤ D) (M : S ⥤ D) (Q : Arrow S ⥤ N)
    (π : Arrow.rightFunc ⋙ R ⟶ Q) (β : R ⋙ E ≅ M)
    {X Y U V : S} {i : U ⟶ X} {j : V ⟶ Y}
    (f : Y ⟶ X) (α : Arrow.mk j ⟶ Arrow.mk i) (hα : α.right = f)
    (cX : M.obj X ⟶ E.obj (Q.obj (Arrow.mk i)))
    (cY : M.obj Y ⟶ E.obj (Q.obj (Arrow.mk j)))
    (hX : cX = (β.app X).inv ≫ E.map (π.app (Arrow.mk i)))
    (hY : cY = (β.app Y).inv ≫ E.map (π.app (Arrow.mk j))) :
    M.map f ≫ cX = cY ≫ (Q ⋙ E).map α := by
  let βX := (β.app X).inv
  let βY := (β.app Y).inv
  let πX := E.map (π.app (Arrow.mk i))
  let πY := E.map (π.app (Arrow.mk j))
  let g := Q.map α
  have h₁ : M.map f ≫ βX = βY ≫ E.map (R.map f) := β.inv.naturality f
  have h₂ : R.map f ≫ π.app (Arrow.mk i) = π.app (Arrow.mk j) ≫ g := by
    have h := π.naturality α
    change R.map α.right ≫ π.app (Arrow.mk i) = π.app (Arrow.mk j) ≫ g at h
    rwa [hα] at h
  have h₃ : E.map (R.map f) ≫ πX = πY ≫ E.map g :=
    (E.map_comp (R.map f) (π.app (Arrow.mk i))).symm.trans
      ((E.congr_map h₂).trans (E.map_comp (π.app (Arrow.mk j)) g))
  calc
    M.map f ≫ cX = M.map f ≫ βX ≫ πX := congrArg (M.map f ≫ ·) hX
    _ = (M.map f ≫ βX) ≫ πX := (Category.assoc _ _ _).symm
    _ = (βY ≫ E.map (R.map f)) ≫ πX := congrArg (· ≫ πX) h₁
    _ = βY ≫ E.map (R.map f) ≫ πX := Category.assoc _ _ _
    _ = βY ≫ πY ≫ E.map g := congrArg (βY ≫ ·) h₃
    _ = (βY ≫ πY) ≫ E.map g := (Category.assoc _ _ _).symm
    _ = cY ≫ (Q ⋙ E).map α := congrArg (· ≫ E.map g) hY.symm

private theorem map_op_comparison_naturality {C A : Type*} [Category* C] [Category* A]
    (H : Cᵒᵖ ⥤ A) {U V W Z : C} (f : U ⟶ V) (eX : V ⟶ Z)
    (eY : U ⟶ W) (r : W ⟶ Z) (h : f ≫ eX = eY ≫ r) :
    H.map eX.op ≫ H.map f.op = H.map r.op ≫ H.map eY.op :=
  (H.map_comp eX.op f.op).symm.trans
    ((H.congr_map (congrArg Quiver.Hom.op h)).trans (H.map_comp r.op eY.op))

private theorem comparison_naturality_of_generator {C : Type*} [Category* C]
    {X₀ X₁ X₂ Y₀ Y₁ Y₂ : C}
    (iX : X₀ ⟶ X₁) (iY : Y₀ ⟶ Y₁) [Epi iX]
    (cX : X₁ ⟶ X₂) (cY : Y₁ ⟶ Y₂) (pX : X₀ ⟶ X₂) (pY : Y₀ ⟶ Y₂)
    (r : X₁ ⟶ Y₁) (r₀ : X₀ ⟶ Y₀) (f : X₂ ⟶ Y₂)
    (hX : iX ≫ cX = pX) (hY : iY ≫ cY = pY)
    (hr : iX ≫ r = r₀ ≫ iY) (h : pX ≫ f = r₀ ≫ pY) : cX ≫ f = r ≫ cY := by
  apply (cancel_epi iX).mp
  calc
    iX ≫ cX ≫ f = (iX ≫ cX) ≫ f := (Category.assoc _ _ _).symm
    _ = pX ≫ f := congrArg (· ≫ f) hX
    _ = r₀ ≫ pY := h
    _ = r₀ ≫ iY ≫ cY := congrArg (r₀ ≫ ·) hY.symm
    _ = (r₀ ≫ iY) ≫ cY := (Category.assoc _ _ _).symm
    _ = (iX ≫ r) ≫ cY := congrArg (· ≫ cY) hr.symm
    _ = iX ≫ r ≫ cY := Category.assoc _ _ _

private theorem dependent_arg_heq {I : Type*} {A : I → Type*}
    (f : (i : I) → A i) {i j : I} (h : i = j) : HEq (f i) (f j) := by
  cases h
  rfl

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "DM(" field ")" => EffectiveMotivesMinus field

variable (X : Sm(k))

/-- The terminal index of the zero codimension support diagram. -/
def coniveauFullSupport : ConiveauSupports k X 0 :=
  ⟨⊤, fun _ _ ↦ zero_le⟩

private def fullSupportIsTerminal : IsTerminal (coniveauFullSupport k X) :=
  IsTerminal.ofUniqueHom
    (fun _ ↦ homOfLE (show _ ≤ (⊤ : Closeds X.left) from le_top))
    (fun _ _ ↦ Subsingleton.elim _ _)

section FullSupportGeometry

variable {X} {Y : Sm(k)}

private def fullSupportPairMap (f : Y ⟶ X) :
    Arrow.mk (supportOpenInclusion k Y (⊤ : Closeds Y.left)) ⟶
      Arrow.mk (supportOpenInclusion k X (⊤ : Closeds X.left)) :=
  supportOpenPairPreimageMap k f (⊤ : Closeds X.left)

private theorem fullSupportPairMap_right (f : Y ⟶ X) : (fullSupportPairMap k f).right = f := rfl

private theorem fullSupportPreimage_index (f : Y ⟶ X) [IsOpenImmersion f.left] :
    (coniveauSupportsPreimage k f 0).obj (coniveauFullSupport k X) = coniveauFullSupport k Y := rfl

end FullSupportGeometry

private theorem isZero_smoothTransferRepresentable_of_isEmpty (Y : Sm(k)) (hY : IsEmpty Y.left) :
    IsZero ((smoothTransferRepresentable k).obj Y) := by
  let A : Cor k := Cor.mk Y
  have hz : IsZero A := by
    apply (IsZero.iff_id_eq_zero A).2
    apply Subtype.ext
    ext z
    exact hY.elim ((pullback.fst Y.hom Y.hom).base z)
  exact (transferRepresentable k).map_isZero hz

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} (SheafWithTransfers.{u + 1} k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Use the transfer-sheaf abelian structure in the comparison at stage zero. -/
local instance coniveauStageZeroAbelian : Abelian (LargeSheaves k) := SheafWithTransfers.abelian k

/-- The original quotient map identifies the relative motive for full support. -/
@[no_expose]
def fullSupportMotiveIso :
    (effectiveSmoothMotive k).obj X ≅
      effectivePairMotive k (supportOpenInclusion k X (⊤ : Closeds X.left)) := by
  let U := (SmoothSite.opensFunctor X).obj (⊤ : Closeds X.left).compl
  let j := supportOpenInclusion k X (⊤ : Closeds X.left)
  let R := smoothTransferRepresentable k
  have hU : IsEmpty U.left := ⟨fun x ↦ by
    have hx : x.1 ∉ ((⊤ : Closeds X.left) : Set X.left) := x.2
    exact hx (by simp)⟩
  have hzero : R.map j = 0 :=
    (isZero_smoothTransferRepresentable_of_isEmpty k U hU).eq_of_src _ _
  let p := cokernel.π (R.map j)
  have hp : IsIso p := cokernel.π_of_zero hzero
  let e := @asIso _ _ _ _ p hp
  exact ((smoothTransferRepresentableEffectiveIso k).app X).symm ≪≫
    (effectiveTransferSheaf k).mapIso e

set_option maxHeartbeats 800000 in
-- The comparison uses the literal projection onto the transfer cokernel.
/-- The full-support comparison is induced by the original transfer quotient projection. -/
theorem fullSupportMotiveIso_hom :
    (fullSupportMotiveIso k X).hom = ((smoothTransferRepresentableEffectiveIso k).app X).inv ≫
      (effectiveTransferSheaf k).map ((transferPairProjection k).app
        (Arrow.mk (supportOpenInclusion k X (⊤ : Closeds X.left)))) := by
  unfold fullSupportMotiveIso
  rfl

variable [UnivLE.{u, w'}]

set_option maxHeartbeats 550000 in
-- The terminal index is evaluated in a composite cohomology diagram.
/-- The full support alone represents the zero stage. -/
theorem isIso_ι_coniveauFullSupport (K : DM(k)) (n : ℤ) :
    IsIso (colimit.ι (coniveauCohomologyDiagram k X K n 0) (coniveauFullSupport k X)) :=
  (colimit.isColimit _).isIso_ι_app_of_isTerminal _ (fullSupportIsTerminal k X)

private def coniveauFullSupportColimitIso (K : DM(k)) (n : ℤ) :
    (coniveauCohomologyDiagram k X K n 0).obj (coniveauFullSupport k X) ≅
      coniveauCohomology k X K n 0 := by
  letI := isIso_ι_coniveauFullSupport k X K n
  exact asIso (colimit.ι (coniveauCohomologyDiagram k X K n 0) (coniveauFullSupport k X))

private theorem coniveauFullSupportColimitIso_hom (K : DM(k)) (n : ℤ) :
    (coniveauFullSupportColimitIso k X K n).hom =
      colimit.ι (coniveauCohomologyDiagram k X K n 0) (coniveauFullSupport k X) := rfl

set_option maxHeartbeats 550000 in
-- The represented Hom at the full support has the literal group of the terminal index.
/-- The effective smooth motive computes the cohomology of the full closed support. -/
def coniveauFullSupportComparison (K : DM(k)) (n : ℤ) :
    (coniveauCohomologyDiagram k X K n 0).obj (coniveauFullSupport k X) ≅
      AddCommGrpCat.of ((effectiveSmoothMotive k).obj X ⟶ K⟦n⟧) :=
  (preadditiveYoneda.obj (K⟦n⟧)).mapIso (fullSupportMotiveIso k X).op

/-- At stage zero the cohomology of the full support maps isomorphically to
ordinary cohomology of the original effective smooth motive. -/
@[no_expose]
def coniveauCohomologyZeroIso (K : DM(k)) (n : ℤ) :
    coniveauCohomology k X K n 0 ≅
      AddCommGrpCat.of ((effectiveSmoothMotive k).obj X ⟶ K⟦n⟧) :=
  (coniveauFullSupportColimitIso k X K n).symm ≪≫ coniveauFullSupportComparison k X K n

private theorem coniveauCohomologyZeroIso_hom_eq (K : DM(k)) (n : ℤ) :
    (coniveauCohomologyZeroIso k X K n).hom =
      (coniveauFullSupportColimitIso k X K n).inv ≫
        (coniveauFullSupportComparison k X K n).hom := by
  unfold coniveauCohomologyZeroIso
  rfl

/-- The zero-stage comparison on the full support is the represented Hom comparison. -/
theorem ι_coniveauCohomologyZeroIso_hom (K : DM(k)) (n : ℤ) :
    colimit.ι (coniveauCohomologyDiagram k X K n 0) (coniveauFullSupport k X) ≫
        (coniveauCohomologyZeroIso k X K n).hom = (coniveauFullSupportComparison k X K n).hom := by
  let e := coniveauFullSupportColimitIso k X K n
  let c := coniveauFullSupportComparison k X K n
  have h : e.hom ≫ e.inv ≫ c.hom = c.hom := e.hom_inv_id_assoc c.hom
  rw [← coniveauFullSupportColimitIso_hom, coniveauCohomologyZeroIso_hom_eq]
  exact h

/-- The comparison formula remains valid after mapping out of ordinary cohomology. -/
theorem ι_coniveauCohomologyZeroIso_hom_assoc (K : DM(k)) (n : ℤ) {A : AddCommGrpCat.{w'}}
    (m : AddCommGrpCat.of ((effectiveSmoothMotive k).obj X ⟶ K⟦n⟧) ⟶ A) :
    colimit.ι (coniveauCohomologyDiagram k X K n 0) (coniveauFullSupport k X) ≫
        (coniveauCohomologyZeroIso k X K n).hom ≫ m =
      (coniveauFullSupportComparison k X K n).hom ≫ m := by
  rw [← Category.assoc, ι_coniveauCohomologyZeroIso_hom]

attribute [local irreducible] Cor.graphFunctor transferRepresentable effectiveMotive
  transferPairCokernelFunctor fullSupportMotiveIso coniveauCohomologyZeroIso

variable {X} {Y : Sm(k)}

set_option maxHeartbeats 900000 in
-- The two quotient projections must be identified after effective reflection.
omit [UnivLE.{u, w'}] in
private theorem fullSupportMotiveIso_hom_naturality (f : Y ⟶ X) :
    (effectiveSmoothMotive k).map f ≫ (fullSupportMotiveIso k X).hom =
      (fullSupportMotiveIso k Y).hom ≫ (effectivePairMotiveFunctor k).map
        (fullSupportPairMap k f) := by
  let R := smoothTransferRepresentable k
  let E := effectiveTransferSheaf k
  let M := effectiveSmoothMotive k
  let Q := transferPairCokernelFunctor k
  let π := transferPairProjection k
  let β := smoothTransferRepresentableEffectiveIso k
  let i := supportOpenInclusion k X (⊤ : Closeds X.left)
  let j := supportOpenInclusion k Y (⊤ : Closeds Y.left)
  let α : Arrow.mk j ⟶ Arrow.mk i := fullSupportPairMap k f
  let cX := (fullSupportMotiveIso k X).hom
  let cY := (fullSupportMotiveIso k Y).hom
  have hX : cX = (β.app X).inv ≫ E.map (π.app (Arrow.mk i)) := fullSupportMotiveIso_hom k X
  have hY : cY = (β.app Y).inv ≫ E.map (π.app (Arrow.mk j)) := fullSupportMotiveIso_hom k Y
  have hα : α.right = f := fullSupportPairMap_right k f
  have h : M.map f ≫ cX = cY ≫ (Q ⋙ E).map α :=
    projectedComparison_naturality R E M Q π β f α hα cX cY hX hY
  exact h

set_option maxHeartbeats 550000 in
-- Compare the injections after identifying the two geometric indices of full support.
private theorem fullSupportGenerator_restrict (K : DM(k)) (n : ℤ)
    (f : Y ⟶ X) [IsOpenImmersion f.left] :
    colimit.ι (coniveauCohomologyDiagram k X K n 0) (coniveauFullSupport k X) ≫
        coniveauCohomologyRestrict k K n 0 f =
      closedSupportCohomologyPreimageMap k X K n f ⊤ ≫
        colimit.ι (coniveauCohomologyDiagram k Y K n 0) (coniveauFullSupport k Y) := by
  let F := coniveauCohomologyDiagram k Y K n 0
  let z := coniveauFullSupport k X
  let h := ι_coniveauCohomologyRestrict k K n f z
  have hi := fullSupportPreimage_index k f
  have hι := eq_of_heq (dependent_arg_heq (colimit.ι F) hi)
  exact h.trans (congrArg (closedSupportCohomologyPreimageMap k X K n f ⊤ ≫ ·) hι)

set_option maxHeartbeats 550000 in
-- This is the original motive projection square after applying the shifted Hom functor.
omit [UnivLE.{u, w'}] in
private theorem fullSupportHomComparison_naturality (K : DM(k)) (n : ℤ) (f : Y ⟶ X) :
    (coniveauFullSupportComparison k X K n).hom ≫
        (preadditiveYoneda.obj (K⟦n⟧)).map ((effectiveSmoothMotive k).map f).op =
      closedSupportCohomologyPreimageMap k X K n f ⊤ ≫
        (coniveauFullSupportComparison k Y K n).hom := by
  let H := preadditiveYoneda.obj (K⟦n⟧)
  let u := (effectiveSmoothMotive k).map f
  let eX := (fullSupportMotiveIso k X).hom
  let eY := (fullSupportMotiveIso k Y).hom
  let r := (effectivePairMotiveFunctor k).map (fullSupportPairMap k f)
  have hM : u ≫ eX = eY ≫ r := fullSupportMotiveIso_hom_naturality k f
  have h : H.map eX.op ≫ H.map u.op = H.map r.op ≫ H.map eY.op :=
    map_op_comparison_naturality H u eX eY r hM
  exact h

set_option maxHeartbeats 900000 in
-- The full-support generator compares ordinary and relative shifted Hom functors.
/-- The stage-zero comparison intertwines restriction with the original smooth motive map. -/
theorem coniveauCohomologyZeroIso_hom_restrict_naturality (K : DM(k)) (n : ℤ)
    (f : Y ⟶ X) [IsOpenImmersion f.left] :
    (coniveauCohomologyZeroIso k X K n).hom ≫
        (preadditiveYoneda.obj (K⟦n⟧)).map ((effectiveSmoothMotive k).map f).op =
      coniveauCohomologyRestrict k K n 0 f ≫ (coniveauCohomologyZeroIso k Y K n).hom := by
  let F := coniveauCohomologyDiagram k X K n 0
  let G := coniveauCohomologyDiagram k Y K n 0
  let sX := coniveauFullSupport k X
  let sY := coniveauFullSupport k Y
  let iX := colimit.ι F sX
  let iY := colimit.ι G sY
  let cX := (coniveauCohomologyZeroIso k X K n).hom
  let cY := (coniveauCohomologyZeroIso k Y K n).hom
  let pX := (coniveauFullSupportComparison k X K n).hom
  let pY := (coniveauFullSupportComparison k Y K n).hom
  let r := coniveauCohomologyRestrict k K n 0 f
  let r₀ := closedSupportCohomologyPreimageMap k X K n f (⊤ : Closeds X.left)
  let o := (preadditiveYoneda.obj (K⟦n⟧)).map ((effectiveSmoothMotive k).map f).op
  have hNat : pX ≫ o = r₀ ≫ pY := fullSupportHomComparison_naturality k K n f
  have hR : iX ≫ r = r₀ ≫ iY := fullSupportGenerator_restrict k K n f
  let : IsIso iX := isIso_ι_coniveauFullSupport k X K n
  have h : cX ≫ o = r ≫ cY := comparison_naturality_of_generator iX iY cX cY pX pY r r₀ o
    (ι_coniveauCohomologyZeroIso_hom k X K n) (ι_coniveauCohomologyZeroIso_hom k Y K n) hR hNat
  exact h

variable (X)

/-- The stage-zero comparisons are natural on actual opens of a fixed smooth scheme. -/
theorem coniveauCohomologyZeroIso_hom_openMap_naturality (K : DM(k)) (n : ℤ)
    {U V : X.left.Opens} (f : U ⟶ V) :
    (coniveauCohomologyZeroIso k ((SmoothSite.opensFunctor X).obj V) K n).hom ≫
        (preadditiveYoneda.obj (K⟦n⟧)).map
          ((effectiveSmoothMotive k).map ((SmoothSite.opensFunctor X).map f)).op =
      coniveauCohomologyOpenMap k X K n 0 f ≫
        (coniveauCohomologyZeroIso k ((SmoothSite.opensFunctor X).obj U) K n).hom :=
  coniveauCohomologyZeroIso_hom_restrict_naturality k K n ((SmoothSite.opensFunctor X).map f)

end AlgebraicGeometry.MotivicHomotopy
