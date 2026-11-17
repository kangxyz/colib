/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Basic
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.TransferTriangle
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.OpenImmersion
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.TransferExcision
public import Colib.AlgebraicGeometry.MotivicHomotopy.Purity.PairOpenCoverGeometry
import Colib.AlgebraicGeometry.Sites.Smooth.Cartier.PunctureComparison
import Colib.CategoryTheory.Square.ShortComplex
public import Colib.CategoryTheory.Triangulated.SignedSquare
import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Relative Mayer–Vietoris for two covering opens

The signed Mayer–Vietoris rows of the ambient schemes and their open
complements give a short exact row on the four actual transfer quotients.
Effective reflection takes this row to the distinguished triangle of
relative motives, with the signed difference and sum on its first two sides.
-/

public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme
open scoped ZeroObject


namespace AlgebraicGeometry.MotivicHomotopy

universe u v w w'

section Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The biproduct of the two cokernel projections is a cokernel of the biproduct map. -/
private def biprodCokernelIsColimit {A B A' B' : C} (a : A ⟶ B) (b : A' ⟶ B') :
    IsColimit (CokernelCofork.ofπ (biprod.map (cokernel.π a) (cokernel.π b))
      (show biprod.map a b ≫ biprod.map (cokernel.π a) (cokernel.π b) = 0 by
        apply biprod.hom_ext' <;> simp)) := by
  let π := biprod.map (cokernel.π a) (cokernel.π b)
  have ha {Z : C} (g : B ⊞ B' ⟶ Z) (h : biprod.map a b ≫ g = 0) :
      a ≫ biprod.inl ≫ g = 0 := by
    simpa only [Category.assoc, biprod.inl_map_assoc, comp_zero] using
      congrArg ((biprod.inl : A ⟶ A ⊞ A') ≫ ·) h
  have hb {Z : C} (g : B ⊞ B' ⟶ Z) (h : biprod.map a b ≫ g = 0) :
      b ≫ biprod.inr ≫ g = 0 := by
    simpa only [Category.assoc, biprod.inr_map_assoc, comp_zero] using
      congrArg ((biprod.inr : A' ⟶ A ⊞ A') ≫ ·) h
  refine CokernelCofork.IsColimit.ofπ π _
    (fun g h => biprod.desc (cokernel.desc a (biprod.inl ≫ g) (ha g h))
      (cokernel.desc b (biprod.inr ≫ g) (hb g h))) ?_ ?_
  · intro Z g h
    apply biprod.hom_ext' <;> simp [π]
  · intro Z g h m hm
    apply (cancel_epi π).1
    rw [hm]
    apply biprod.hom_ext' <;> simp [π]

/-- Two short exact rows give a short exact quotient row when the vertical maps are monic. -/
private theorem quotientSequence_shortExact {U X Q : ShortComplex C} (j : U ⟶ X) (π : X ⟶ Q)
    (w : j ≫ π = 0) (hU : U.ShortExact) (hX : X.ShortExact)
    [Mono j.τ₁] [Mono j.τ₂] [Mono j.τ₃]
    (h₁ : IsColimit (CokernelCofork.ofπ π.τ₁
      (show j.τ₁ ≫ π.τ₁ = 0 from congrArg ShortComplex.Hom.τ₁ w)))
    (h₂ : IsColimit (CokernelCofork.ofπ π.τ₂
      (show j.τ₂ ≫ π.τ₂ = 0 from congrArg ShortComplex.Hom.τ₂ w)))
    (h₃ : IsColimit (CokernelCofork.ofπ π.τ₃
      (show j.τ₃ ≫ π.τ₃ = 0 from congrArg ShortComplex.Hom.τ₃ w))) :
    Q.ShortExact := by
  let D : ShortComplex.SnakeInput C :=
    { L₀ := ShortComplex.mk (0 : (0 : C) ⟶ 0) (0 : (0 : C) ⟶ 0) (by simp)
      L₁ := U
      L₂ := X
      L₃ := Q
      v₀₁ := 0
      v₁₂ := j
      v₂₃ := π
      w₀₂ := zero_comp
      w₁₃ := w
      h₀ := by
        apply ShortComplex.isLimitOfIsLimitπ <;>
          apply (KernelFork.isLimitMapConeEquiv _ _).2 <;>
          apply KernelFork.IsLimit.ofMonoOfIsZero
        · exact (inferInstance : Mono j.τ₁)
        · exact isZero_zero C
        · exact (inferInstance : Mono j.τ₂)
        · exact isZero_zero C
        · exact (inferInstance : Mono j.τ₃)
        · exact isZero_zero C
      h₃ := by
        apply ShortComplex.isColimitOfIsColimitπ <;>
          apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
        · exact h₁
        · exact h₂
        · exact h₃
      L₁_exact := hU.exact
      epi_L₁_g := hU.epi_g
      L₂_exact := hX.exact
      mono_L₂_f := hX.mono_f }
  let : Epi X.g := hX.epi_g
  refine ShortComplex.ShortExact.mk' D.L₃_exact ?_ (D.epi_L₃_g)
  have hδ : D.δ = 0 := (isZero_zero C).eq_of_src (D.δ : (0 : C) ⟶ Q.X₁) 0
  exact (D.L₂'.exact_iff_mono hδ).1 D.L₂'_exact

end Abelian

section Cover

variable {C : Type u} [Category.{v} C]

/-- The four vertical pair inclusions and their maps along the cover. -/
@[expose] def arrowSquare {U X : Square C} (j : U ⟶ X) : Square (Arrow C) where
  X₁ := Arrow.mk j.τ₁
  X₂ := Arrow.mk j.τ₂
  X₃ := Arrow.mk j.τ₃
  X₄ := Arrow.mk j.τ₄
  f₁₂ := Arrow.homMk' U.f₁₂ X.f₁₂ j.comm₁₂
  f₁₃ := Arrow.homMk' U.f₁₃ X.f₁₃ j.comm₁₃
  f₂₄ := Arrow.homMk' U.f₂₄ X.f₂₄ j.comm₂₄
  f₃₄ := Arrow.homMk' U.f₃₄ X.f₃₄ j.comm₃₄
  fac := by ext; exacts [U.fac, X.fac]

/-- A compatible map of covers is a map of the four pair arrows. -/
private def arrowSquareMap {U X U' X' : Square C} {j : U ⟶ X} {j' : U' ⟶ X'}
    (a : U ⟶ U') (b : X ⟶ X') (h : j ≫ b = a ≫ j') :
    arrowSquare j ⟶ arrowSquare j' where
  τ₁ := Arrow.homMk' a.τ₁ b.τ₁ (congrArg Square.Hom.τ₁ h.symm)
  τ₂ := Arrow.homMk' a.τ₂ b.τ₂ (congrArg Square.Hom.τ₂ h.symm)
  τ₃ := Arrow.homMk' a.τ₃ b.τ₃ (congrArg Square.Hom.τ₃ h.symm)
  τ₄ := Arrow.homMk' a.τ₄ b.τ₄ (congrArg Square.Hom.τ₄ h.symm)
  comm₁₂ := by ext; exacts [a.comm₁₂, b.comm₁₂]
  comm₁₃ := by ext; exacts [a.comm₁₃, b.comm₁₃]
  comm₂₄ := by ext; exacts [a.comm₂₄, b.comm₂₄]
  comm₃₄ := by ext; exacts [a.comm₃₄, b.comm₃₄]

variable {D : Type*} [Category* D] [Abelian D]

/-- Take the quotient of the transfer rows without changing any corner quotient. -/
private theorem quotientCoverSequence_shortExact (F : C ⥤ D) {U X : Square C} (j : U ⟶ X)
    (hU : (U.map F).commSq.shortComplex.ShortExact)
    (hX : (X.map F).commSq.shortComplex.ShortExact)
    [Mono (F.map j.τ₁)] [Mono (F.map j.τ₂)] [Mono (F.map j.τ₃)] [Mono (F.map j.τ₄)] :
    ((arrowSquare j).map (F.mapArrow ⋙ coker D)).commSq.shortComplex.ShortExact := by
  let J := (Square.shortComplexFunctor D).map ((F.mapSquare).map j)
  let P := Functor.whiskerLeft F.mapArrow (coker.π D)
  let π := (Square.shortComplexFunctor D).map (P.mapSquare.app (arrowSquare j))
  have w : J ≫ π = 0 := by
    apply ShortComplex.hom_ext
    · exact cokernel.condition (F.map j.τ₁)
    · change biprod.map (F.map j.τ₂) (F.map j.τ₃) ≫
        biprod.map (cokernel.π (F.map j.τ₂)) (cokernel.π (F.map j.τ₃)) = 0
      apply biprod.hom_ext' <;> simp
    · exact cokernel.condition (F.map j.τ₄)
  let : Mono J.τ₁ := inferInstanceAs (Mono (F.map j.τ₁))
  let : Mono J.τ₂ := inferInstanceAs (Mono (biprod.map (F.map j.τ₂) (F.map j.τ₃)))
  let : Mono J.τ₃ := inferInstanceAs (Mono (F.map j.τ₄))
  exact quotientSequence_shortExact J π w hU hX
    (cokernelIsCokernel (F.map j.τ₁))
    (biprodCokernelIsColimit (F.map j.τ₂) (F.map j.τ₃))
    (cokernelIsCokernel (F.map j.τ₄))

end Cover

open SheafWithTransfers

-- Keep the represented coefficient functors opaque during triangle-map elaboration.
attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "NST(" field ")" => LargeSheaves field

/-- The canonical abelian structure on sheaves with transfers. -/
local instance pairOpenCoverAbelian : Abelian NST(k) := SheafWithTransfers.abelian k

/-- The square of actual transfer quotients of the four restricted pairs. -/
@[expose] def transferPairOpenCoverSquare {U X : Square Sm(k)} (j : U ⟶ X) : Square NST(k) :=
  (arrowSquare j).map (transferPairCokernelFunctor k)

/-- The relative transfer row has the signed difference and sum of the actual quotient maps. -/
abbrev transferPairOpenCoverSequence {U X : Square Sm(k)} (j : U ⟶ X) :
    ShortComplex NST(k) := (transferPairOpenCoverSquare k j).commSq.shortComplex

set_option maxHeartbeats 2400000 in
-- Identify the original maps of all four transfer cokernels.
/-- Two compatible pullback cover squares and open complement inclusions
induce a short exact row of relative transfer quotients. -/
theorem transferPairOpenCoverSequence_shortExact {U X : Square Sm(k)} (j : U ⟶ X)
    (hU : U.IsPullback) (hX : X.IsPullback)
    [IsOpenImmersion U.f₂₄.left] [IsOpenImmersion U.f₃₄.left]
    [IsOpenImmersion X.f₂₄.left] [IsOpenImmersion X.f₃₄.left]
    [IsOpenImmersion j.τ₁.left] [IsOpenImmersion j.τ₂.left]
    [IsOpenImmersion j.τ₃.left] [IsOpenImmersion j.τ₄.left]
    (cU : Set.range U.f₂₄.left ∪ Set.range U.f₃₄.left = Set.univ)
    (cX : Set.range X.f₂₄.left ∪ Set.range X.f₃₄.left = Set.univ) :
    (transferPairOpenCoverSequence k j).ShortExact := by
  let : Mono ((smoothTransferRepresentable k).map j.τ₁) :=
    mono_transferRepresentable_map_openImmersion k j.τ₁
  let : Mono ((smoothTransferRepresentable k).map j.τ₂) :=
    mono_transferRepresentable_map_openImmersion k j.τ₂
  let : Mono ((smoothTransferRepresentable k).map j.τ₃) :=
    mono_transferRepresentable_map_openImmersion k j.τ₃
  let : Mono ((smoothTransferRepresentable k).map j.τ₄) :=
    mono_transferRepresentable_map_openImmersion k j.τ₄
  exact quotientCoverSequence_shortExact (smoothTransferRepresentable k) j
    (transferMayerVietorisSequence_shortExact k U hU
      (transferSquare_isPushout_of_openCover k U hU cU))
    (transferMayerVietorisSequence_shortExact k X hX
      (transferSquare_isPushout_of_openCover k X hX cX))

set_option maxHeartbeats 2400000 in
-- Identify the source and target of the functor on the four arrow quotients.
private def transferPairOpenCoverSquareMap {U X U' X' : Square Sm(k)} {j : U ⟶ X} {j' : U' ⟶ X'}
    (a : U ⟶ U') (b : X ⟶ X') (h : j ≫ b = a ≫ j') :
    transferPairOpenCoverSquare k j ⟶ transferPairOpenCoverSquare k j' :=
  (transferPairCokernelFunctor k).mapSquare.map (arrowSquareMap a b h)

set_option maxHeartbeats 2400000 in
-- Identify the terms of the signed row with those of the quotient square.
/-- Compatible maps of cover squares induce the actual maps on the four relative quotients. -/
def transferPairOpenCoverSequenceMap {U X U' X' : Square Sm(k)} {j : U ⟶ X} {j' : U' ⟶ X'}
    (a : U ⟶ U') (b : X ⟶ X') (h : j ≫ b = a ≫ j') :
    transferPairOpenCoverSequence k j ⟶ transferPairOpenCoverSequence k j' :=
  (Square.shortComplexFunctor NST(k)).map (transferPairOpenCoverSquareMap k a b h)

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} NST(k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

local notation "F" => effectiveTransferSheaf k

local instance instPairOpenCoverPreservesBinaryBiproducts :
    PreservesBinaryBiproducts (F) :=
  preservesBinaryBiproducts_of_preservesBiproducts (F)

set_option maxHeartbeats 2400000 in
-- Identify the four reflected corners of the cover and the endpoints of the boundary.
/-- The relative Mayer–Vietoris triangle on the actual motives of the four pairs.
Use `transferPairOpenCoverSequence_shortExact` for two covering opens. -/
@[expose] def effectivePairOpenCoverTriangle {U X : Square Sm(k)} {j : U ⟶ X}
    (h : (transferPairOpenCoverSequence k j).ShortExact) :
    Triangle (EffectiveMotivesMinus k) :=
  ((transferPairOpenCoverSquare k j).map (F)).shortComplexTriangle
    (effectiveTransferSheafConnecting k h)

set_option maxHeartbeats 2400000 in
-- Identify the reflected transfer row with the image of the quotient square.
/-- The original reflected transfer row identifies the relative cover triangle. -/
@[expose] def effectivePairOpenCoverTriangleIso {U X : Square Sm(k)} {j : U ⟶ X}
    (h : (transferPairOpenCoverSequence k j).ShortExact) :
    effectiveTransferSheafTriangle k h ≅ effectivePairOpenCoverTriangle k h :=
  Square.mapShortComplexTriangleIso (F) (transferPairOpenCoverSquare k j)
    (effectiveTransferSheafConnecting k h)

/-- The relative Mayer–Vietoris triangle is distinguished. -/
theorem effectivePairOpenCoverTriangle_distinguished {U X : Square Sm(k)} {j : U ⟶ X}
    (h : (transferPairOpenCoverSequence k j).ShortExact) :
    effectivePairOpenCoverTriangle k h ∈ distTriang _ :=
  isomorphic_distinguished _ (effectiveTransferSheafTriangle_distinguished k h) _
    (effectivePairOpenCoverTriangleIso k h).symm

set_option maxHeartbeats 2400000 in
-- Identify the connecting-map square with that of the native transfer triangle.
/-- Compatible maps of two covers induce a morphism of the relative triangles. -/
def effectivePairOpenCoverTriangleMap {U X U' X' : Square Sm(k)} {j : U ⟶ X} {j' : U' ⟶ X'}
    (a : U ⟶ U') (b : X ⟶ X') (h : j ≫ b = a ≫ j')
    (h₁ : (transferPairOpenCoverSequence k j).ShortExact)
    (h₂ : (transferPairOpenCoverSequence k j').ShortExact) :
    effectivePairOpenCoverTriangle k h₁ ⟶ effectivePairOpenCoverTriangle k h₂ := by
  let m := (F).mapSquare.map (transferPairOpenCoverSquareMap k a b h)
  let p := effectiveTransferSheafTriangleMap k h₁ h₂ (transferPairOpenCoverSequenceMap k a b h)
  exact Square.shortComplexTriangleMap m
    (δ := effectiveTransferSheafConnecting k h₁) (ε := effectiveTransferSheafConnecting k h₂)
    p.comm₃

section Comparison

variable {U X U' X' : Square Sm(k)} {j : U ⟶ X} {j' : U' ⟶ X'}
  (a : U ⟶ U') (b : X ⟶ X') (h : j ≫ b = a ≫ j')
  (h₁ : (transferPairOpenCoverSequence k j).ShortExact)
  (h₂ : (transferPairOpenCoverSequence k j').ShortExact)

local notation "M" => effectivePairMotiveFunctor k

set_option maxHeartbeats 2400000 in
-- Read the reflected quotient at the overlap.
/-- The comparison is the original pair map on the overlap. -/
theorem effectivePairOpenCoverTriangleMap_hom₁ :
    (effectivePairOpenCoverTriangleMap k a b h h₁ h₂).hom₁ =
      (M).map (Arrow.homMk' a.τ₁ b.τ₁ (congrArg Square.Hom.τ₁ h.symm)) := (rfl)

set_option maxHeartbeats 2400000 in
-- Read the reflected quotients at both cover charts.
/-- The comparison is the biproduct of the original pair maps on the charts. -/
theorem effectivePairOpenCoverTriangleMap_hom₂ :
    (effectivePairOpenCoverTriangleMap k a b h h₁ h₂).hom₂ =
      biprod.map ((M).map (Arrow.homMk' a.τ₂ b.τ₂ (congrArg Square.Hom.τ₂ h.symm)))
        ((M).map (Arrow.homMk' a.τ₃ b.τ₃ (congrArg Square.Hom.τ₃ h.symm))) := (rfl)

set_option maxHeartbeats 2400000 in
-- Read the reflected quotient at the union.
/-- The comparison is the original pair map on the total pair. -/
theorem effectivePairOpenCoverTriangleMap_hom₃ :
    (effectivePairOpenCoverTriangleMap k a b h h₁ h₂).hom₃ =
      (M).map (Arrow.homMk' a.τ₄ b.τ₄ (congrArg Square.Hom.τ₄ h.symm)) := (rfl)

include h₁ h₂ in
/-- An isomorphism on the two charts and their overlap gives an isomorphism
on the original motive map of the total pair. -/
theorem isIso_effectivePairOpenCoverMap_of_isIso_charts
    (e₁ : IsIso ((M).map (Arrow.homMk' a.τ₁ b.τ₁ (congrArg Square.Hom.τ₁ h.symm))))
    (e₂ : IsIso ((M).map (Arrow.homMk' a.τ₂ b.τ₂ (congrArg Square.Hom.τ₂ h.symm))))
    (e₃ : IsIso ((M).map (Arrow.homMk' a.τ₃ b.τ₃ (congrArg Square.Hom.τ₃ h.symm)))) :
    IsIso ((M).map (Arrow.homMk' a.τ₄ b.τ₄ (congrArg Square.Hom.τ₄ h.symm))) := by
  rw [← effectivePairOpenCoverTriangleMap_hom₃ k a b h h₁ h₂]
  apply isIso₃_of_isIso₁₂ (effectivePairOpenCoverTriangleMap k a b h h₁ h₂)
    (effectivePairOpenCoverTriangle_distinguished k h₁)
    (effectivePairOpenCoverTriangle_distinguished k h₂)
  · rw [effectivePairOpenCoverTriangleMap_hom₁]
    exact e₁
  · rw [effectivePairOpenCoverTriangleMap_hom₂]
    let bIso := biprod.mapIso (@asIso _ _ _ _ _ e₂) (@asIso _ _ _ _ _ e₃)
    exact (inferInstance : IsIso bIso.hom)

end Comparison


/-- A predicate with binary Mayer–Vietoris descent holds on a finite union
if it holds on every subopen of each covering chart. -/
theorem predicate_of_finset_sup {ι L : Type*} [Lattice L] [OrderBot L]
    (P : L → Prop) (hbot : P ⊥)
    (hstep : ∀ V W : L, P V → P W → P (V ⊓ W) → P (V ⊔ W))
    (s : Finset ι) (cover : ι → L) (hloc : ∀ i ∈ s, ∀ V ≤ cover i, P V) :
    P (s.sup cover) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using hbot
  | @insert i s hi ih =>
    rw [Finset.sup_insert]
    exact hstep (cover i) (s.sup cover)
      (hloc i (Finset.mem_insert_self i s) _ le_rfl)
      (ih (fun l hl => hloc l (Finset.mem_insert_of_mem hl)))
      (hloc i (Finset.mem_insert_self i s) _ inf_le_left)

/-- Finite union descent needs only smaller chart opens in a class closed under intersection. -/
theorem predicate_of_finset_sup_of_inf_closed {ι L : Type*} [DistribLattice L] [OrderBot L]
    (P Q : L → Prop) (hbot : P ⊥)
    (hstep : ∀ V W : L, P V → P W → P (V ⊓ W) → P (V ⊔ W))
    (hQ : ∀ V W : L, Q V → Q W → Q (V ⊓ W))
    (s : Finset ι) (cover : ι → L) (hcover : ∀ i ∈ s, Q (cover i))
    (hloc : ∀ i ∈ s, ∀ V ≤ cover i, Q V → P V) : P (s.sup cover) := by
  classical
  have H (t : Finset ι) (hsub : t ⊆ s) : ∀ V, Q V → P (V ⊓ t.sup cover) := by
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sup_empty, inf_bot_eq] using fun _ _ => hbot
    | @insert i t hi ih =>
      intro V hV
      have ht : t ⊆ s := fun j hj => hsub (Finset.mem_insert_of_mem hj)
      have hs : i ∈ s := hsub (Finset.mem_insert_self i t)
      rw [Finset.sup_insert, inf_sup_left]
      exact hstep _ _ (hloc i hs _ inf_le_right (hQ _ _ hV (hcover i hs))) (ih ht V hV)
        (by
          have e : (V ⊓ cover i) ⊓ (V ⊓ t.sup cover) = (V ⊓ cover i) ⊓ t.sup cover := by
            apply le_antisymm
            · exact le_inf inf_le_left (inf_le_right.trans inf_le_right)
            · exact le_inf inf_le_left (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
          rw [e]
          exact ih ht (V ⊓ cover i) (hQ _ _ hV (hcover i hs)))
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty] using hbot
  | @insert i t hi ih =>
    rw [Finset.sup_insert]
    have hx := Finset.mem_insert_self i t
    have ht : t ⊆ insert i t := fun j hj => Finset.mem_insert_of_mem hj
    exact hstep _ _ (hloc i hx _ le_rfl (hcover i hx))
      (ih (fun j hj => hcover j (ht hj)) (fun j hj => hloc j (ht hj))
        (fun t' hsub => H t' (hsub.trans ht)))
      (H t ht _ (hcover i hx))

section Locality

open AlgebraicGeometry.Scheme.SmoothSite

variable {U X U' X' : Sm(k)} (j : U ⟶ X) (j' : U' ⟶ X')
  [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left]
  (a : U ⟶ U') (b : X ⟶ X') (h : a ≫ j' = j ≫ b)

local notation "P" => effectivePairMotiveFunctor k

include h in
omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory NST(k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]
  [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left] in
private theorem pairOpenPreimage_le (W : X'.left.Opens) :
    (j.left ⁻¹ᵁ (b.left ⁻¹ᵁ W)) ≤ a.left ⁻¹ᵁ (j'.left ⁻¹ᵁ W) := by
  have H : a.left ≫ j'.left = j.left ≫ b.left :=
    congrArg (fun f : U ⟶ X' => f.left) h
  rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage,
    ← AlgebraicGeometry.Scheme.Hom.comp_preimage, H]

private def pairComparisonOpenMap (W : X'.left.Opens) :
    (opensFunctor U).obj (j.left ⁻¹ᵁ (b.left ⁻¹ᵁ W)) ⟶
      (opensFunctor U').obj (j'.left ⁻¹ᵁ W) :=
  restrictedOpenMap U' a (j'.left ⁻¹ᵁ W) (j.left ⁻¹ᵁ (b.left ⁻¹ᵁ W))
    (pairOpenPreimage_le k j j' a b h W)

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory NST(k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]
  [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left] in
private theorem pairComparisonOpenMap_comm (W : X'.left.Opens) :
    pairComparisonOpenMap k j j' a b h W ≫ preimageOpenMap X' j' W =
      preimageOpenMap X j (b.left ⁻¹ᵁ W) ≫ preimageOpenMap X' b W := by
  let T := j.left ⁻¹ᵁ (b.left ⁻¹ᵁ W)
  let e := pairOpenPreimage_le k j j' a b h W
  apply MorphismProperty.Over.Hom.ext
  apply (cancel_mono W.ι).1
  change (a.left.resLE (j'.left ⁻¹ᵁ W) T e ≫
      j'.left.resLE W (j'.left ⁻¹ᵁ W) le_rfl) ≫ W.ι =
    (j.left.resLE (b.left ⁻¹ᵁ W) T le_rfl ≫
      b.left.resLE W (b.left ⁻¹ᵁ W) le_rfl) ≫ W.ι
  have H : a.left ≫ j'.left = j.left ≫ b.left :=
    congrArg (fun f : U ⟶ X' => f.left) h
  simp only [Category.assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι,
    AlgebraicGeometry.Scheme.Hom.resLE_comp_ι_assoc]
  exact (Category.assoc _ _ _).trans ((congrArg (T.ι ≫ ·) H).trans (Category.assoc _ _ _).symm)

variable {k} in
/-- The map of actual open inclusions, restricted over an open of the target ambient scheme. -/
def pairArrowMapOnOpen (W : X'.left.Opens) :
    Arrow.mk (preimageOpenMap X j (b.left ⁻¹ᵁ W)) ⟶ Arrow.mk (preimageOpenMap X' j' W) :=
  Arrow.homMk' (pairComparisonOpenMap k j j' a b h W)
    (preimageOpenMap X' b W) (pairComparisonOpenMap_comm k j j' a b h W)

/-- The original map of pairs, restricted over an open of the target ambient scheme. -/
def effectivePairMapOnOpen (W : X'.left.Opens) :
    effectivePairMotive k (preimageOpenMap X j (b.left ⁻¹ᵁ W)) ⟶
      effectivePairMotive k (preimageOpenMap X' j' W) :=
  (P).map (pairArrowMapOnOpen j j' a b h W)

omit [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left] in
/-- The map on a restricted open pair is the relative motive of its original arrow map. -/
theorem effectivePairMapOnOpen_eq_map (W : X'.left.Opens) :
    effectivePairMapOnOpen k j j' a b h W = (P).map (pairArrowMapOnOpen j j' a b h W) := (rfl)

variable {k} in
/-- The restricted pair maps commute with their actual open inclusions. -/
@[expose] def pairArrowOpenInclusion {U X : Sm(k)} (j : U ⟶ X) (W : X.left.Opens) :
    Arrow.mk (preimageOpenMap X j W) ⟶ Arrow.mk j :=
  Arrow.homMk' (openInclusion U (j.left ⁻¹ᵁ W)) (openInclusion X W)
    (restrictedOpenMap_comp_openInclusion X j W _ le_rfl).symm

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory NST(k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]
  [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left] in
variable {k} in
/-- Comparison with the original pair maps comes from the given open inclusions. -/
theorem pairArrowMapOnOpen_comp (W : X'.left.Opens) :
    pairArrowMapOnOpen j j' a b h W ≫ pairArrowOpenInclusion j' W =
      pairArrowOpenInclusion j (b.left ⁻¹ᵁ W) ≫ Arrow.homMk' a b h := by
  apply Arrow.hom_ext
  · exact restrictedOpenMap_comp_openInclusion U' a (j'.left ⁻¹ᵁ W)
      (j.left ⁻¹ᵁ (b.left ⁻¹ᵁ W)) (pairOpenPreimage_le k j j' a b h W)
  · exact restrictedOpenMap_comp_openInclusion X' b W _ le_rfl

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory NST(k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]
  [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left] in
private theorem pairComparisonOpenMap_naturality {V W : X'.left.Opens} (e : V ≤ W) :
    (opensFunctor U).map (homOfLE (j.left.preimage_mono (b.left.preimage_mono e))) ≫
        pairComparisonOpenMap k j j' a b h W =
      pairComparisonOpenMap k j j' a b h V ≫
        (opensFunctor U').map (homOfLE (j'.left.preimage_mono e)) :=
  restrictedOpenMap_naturality U' a (j'.left.preimage_mono e)
    (j.left.preimage_mono (b.left.preimage_mono e))
    (pairOpenPreimage_le k j j' a b h V) (pairOpenPreimage_le k j j' a b h W)

private def pairComparisonOpenUnionCoverMap (V W : X'.left.Opens) :
    openUnionCoverSquare U (j.left ⁻¹ᵁ (b.left ⁻¹ᵁ V))
        (j.left ⁻¹ᵁ (b.left ⁻¹ᵁ W)) ⟶
      openUnionCoverSquare U' (j'.left ⁻¹ᵁ V) (j'.left ⁻¹ᵁ W) where
  τ₁ := pairComparisonOpenMap k j j' a b h (V ⊓ W)
  τ₂ := pairComparisonOpenMap k j j' a b h V
  τ₃ := pairComparisonOpenMap k j j' a b h W
  τ₄ := pairComparisonOpenMap k j j' a b h (V ⊔ W)
  comm₁₂ := pairComparisonOpenMap_naturality k j j' a b h (inf_le_left : V ⊓ W ≤ V)
  comm₁₃ := pairComparisonOpenMap_naturality k j j' a b h (inf_le_right : V ⊓ W ≤ W)
  comm₂₄ := pairComparisonOpenMap_naturality k j j' a b h (le_sup_left : V ≤ V ⊔ W)
  comm₃₄ := pairComparisonOpenMap_naturality k j j' a b h (le_sup_right : W ≤ V ⊔ W)

set_option maxHeartbeats 2400000 in
-- Compare the four component maps after nested restriction.
omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory NST(k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]
  [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left] in
private theorem pairOpenUnionCoverMaps_comm (V W : X'.left.Opens) :
    preimageOpenUnionCoverMap X (b.left ⁻¹ᵁ V) (b.left ⁻¹ᵁ W) j ≫
        preimageOpenUnionCoverMap X' V W b =
      pairComparisonOpenUnionCoverMap k j j' a b h V W ≫
        preimageOpenUnionCoverMap X' V W j' := by
  apply Square.Hom.ext
  · exact (pairComparisonOpenMap_comm k j j' a b h (V ⊓ W)).symm
  · exact (pairComparisonOpenMap_comm k j j' a b h V).symm
  · exact (pairComparisonOpenMap_comm k j j' a b h W).symm
  · exact (pairComparisonOpenMap_comm k j j' a b h (V ⊔ W)).symm

set_option maxHeartbeats 2400000 in
-- Compare the two actual two-open covers after four preimages.
/-- A relative motive map is invertible on the union of two opens if its
actual restrictions to the two opens and to their intersection are invertible. -/
theorem isIso_effectivePairMapOnOpen_sup (V W : X'.left.Opens)
    (hV : IsIso (effectivePairMapOnOpen k j j' a b h V))
    (hW : IsIso (effectivePairMapOnOpen k j j' a b h W))
    (hVW : IsIso (effectivePairMapOnOpen k j j' a b h (V ⊓ W))) :
    IsIso (effectivePairMapOnOpen k j j' a b h (V ⊔ W)) := by
  let X₀ := openUnionCoverSquare X (b.left ⁻¹ᵁ V) (b.left ⁻¹ᵁ W)
  let X₁ := openUnionCoverSquare X' V W
  let U₀ := openUnionCoverSquare U (j.left ⁻¹ᵁ (b.left ⁻¹ᵁ V))
    (j.left ⁻¹ᵁ (b.left ⁻¹ᵁ W))
  let U₁ := openUnionCoverSquare U' (j'.left ⁻¹ᵁ V) (j'.left ⁻¹ᵁ W)
  let A : U₀ ⟶ U₁ := pairComparisonOpenUnionCoverMap k j j' a b h V W
  let B : X₀ ⟶ X₁ := preimageOpenUnionCoverMap X' V W b
  let j₀ : U₀ ⟶ X₀ := preimageOpenUnionCoverMap X (b.left ⁻¹ᵁ V) (b.left ⁻¹ᵁ W) j
  let j₁ : U₁ ⟶ X₁ := preimageOpenUnionCoverMap X' V W j'
  have H : j₀ ≫ B = A ≫ j₁ := pairOpenUnionCoverMaps_comm k j j' a b h V W
  let : AlgebraicGeometry.IsOpenImmersion j₀.τ₁.left := inferInstanceAs
    (AlgebraicGeometry.IsOpenImmersion (preimageOpenMap X j (b.left ⁻¹ᵁ (V ⊓ W))).left)
  let : AlgebraicGeometry.IsOpenImmersion j₀.τ₂.left := inferInstanceAs
    (AlgebraicGeometry.IsOpenImmersion (preimageOpenMap X j (b.left ⁻¹ᵁ V)).left)
  let : AlgebraicGeometry.IsOpenImmersion j₀.τ₃.left := inferInstanceAs
    (AlgebraicGeometry.IsOpenImmersion (preimageOpenMap X j (b.left ⁻¹ᵁ W)).left)
  let : AlgebraicGeometry.IsOpenImmersion j₀.τ₄.left := inferInstanceAs
    (AlgebraicGeometry.IsOpenImmersion (preimageOpenMap X j (b.left ⁻¹ᵁ (V ⊔ W))).left)
  let : AlgebraicGeometry.IsOpenImmersion j₁.τ₁.left := inferInstanceAs
    (AlgebraicGeometry.IsOpenImmersion (preimageOpenMap X' j' (V ⊓ W)).left)
  let : AlgebraicGeometry.IsOpenImmersion j₁.τ₂.left := inferInstanceAs
    (AlgebraicGeometry.IsOpenImmersion (preimageOpenMap X' j' V).left)
  let : AlgebraicGeometry.IsOpenImmersion j₁.τ₃.left := inferInstanceAs
    (AlgebraicGeometry.IsOpenImmersion (preimageOpenMap X' j' W).left)
  let : AlgebraicGeometry.IsOpenImmersion j₁.τ₄.left := inferInstanceAs
    (AlgebraicGeometry.IsOpenImmersion (preimageOpenMap X' j' (V ⊔ W)).left)
  have h₀ := transferPairOpenCoverSequence_shortExact k j₀
    (openUnionCoverSquare_isPullback U _ _) (openUnionCoverSquare_isPullback X _ _)
    (openUnionCoverSquare_range_cover U _ _) (openUnionCoverSquare_range_cover X _ _)
  have h₁ := transferPairOpenCoverSequence_shortExact k j₁
    (openUnionCoverSquare_isPullback U' _ _) (openUnionCoverSquare_isPullback X' V W)
    (openUnionCoverSquare_range_cover U' _ _) (openUnionCoverSquare_range_cover X' V W)
  exact isIso_effectivePairOpenCoverMap_of_isIso_charts k A B H h₀ h₁ hVW hV hW

omit [PerfectField k] [HasDerivedCategory (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory NST(k)]
  [HasExt (Sheaf (SmoothSite.nisnevichTopology (Spec (CommRingCat.of k))) AddCommGrpCat.{u + 1})]
  [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left] in
private theorem isIso_preimageOpenMap_of_le_range {X U : Sm(k)} (j : U ⟶ X)
    [AlgebraicGeometry.IsOpenImmersion j.left] (W : X.left.Opens) (hW : W ≤ j.left.opensRange) :
    IsIso (preimageOpenMap X j W) := by
  refine @isIso_of_reflects_iso _ _ _ _ _ _ (preimageOpenMap X j W) (forgetScheme _) ?_ _
  change IsIso (preimageOpenMap X j W).left
  apply AlgebraicGeometry.isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply SetLike.coe_injective
  rw [AlgebraicGeometry.Scheme.Hom.coe_opensRange]
  ext x
  constructor
  · intro _
    trivial
  · intro _
    obtain ⟨y, hy⟩ := hW x.property
    have hyW : y ∈ j.left ⁻¹ᵁ W := by
      rw [AlgebraicGeometry.Scheme.Hom.mem_preimage, hy]
      exact x.property
    refine ⟨⟨y, hyW⟩, ?_⟩
    apply Subtype.ext
    change ((j.left.resLE W (j.left ⁻¹ᵁ W) le_rfl ≫ W.ι) ⟨y, _⟩) = x.val
    rw [AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
    exact hy

/-- A cartesian morphism of open pairs is invertible on the relative motives over an open
contained in the target's indicated open complement. -/
theorem isIso_effectivePairMapOnOpen_of_le_range (W : X'.left.Opens)
    (hW : W ≤ j'.left.opensRange) (hp : IsPullback a.left j.left j'.left b.left) :
    IsIso (effectivePairMapOnOpen k j j' a b h W) := by
  have hR : b.left ⁻¹ᵁ W ≤ j.left.opensRange := by
    apply (b.left.preimage_mono hW).trans
    apply le_of_eq
    apply SetLike.coe_injective
    rw [AlgebraicGeometry.Scheme.Hom.coe_preimage, AlgebraicGeometry.Scheme.Hom.coe_opensRange,
      AlgebraicGeometry.Scheme.Hom.coe_opensRange]
    exact (range_fst_of_cartesian hp.flip).symm
  let q := preimageOpenMap X j (b.left ⁻¹ᵁ W)
  let q' := preimageOpenMap X' j' W
  let : IsIso q := isIso_preimageOpenMap_of_le_range k j _ hR
  let : IsIso q' := isIso_preimageOpenMap_of_le_range k j' _ hW
  let R := smoothTransferRepresentable k
  have hz : IsZero (effectivePairMotive k q) := (F).map_isZero (isZero_cokernel_of_epi (R.map q))
  have hz' : IsZero (effectivePairMotive k q') := (F).map_isZero (isZero_cokernel_of_epi (R.map q'))
  exact hz.isIso hz' (effectivePairMapOnOpen k j j' a b h W)

omit [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left] in
/-- The relative motive over the empty open is zero on both sides. -/
theorem isIso_effectivePairMapOnOpen_bot :
    IsIso (effectivePairMapOnOpen k j j' a b h ⊥) := by
  let q := preimageOpenMap X j (b.left ⁻¹ᵁ (⊥ : X'.left.Opens))
  let q' := preimageOpenMap X' j' (⊥ : X'.left.Opens)
  let : IsEmpty ((opensFunctor X).obj (b.left ⁻¹ᵁ (⊥ : X'.left.Opens))).left := by
    change IsEmpty (b.left ⁻¹ᵁ (⊥ : X'.left.Opens)).toScheme
    rw [AlgebraicGeometry.Scheme.Hom.preimage_bot]
    exact ⟨fun x => x.property⟩
  let : IsEmpty ((opensFunctor X').obj (⊥ : X'.left.Opens)).left :=
    ⟨fun x => x.property⟩
  let : IsIso q := by
    refine @isIso_of_reflects_iso _ _ _ _ _ _ q (forgetScheme _) ?_ _
    exact inferInstanceAs (IsIso q.left)
  let : IsIso q' := by
    refine @isIso_of_reflects_iso _ _ _ _ _ _ q' (forgetScheme _) ?_ _
    exact inferInstanceAs (IsIso q'.left)
  let R := smoothTransferRepresentable k
  have hz : IsZero (effectivePairMotive k q) :=
    ((F).map_isZero (isZero_cokernel_of_epi (R.map q)))
  have hz' : IsZero (effectivePairMotive k q') :=
    ((F).map_isZero (isZero_cokernel_of_epi (R.map q')))
  exact hz.isIso hz' (effectivePairMapOnOpen k j j' a b h ⊥)

omit [AlgebraicGeometry.IsOpenImmersion j.left] [AlgebraicGeometry.IsOpenImmersion j'.left] in
private theorem isIso_effectivePairMap_of_isIso_top
    (H : IsIso (effectivePairMapOnOpen k j j' a b h ⊤)) :
    IsIso ((P).map (Arrow.homMk' a b h)) := by
  let c₀ := pairArrowOpenInclusion j (b.left ⁻¹ᵁ (⊤ : X'.left.Opens))
  let c₁ := pairArrowOpenInclusion j' (⊤ : X'.left.Opens)
  have hIso {A : Sm(k)} (W : A.left.Opens) (e : W = ⊤) :
      IsIso (openInclusion A W) := by
    subst W
    refine @isIso_of_reflects_iso _ _ _ _ _ _ (openInclusion A ⊤) (forgetScheme _) ?_ _
    exact inferInstanceAs (IsIso A.left.topIso.hom)
  let : IsIso c₀.left := hIso _ (by simp)
  let : IsIso c₀.right := hIso _ (by simp)
  let : IsIso c₁.left := hIso _ (by simp)
  let : IsIso c₁.right := hIso _ rfl
  let : IsIso c₀ := Arrow.isIso_of_isIso_left_of_isIso_right c₀
  let : IsIso c₁ := Arrow.isIso_of_isIso_left_of_isIso_right c₁
  let r := pairArrowMapOnOpen j j' a b h (⊤ : X'.left.Opens)
  have hr : r ≫ c₁ = c₀ ≫ Arrow.homMk' a b h := pairArrowMapOnOpen_comp j j' a b h ⊤
  have hm : (P).map r ≫ (P).map c₁ = (P).map c₀ ≫ (P).map (Arrow.homMk' a b h) := by
    rw [← (P).map_comp, ← (P).map_comp, hr]
  let : IsIso ((P).map r) := H
  have : IsIso ((P).map c₀ ≫ (P).map (Arrow.homMk' a b h)) := by
    rw [← hm]
    infer_instance
  exact IsIso.of_isIso_comp_left ((P).map c₀) ((P).map (Arrow.homMk' a b h))

/-- The finite-open criterion for the actual restricted relative motive maps.
The local premise applies to all open subsets of each chosen chart. -/
theorem isIso_effectivePairMapOnOpen_finsetSup {ι : Type*} (s : Finset ι)
    (cover : ι → X'.left.Opens)
    (hloc : ∀ i ∈ s, ∀ V ≤ cover i, IsIso (effectivePairMapOnOpen k j j' a b h V)) :
    IsIso (effectivePairMapOnOpen k j j' a b h (s.sup cover)) :=
  predicate_of_finset_sup (fun V => IsIso (effectivePairMapOnOpen k j j' a b h V))
    (isIso_effectivePairMapOnOpen_bot k j j' a b h)
    (isIso_effectivePairMapOnOpen_sup k j j' a b h) s cover hloc

/-- If the target ambient scheme has the indicated finite open cover, its
original relative motive map is an isomorphism by the finite-open criterion. -/
theorem isIso_effectivePairMap_of_finiteOpenCover {ι : Type*} (s : Finset ι)
    (cover : ι → X'.left.Opens) (hc : s.sup cover = ⊤)
    (hloc : ∀ i ∈ s, ∀ V ≤ cover i, IsIso (effectivePairMapOnOpen k j j' a b h V)) :
    IsIso ((P).map (Arrow.homMk' a b h)) := by
  have H := isIso_effectivePairMapOnOpen_finsetSup k j j' a b h s cover hloc
  rw [hc] at H
  exact isIso_effectivePairMap_of_isIso_top k j j' a b h H

/-- It suffices to check smaller members of an intersection-closed class of chart opens. -/
theorem isIso_effectivePairMap_of_finiteOpenCover_of_inf_closed {ι : Type*}
    (Q : X'.left.Opens → Prop) (hQ : ∀ V W, Q V → Q W → Q (V ⊓ W))
    (s : Finset ι) (cover : ι → X'.left.Opens) (hc : s.sup cover = ⊤)
    (hq : ∀ i ∈ s, Q (cover i))
    (hloc : ∀ i ∈ s, ∀ W ≤ cover i, Q W → IsIso (effectivePairMapOnOpen k j j' a b h W)) :
    IsIso ((P).map (Arrow.homMk' a b h)) := by
  have H := predicate_of_finset_sup_of_inf_closed
    (fun V => IsIso (effectivePairMapOnOpen k j j' a b h V)) Q
    (isIso_effectivePairMapOnOpen_bot k j j' a b h)
    (isIso_effectivePairMapOnOpen_sup k j j' a b h) hQ s cover hq hloc
  rw [hc] at H
  exact isIso_effectivePairMap_of_isIso_top k j j' a b h H

end Locality

end AlgebraicGeometry.MotivicHomotopy
