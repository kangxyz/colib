/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.Basic
public import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.TransferTriangle
import Colib.AlgebraicGeometry.MotivicHomotopy.EffectiveMotives.Pairs.OpenImmersion
import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower

/-!
# Relative motives of nested opens

For nested opens the three original transfer quotients form the standard
short exact sequence for the cokernels of a composite. The boundary is the
connecting map of this short exact sequence followed by effective reflection.
Both quotient maps are induced by the actual maps of pairs.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry.Scheme

universe u w w'

namespace AlgebraicGeometry.MotivicHomotopy

open SheafWithTransfers

attribute [local irreducible] Cor.graphFunctor transferRepresentable

variable (k : Type u) [Field k]

local notation "Sm(" field ")" => SmoothSite (Spec (CommRingCat.of field))
local notation "NST(" field ")" => LargeSheaves field
local notation "R" => smoothTransferRepresentable k

/-- Use the native abelian structure for the three original transfer quotients. -/
local instance instAbelianNestedPair : Abelian (LargeSheaves k) :=
  SheafWithTransfers.abelian k

/-- The first map of pairs for `U ⊆ V ⊆ X`, induced by `V ⟶ X`. -/
def nestedPairFirstSquare {U V X : Sm(k)} (i : U ⟶ V) (j : V ⟶ X) : Square Sm(k) where
  f₁₂ := 𝟙 U
  f₁₃ := i
  f₂₄ := i ≫ j
  f₃₄ := j
  fac := Category.id_comp _

/-- The second map of pairs for `U ⊆ V ⊆ X`, induced by `U ⟶ V`. -/
def nestedPairSecondSquare {U V X : Sm(k)} (i : U ⟶ V) (j : V ⟶ X) : Square Sm(k) where
  f₁₂ := i
  f₁₃ := i ≫ j
  f₂₄ := j
  f₃₄ := 𝟙 X
  fac := (Category.comp_id _).symm

section Transfer

variable {U V X : Sm(k)} (i : U ⟶ V) (j : V ⟶ X)

/-- The composite transfer quotient is identified with the quotient of the composite open. -/
def nestedThirdQuotientIso :
    cokernel ((R).map i ≫ (R).map j) ≅ transferPairCokernel k (i ≫ j) :=
  cokernelIsoOfEq ((R).map_comp i j).symm

private def nestedPairCokernelCompSequence : ShortComplex NST(k) :=
  let f := (R).map i
  let g := (R).map j
  let e := nestedThirdQuotientIso k i j
  ShortComplex.mk (Stacks.Abelian.cokernelCompι f g ≫ e.hom)
    (e.inv ≫ Stacks.Abelian.cokernelCompπ f g) (by
      rw [Category.assoc, Iso.hom_inv_id_assoc, Stacks.Abelian.cokernelCompι_comp_cokernelCompπ])

private def nestedPairCokernelCompSequenceIso :
    Stacks.Abelian.cokernelCompShortComplex ((R).map i) ((R).map j) ≅
      nestedPairCokernelCompSequence k i j := by
  let f := (R).map i
  let g := (R).map j
  let A := Stacks.Abelian.cokernelCompShortComplex f g
  let B := nestedPairCokernelCompSequence k i j
  let e : A.X₂ ≅ B.X₂ := nestedThirdQuotientIso k i j
  refine ShortComplex.isoMk (Iso.refl A.X₁ : A.X₁ ≅ B.X₁) e
    (Iso.refl A.X₃ : A.X₃ ≅ B.X₃) ?_ ?_
  · change 𝟙 (cokernel f) ≫ (Stacks.Abelian.cokernelCompι f g ≫ e.hom) =
      Stacks.Abelian.cokernelCompι f g ≫ e.hom
    exact Category.id_comp _
  · change e.hom ≫ e.inv ≫ Stacks.Abelian.cokernelCompπ f g =
      Stacks.Abelian.cokernelCompπ f g ≫ 𝟙 (cokernel g)
    let π : A.X₂ ⟶ A.X₃ := A.g
    exact (e.hom_inv_id_assoc π).trans (Category.comp_id π).symm

private theorem nestedPairCokernelCompSequence_shortExact
    [IsOpenImmersion i.left] [IsOpenImmersion j.left] :
    (nestedPairCokernelCompSequence k i j).ShortExact := by
  let : Mono ((R).map i) := mono_transferRepresentable_map_openImmersion k i
  let : Mono ((R).map j) := mono_transferRepresentable_map_openImmersion k j
  exact ShortComplex.shortExact_of_iso (nestedPairCokernelCompSequenceIso k i j)
    (Stacks.Abelian.cokernelCompShortComplex_shortExact ((R).map i) ((R).map j))

set_option maxHeartbeats 650000 in
-- The quotient comparison elaborates across two presentations of the same cokernel.
private theorem nestedPairCokernelCompSequence_f :
    (nestedPairCokernelCompSequence k i j).f =
      (transferPairCokernelFunctor k).map
        (Arrow.homMk' (𝟙 U) j (Category.id_comp _) :
          Arrow.mk i ⟶ Arrow.mk (i ≫ j)) := by
  let f := (R).map i
  let g := (R).map j
  let p := transferPairProjection k
  let α : Arrow.mk i ⟶ Arrow.mk (i ≫ j) := Arrow.homMk' (𝟙 U) j (Category.id_comp _)
  let e := nestedThirdQuotientIso k i j
  have h : g ≫ p.app (Arrow.mk (i ≫ j)) =
      p.app (Arrow.mk i) ≫ (transferPairCokernelFunctor k).map α :=
    p.naturality α
  apply (cancel_epi (cokernel.π f)).mp
  change cokernel.π f ≫ (Stacks.Abelian.cokernelCompι f g ≫ e.hom) = _
  rw [Stacks.Abelian.π_comp_cokernelCompι_assoc]
  have hπ : cokernel.π (f ≫ g) ≫ e.hom = p.app (Arrow.mk (i ≫ j)) :=
    π_comp_cokernelIsoOfEq_hom ((R).map_comp i j).symm
  exact (congrArg (g ≫ ·) hπ).trans h

set_option maxHeartbeats 650000 in
-- The quotient comparison elaborates across two presentations of the same cokernel.
private theorem nestedPairCokernelCompSequence_g :
    (nestedPairCokernelCompSequence k i j).g =
      (transferPairCokernelFunctor k).map
        (Arrow.homMk' i (𝟙 X) (Category.comp_id _).symm :
          Arrow.mk (i ≫ j) ⟶ Arrow.mk j) := by
  let f := (R).map i
  let g := (R).map j
  let p := transferPairProjection k
  let β : Arrow.mk (i ≫ j) ⟶ Arrow.mk j := Arrow.homMk' i (𝟙 X) (Category.comp_id _).symm
  let e := nestedThirdQuotientIso k i j
  have h : (R).map (𝟙 X) ≫ p.app (Arrow.mk j) =
      p.app (Arrow.mk (i ≫ j)) ≫ (transferPairCokernelFunctor k).map β :=
    p.naturality β
  let p₀ := p.app (Arrow.mk (i ≫ j))
  let π := Stacks.Abelian.cokernelCompπ f g
  have hπ : p₀ ≫ e.inv = cokernel.π (f ≫ g) :=
    π_comp_cokernelIsoOfEq_inv ((R).map_comp i j).symm
  let : Epi p₀ := inferInstanceAs (Epi (cokernel.π ((R).map (i ≫ j))))
  apply (cancel_epi p₀).mp
  rw [(R).map_id, Category.id_comp] at h
  have hπ' : cokernel.π (f ≫ g) ≫ π = p.app (Arrow.mk j) :=
    Stacks.Abelian.π_comp_cokernelCompπ f g
  exact (Category.assoc p₀ e.inv π).symm.trans
    ((congrArg (· ≫ π) hπ).trans (hπ'.trans h))

/-- The corresponding map between original arrows. -/
abbrev nestedPairFirstArrow :
    Arrow.mk i ⟶ Arrow.mk (i ≫ j) := Arrow.homMk' (𝟙 U) j (Category.id_comp _)

/-- The corresponding map between original arrows. -/
abbrev nestedPairSecondArrow :
    Arrow.mk (i ≫ j) ⟶ Arrow.mk j := Arrow.homMk' i (𝟙 X) (Category.comp_id _).symm

/-- The two original nested quotient maps compose to zero. -/
theorem nestedPairTransferSequence_zero :
    (transferPairCokernelFunctor k).map (nestedPairFirstArrow k i j) ≫
      (transferPairCokernelFunctor k).map (nestedPairSecondArrow k i j) = 0 := by
  have h := (nestedPairCokernelCompSequence k i j).zero
  exact (congrArg₂ (· ≫ ·) (nestedPairCokernelCompSequence_f k i j).symm
    (nestedPairCokernelCompSequence_g k i j).symm).trans h

/-- The actual quotient sequence on the maps of nested pairs. -/
def nestedPairTransferSequence : ShortComplex NST(k) :=
  ShortComplex.mk ((transferPairCokernelFunctor k).map (nestedPairFirstArrow k i j))
    ((transferPairCokernelFunctor k).map (nestedPairSecondArrow k i j))
    (nestedPairTransferSequence_zero k i j)

/-- The two maps of the transfer quotient sequence use the original arrow functor. -/
theorem nestedPairTransferSequence_f :
    (nestedPairTransferSequence k i j).f =
      (transferPairCokernelFunctor k).map
        (Arrow.homMk' (𝟙 U) j (Category.id_comp _) :
          Arrow.mk i ⟶ Arrow.mk (i ≫ j)) := rfl

/-- The second transfer quotient map uses the original inclusions of opens. -/
theorem nestedPairTransferSequence_g :
    (nestedPairTransferSequence k i j).g =
      (transferPairCokernelFunctor k).map
        (Arrow.homMk' i (𝟙 X) (Category.comp_id _).symm :
          Arrow.mk (i ≫ j) ⟶ Arrow.mk j) := rfl

private theorem shortExact_mk_of_eq {C : Type*} [Category* C] [HasZeroMorphisms C]
    {A B D : C} {f f' : A ⟶ B} {g g' : B ⟶ D}
    {h : f ≫ g = 0} {h' : f' ≫ g' = 0}
    (hf : f = f') (hg : g = g') (hs : (ShortComplex.mk f g h).ShortExact) :
    (ShortComplex.mk f' g' h').ShortExact := by
  subst f'
  subst g'
  exact hs

set_option maxHeartbeats 900000 in
-- Transport exactness through the two identified maps on the literal quotients.
/-- The original signed transfer quotients of three nested opens form a short exact sequence. -/
theorem nestedPairTransferSequence_shortExact [IsOpenImmersion i.left] [IsOpenImmersion j.left] :
    (nestedPairTransferSequence k i j).ShortExact := by
  unfold nestedPairTransferSequence
  exact shortExact_mk_of_eq (nestedPairCokernelCompSequence_f k i j)
    (nestedPairCokernelCompSequence_g k i j) (nestedPairCokernelCompSequence_shortExact k i j)

variable {U' V' X' : Sm(k)} {i' : U' ⟶ V'} {j' : V' ⟶ X'}

private def nestedPairTransferSequenceMapOfSquares
    (α : Arrow.mk i ⟶ Arrow.mk i')
    (β : Arrow.mk (i ≫ j) ⟶ Arrow.mk (i' ≫ j'))
    (γ : Arrow.mk j ⟶ Arrow.mk j')
    (h₁ : α ≫ nestedPairFirstArrow k i' j' = nestedPairFirstArrow k i j ≫ β)
    (h₂ : β ≫ nestedPairSecondArrow k i' j' = nestedPairSecondArrow k i j ≫ γ) :
    nestedPairTransferSequence k i j ⟶ nestedPairTransferSequence k i' j' := by
  let P := transferPairCokernelFunctor k
  let f := nestedPairFirstArrow k i j
  let f' := nestedPairFirstArrow k i' j'
  let g := nestedPairSecondArrow k i j
  let g' := nestedPairSecondArrow k i' j'
  have e₁ : P.map α ≫ P.map f' = P.map f ≫ P.map β :=
    ((P.map_comp α f').symm.trans (P.congr_map h₁)).trans (P.map_comp f β)
  have e₂ : P.map β ≫ P.map g' = P.map g ≫ P.map γ :=
    ((P.map_comp β g').symm.trans (P.congr_map h₂)).trans (P.map_comp g γ)
  exact ShortComplex.homMk (P.map α) (P.map β) (P.map γ) e₁ e₂

set_option maxHeartbeats 600000 in
-- The two naturality identities already hold in the category of smooth pairs.
/-- The original three quotient maps for a commuting diagram of nested opens. -/
@[no_expose]
def nestedPairTransferSequenceMap (a : U ⟶ U') (b : V ⟶ V') (c : X ⟶ X')
    (hi : i ≫ b = a ≫ i') (hj : j ≫ c = b ≫ j') :
    nestedPairTransferSequence k i j ⟶ nestedPairTransferSequence k i' j' := by
  let α : Arrow.mk i ⟶ Arrow.mk i' := Arrow.homMk' a b hi.symm
  let β : Arrow.mk (i ≫ j) ⟶ Arrow.mk (i' ≫ j') := Arrow.homMk' a c
    (by
      calc
        a ≫ (i' ≫ j') = (a ≫ i') ≫ j' := (Category.assoc _ _ _).symm
        _ = (i ≫ b) ≫ j' := congrArg (· ≫ j') hi.symm
        _ = i ≫ (b ≫ j') := Category.assoc _ _ _
        _ = i ≫ (j ≫ c) := congrArg (i ≫ ·) hj.symm
        _ = (i ≫ j) ≫ c := (Category.assoc _ _ _).symm)
  let γ : Arrow.mk j ⟶ Arrow.mk j' := Arrow.homMk' b c hj.symm
  have h₁ : α ≫ nestedPairFirstArrow k i' j' = nestedPairFirstArrow k i j ≫ β := by
    apply Arrow.hom_ext
    · exact (Category.comp_id a).trans (Category.id_comp a).symm
    · exact hj.symm
  have h₂ : β ≫ nestedPairSecondArrow k i' j' = nestedPairSecondArrow k i j ≫ γ := by
    apply Arrow.hom_ext
    · exact hi.symm
    · exact (Category.comp_id c).trans (Category.id_comp c).symm
  exact nestedPairTransferSequenceMapOfSquares k i j α β γ h₁ h₂

end Transfer

section Effective

variable [PerfectField k]
  [HasDerivedCategory.{w} (PresheafWithTransfers.{u + 1} k)]
  [HasDerivedCategory.{w'} NST(k)]
  [HasExt.{u + 1} (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

variable {U V X : Sm(k)} (i : U ⟶ V) (j : V ⟶ X)
  [IsOpenImmersion i.left] [IsOpenImmersion j.left]

/-- The distinguished triangle of the three actual relative motives for nested opens.
Its boundary is induced by the transfer short exact sequence with positive quotient maps. -/
abbrev effectiveNestedPairTriangle : Triangle (EffectiveMotivesMinus k) :=
  effectiveTransferSheafTriangle k (nestedPairTransferSequence_shortExact k i j)

/-- The connecting arrow for the actual nested opens, typed in the original pair objects. -/
abbrev effectiveNestedPairBoundary :
    effectivePairMotive k j ⟶ (effectivePairMotive k i)⟦(1 : ℤ)⟧ :=
  (effectiveNestedPairTriangle k i j).mor₃

set_option maxHeartbeats 750000 in
-- The triangle and the pair functor share the underlying transfer quotient.
/-- The first triangle arrow is the original map induced by the ambient inclusion. -/
theorem effectiveNestedPairTriangle_mor₁ :
    (effectiveNestedPairTriangle k i j).mor₁ =
      effectivePairMotiveMap k (nestedPairFirstSquare k i j) :=
  (effectiveTransferSheaf k).congr_map (nestedPairTransferSequence_f k i j)

set_option maxHeartbeats 750000 in
-- The triangle and the pair functor share the underlying transfer quotient.
/-- The second triangle arrow is the original map induced by inclusion of the open pieces. -/
theorem effectiveNestedPairTriangle_mor₂ :
    (effectiveNestedPairTriangle k i j).mor₂ =
      effectivePairMotiveMap k (nestedPairSecondSquare k i j) :=
  (effectiveTransferSheaf k).congr_map (nestedPairTransferSequence_g k i j)

/-- The triangle of actual pair maps for three nested opens is distinguished. -/
theorem effectiveNestedPairTriangle_distinguished :
    effectiveNestedPairTriangle k i j ∈ distTriang _ :=
  effectiveTransferSheafTriangle_distinguished k (nestedPairTransferSequence_shortExact k i j)

/-- A commuting diagram of nested opens induces a morphism of their relative triangles. -/
@[no_expose]
def effectiveNestedPairTriangleMap {U' V' X' : Sm(k)} (i' : U' ⟶ V') (j' : V' ⟶ X')
    [IsOpenImmersion i'.left] [IsOpenImmersion j'.left]
    (a : U ⟶ U') (b : V ⟶ V') (c : X ⟶ X')
    (hi : i ≫ b = a ≫ i') (hj : j ≫ c = b ≫ j') :
    effectiveNestedPairTriangle k i j ⟶ effectiveNestedPairTriangle k i' j' :=
  effectiveTransferSheafTriangleMap k (nestedPairTransferSequence_shortExact k i j)
    (nestedPairTransferSequence_shortExact k i' j')
    (nestedPairTransferSequenceMap k i j a b c hi hj)

set_option maxHeartbeats 550000 in
-- Use the two literal components of the map of effective triangles.
/-- The positive nested-open boundary is natural for the original maps of all three quotients. -/
theorem effectiveNestedPairBoundary_naturality {U' V' X' : Sm(k)}
    (i' : U' ⟶ V') (j' : V' ⟶ X')
    [IsOpenImmersion i'.left] [IsOpenImmersion j'.left]
    (a : U ⟶ U') (b : V ⟶ V') (c : X ⟶ X')
    (hi : i ≫ b = a ≫ i') (hj : j ≫ c = b ≫ j') :
    (effectivePairMotiveFunctor k).map (Arrow.homMk' b c hj.symm) ≫
      effectiveNestedPairBoundary k i' j' =
        effectiveNestedPairBoundary k i j ≫
          ((effectivePairMotiveFunctor k).map (Arrow.homMk' a b hi.symm))⟦(1 : ℤ)⟧' := by
  let M := effectiveNestedPairTriangleMap k i j i' j' a b c hi hj
  let F := effectivePairMotiveFunctor k
  let S := shiftFunctor (EffectiveMotivesMinus k) (1 : ℤ)
  have h₁ : M.hom₁ = F.map (Arrow.homMk' a b hi.symm) := rfl
  have h₃ : M.hom₃ = F.map (Arrow.homMk' b c hj.symm) := rfl
  change F.map (Arrow.homMk' b c hj.symm) ≫ _ =
    _ ≫ S.map (F.map (Arrow.homMk' a b hi.symm))
  rw [← h₃, ← h₁]
  exact M.comm₃.symm

end Effective

end AlgebraicGeometry.MotivicHomotopy
