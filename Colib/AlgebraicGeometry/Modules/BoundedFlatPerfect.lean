/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Modules.PerfectJoint
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatRetract
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk

/-!
# Bounded Above Flat Perfect Complexes

These are native perfect sheaf complexes with an upper bound on their terms and flat terms.
There is no lower term bound, local freeness or quasicoherence assumption on the terms.
Native Stacks Tag 05NE identifies the flatness condition with flatness of every stalk.
The full subcategory keeps the original complexes and chain maps.

Adapted from `Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Basic.lean`
at `c561118b7795eb9780be9ed391c3251d6a4d0afd`, using native Stacks perfectness and flatness.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open AlgebraicGeometry StrictlyPerfect
open scoped ZeroObject

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-- Perfect complexes with a global upper term bound and flat sheaves in every degree. -/
@[colib_tag "COL-0323", stacks 05NE "The flat terms are exactly stalkwise-flat sheaves",
  colib_ref "quillen"
    "Quillen/Aglib/AlgebraicGeometry/Modules/PerfectComplexes/BoundedFlat/Basic.lean:41-47"
    "adaptation" "The original bounded-above flat local-perfect object class on native sheaves"]
def boundedAboveFlatPerfectComplex (X : RingedSpace.{u, u}) :
    ObjectProperty (CochainComplex (OXMod.{u, u, u} X) ℤ) := fun K =>
  IsPerfectComplex K ∧ (∃ b : ℤ, K.IsStrictlyLE b) ∧
    ∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) (K.X n)

/-- Every zero sheaf is flat, as a retract of its native flat cover. -/
theorem isFlat_of_isZero (M : OXMod.{u, u, u} X) (hM : IsZero M) :
    AlgebraicGeometry.SheafOfModules.IsFlat (O := X.sheaf) M := by
  obtain ⟨N, p, hN, -⟩ := Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat X.sheaf M
  exact Stacks.SheafOfModules.FlatRetract.isFlat_of_retract X.sheaf
    (hM.to_ N) p (hM.eq_of_src _ _) hN

/-- Zero complexes have an upper term bound and flat perfect terms. -/
theorem boundedAboveFlatPerfectComplex_of_isZero
    {K : CochainComplex (OXMod.{u, u, u} X) ℤ} (hK : IsZero K) :
    boundedAboveFlatPerfectComplex X K := by
  have hz (n : ℤ) := (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).map_isZero hK
  exact ⟨isPerfectComplex_of_forall_isZero hz,
    ⟨0, (K.isStrictlyLE_iff 0).2 (fun n _ => hz n)⟩,
    fun n => isFlat_of_isZero _ (hz n)⟩

instance boundedAboveFlatPerfectComplex_containsZero :
    (boundedAboveFlatPerfectComplex X).ContainsZero where
  exists_zero := ⟨0, isZero_zero _, boundedAboveFlatPerfectComplex_of_isZero (isZero_zero _)⟩

/-- Actual chain isomorphisms preserve the upper bound, flat terms and perfectness. -/
theorem boundedAboveFlatPerfectComplex_of_iso
    {K L : CochainComplex (OXMod.{u, u, u} X) ℤ} (e : K ≅ L)
    (hK : boundedAboveFlatPerfectComplex X K) : boundedAboveFlatPerfectComplex X L := by
  obtain ⟨hp, ⟨b, hb⟩, hf⟩ := hK
  let en (n : ℤ) := (HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso e
  refine ⟨hp.of_iso e, ⟨b, (L.isStrictlyLE_iff b).2 ?_⟩, fun n => ?_⟩
  · intro n hn
    exact (K.isZero_of_isStrictlyLE b n hn).of_iso (en n).symm
  · exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso X.sheaf (en n) (hf n)

instance boundedAboveFlatPerfectComplex_closedUnderIsomorphisms :
    (boundedAboveFlatPerfectComplex X).IsClosedUnderIsomorphisms where
  of_iso := boundedAboveFlatPerfectComplex_of_iso

set_option maxHeartbeats 800000 in
-- Degreewise exactness and sheaf-flatness instance synthesis need a larger search budget.
/-- Arbitrary short exact extensions preserve the actual bounded-above flat perfect class. -/
@[stacks 03EY "Flat middle terms in degreewise short exact sequences"]
theorem boundedAboveFlatPerfectComplex_of_shortExact
    {S : ShortComplex (CochainComplex (OXMod.{u, u, u} X) ℤ)} (hS : S.ShortExact)
    (h₁ : boundedAboveFlatPerfectComplex X S.X₁)
    (h₃ : boundedAboveFlatPerfectComplex X S.X₃) : boundedAboveFlatPerfectComplex X S.X₂ := by
  obtain ⟨hp₁, ⟨b, hb⟩, hf₁⟩ := h₁
  obtain ⟨hp₃, ⟨c, hc⟩, hf₃⟩ := h₃
  have hs (n : ℤ) := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS n
  refine ⟨isPerfectComplex_X₂_of_shortExact X hS hp₁ hp₃,
    ⟨max b c, (S.X₂.isStrictlyLE_iff _).2 ?_⟩, fun n => ?_⟩
  · intro n hn
    have h₁ := S.X₁.isZero_of_isStrictlyLE b n (by omega)
    have h₃ := S.X₃.isZero_of_isStrictlyLE c n (by omega)
    exact (hs n).exact.isZero_X₂ (h₁.eq_of_src _ _) (h₃.eq_of_tgt _ _)
  · let E : CochainComplex (OXMod.{u, u, u} X) ℤ ⥤ OXMod.{u, u, u} X :=
      HomologicalComplex.eval _ (.up ℤ) n
    let : E.PreservesZeroMorphisms := { map_zero := by intros; rfl }
    let Sn : ShortComplex (OXMod.{u, u, u} X) := S.map E
    have hSn : Sn.ShortExact := hs n
    exact Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_middle_of_shortExact
      X.sheaf Sn hSn (hf₁ n) (hf₃ n)

instance boundedAboveFlatPerfectComplex_extensionClosed :
    (abelianExactStructure (CochainComplex (OXMod.{u, u, u} X) ℤ)).IsExtensionClosed
      (boundedAboveFlatPerfectComplex X) where
  prop_middle := boundedAboveFlatPerfectComplex_of_shortExact

instance boundedAboveFlatPerfectComplex_closedUnderFiniteProducts :
    (boundedAboveFlatPerfectComplex X).IsClosedUnderFiniteProducts :=
  (abelianExactStructure _).extensionClosed_finiteProducts (boundedAboveFlatPerfectComplex X)

/-- The literal inclusion into all native perfect complexes retains every chain map. -/
def boundedAboveFlatPerfectInclusion (X : RingedSpace.{u, u}) :
    (boundedAboveFlatPerfectComplex X).FullSubcategory ⥤
      ObjectProperty.FullSubcategory (IsPerfectComplex (X := X)) :=
  ObjectProperty.ιOfLE (fun _ h => h.1)

@[simp]
theorem boundedAboveFlatPerfectInclusion_obj
    (K : (boundedAboveFlatPerfectComplex X).FullSubcategory) :
    ((boundedAboveFlatPerfectInclusion X).obj K).obj = K.obj := rfl

@[simp]
theorem boundedAboveFlatPerfectInclusion_map
    {K L : (boundedAboveFlatPerfectComplex X).FullSubcategory} (f : K ⟶ L) :
    ((boundedAboveFlatPerfectInclusion X).map f).hom = f.hom := rfl

end AlgebraicGeometry.RingedSpace
