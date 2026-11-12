/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.CommonNonvanishingRatio
public import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularGeneratorRatioGeneric

/-!
# Ordinary full-boundary representatives of the exact native meromorphic ratio

The common open, its density, both generators, and the unit are all produced from the
original ordinary representatives. Integrality is needed only for generic comparison.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open Stacks.SectionPowerOpen (nonvanishingOpenOn nonvanishingOpenOn_le)

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry

variable {X B : Scheme.{u}} [IsIntegral X] (P : X.Modules)
  [hP : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf P]

local instance commonRatioGenericInvertible :
    SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property P :=
  hP.toAlgebraicGeometry

local instance commonRatioGenericQC : P.IsQuasicoherent :=
  isQuasicoherent_of_isInvertible P

/-- A local representative of a regular meromorphic section does not vanish at the
original generic point. -/
theorem genericPoint_mem_localNonvanishing_of_regularMeromorphic
    (U : X.Opens) (hU : genericPoint X ∈ U) (c : Γ(P, U))
    (s : MeromorphicSection X.sheaf P) (hs : IsRegularMeromorphicSection X.sheaf P s)
    (hc : meromorphicGenericValue X P s = P.presheaf.germ U (genericPoint X) hU c) :
    genericPoint X ∈ nonvanishingOpenOn P U c := by
  refine ⟨hU, ?_⟩
  have hmax : IsLocalRing.maximalIdeal (X.presheaf.stalk (genericPoint X)) = ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField X.functionField)
  have hbot : Stacks.ModuleStalk.maximalSmul P (genericPoint X) = ⊥ := by
    rw [Stacks.ModuleStalk.maximalSmul, hmax, Submodule.bot_smul]
  intro hz
  have hz' : P.presheaf.germ U (genericPoint X) hU c = 0 := by
    simpa only [hbot, Submodule.mem_bot] using hz
  exact ne_zero_of_isRegularMeromorphicSection P s hs
    (constantGenericStalkModuleSection_meromorphicGenericValue X P s) (hc.trans hz')

/-- The produced common nonvanishing open of two regular meromorphic representatives
contains the original generic point. -/
theorem genericPoint_mem_commonSectionNonvanishingOpen
    (Up Uc : X.Opens) (hUp : genericPoint X ∈ Up) (hUc : genericPoint X ∈ Uc)
    (p : Γ(P, Up)) (c : Γ(P, Uc)) (s t : MeromorphicSection X.sheaf P)
    (hs : IsRegularMeromorphicSection X.sheaf P s)
    (ht : IsRegularMeromorphicSection X.sheaf P t)
    (hc : meromorphicGenericValue X P s = P.presheaf.germ Uc (genericPoint X) hUc c)
    (hp : meromorphicGenericValue X P t = P.presheaf.germ Up (genericPoint X) hUp p) :
    genericPoint X ∈ commonSectionNonvanishingOpen P Up Uc p c :=
  ⟨genericPoint_mem_localNonvanishing_of_regularMeromorphic P Up hUp p t ht hp,
    genericPoint_mem_localNonvanishing_of_regularMeromorphic P Uc hUc c s hs hc⟩

/-- The native meromorphic ratio has an actual ordinary unit representative on a
produced dense open containing the entire original boundary, and that unit restricts to one. -/
@[colib_tag "COL-1063"]
theorem exists_denseOpen_unit_eq_meromorphicSectionRatio_boundary_one
    (i : B ⟶ X) (Up Uc : X.Opens)
    (hUp : genericPoint X ∈ Up) (hUc : genericPoint X ∈ Uc)
    (hBUp : (⊤ : B.Opens) ≤ i ⁻¹ᵁ Up) (hBUc : (⊤ : B.Opens) ≤ i ⁻¹ᵁ Uc)
    (p : Γ(P, Up)) (c : Γ(P, Uc)) (s t : MeromorphicSection X.sheaf P)
    (hs : IsRegularMeromorphicSection X.sheaf P s)
    (ht : IsRegularMeromorphicSection X.sheaf P t)
    (hc : meromorphicGenericValue X P s = P.presheaf.germ Uc (genericPoint X) hUc c)
    (hp : meromorphicGenericValue X P t = P.presheaf.germ Up (genericPoint X) hUp p)
    (τ : (pullback i).obj P ≅ SheafOfModules.unit B.ringCatSheaf)
    (hpB : Hom.app τ.hom ⊤ (pullbackSectionHom i P Up ⊤ hBUp p) = (1 : Γ(B, ⊤)))
    (hcB : Hom.app τ.hom ⊤ (pullbackSectionHom i P Uc ⊤ hBUc c) = (1 : Γ(B, ⊤))) :
    ∃ (W : Stacks.Chow.DenseOpen X) (u : Γ(X, W.val)ˣ)
      (hBW : (⊤ : B.Opens) ≤ i ⁻¹ᵁ W.val),
      W.val = commonSectionNonvanishingOpen P Up Uc p c ∧
      Units.map (Stacks.Chow.ofSectionRingHom X W).toMonoidHom u =
        meromorphicSectionRatio X P s t hs ht ∧
      i.appLE W.val ⊤ hBW u.val = (1 : Γ(B, ⊤)) := by
  have hη := genericPoint_mem_commonSectionNonvanishingOpen P Up Uc hUp hUc p c s t
    hs ht hc hp
  let W : Stacks.Chow.DenseOpen X := ⟨commonSectionNonvanishingOpen P Up Uc p c,
    (commonSectionNonvanishingOpen P Up Uc p c).isOpen.dense ⟨genericPoint X, hη⟩⟩
  refine ⟨W, commonNonvanishingRatioUnit P Up Uc p c,
    top_le_preimage_commonSectionNonvanishingOpen P i Up Uc hBUp hBUc p c τ hpB hcB,
    rfl, ?_, appLE_commonNonvanishingRatioUnit_eq_one P i Up Uc hBUp hBUc p c τ hpB hcB⟩
  apply rationalGeneratorRatioUnit_eq_meromorphicSectionRatio X P W hη
    (generatorOnLocalNonvanishing P Up p _ inf_le_left)
    (generatorOnLocalNonvanishing P Uc c _ inf_le_right) s t hs ht
  · exact hc.trans (P.presheaf.germ_res_apply
      (homOfLE (inf_le_right.trans (nonvanishingOpenOn_le P Uc c)))
      (genericPoint X) hη c).symm
  · exact hp.trans (P.presheaf.germ_res_apply
      (homOfLE (inf_le_left.trans (nonvanishingOpenOn_le P Up p)))
      (genericPoint X) hη p).symm

end AlgebraicGeometry
