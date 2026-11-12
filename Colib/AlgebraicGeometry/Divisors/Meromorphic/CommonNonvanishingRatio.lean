/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Divisors.Meromorphic.RegularGeneratorRatioBoundary
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator

/-!
# An actual ordinary unit ratio on the common nonvanishing open

The domain and generators are produced from the two original local ordinary sections.
Their actual full-boundary coordinates force this common domain to contain the full boundary.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SectionPowerOpen (nonvanishingOpenOn nonvanishingOpenOn_le)

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose Scheme.Modules
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf

namespace AlgebraicGeometry.Scheme.Modules

variable {X B : Scheme.{u}} (P : X.Modules)
  [hP : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatIsSheaf P]

/-- The original local section, restricted to any open inside its actual nonvanishing open,
is a native generator on every smaller open. -/
def generatorOnLocalNonvanishing (U : X.Opens) (c : Γ(P, U))
    (V : X.Opens) (hV : V ≤ nonvanishingOpenOn P U c) :
    Stacks.SheafOfModules.GeneratorSections X.toRingedSpace P V := by
  let hVU : V ≤ U := hV.trans (nonvanishingOpenOn_le P U c)
  refine ⟨P.presheaf.map (homOfLE hVU).op c, fun W hW => ?_⟩
  have hbij := Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    (X := X.toRingedSpace) P c W (hW.trans hVU) (fun y hy => ?_)
  · have heq : P.val.restrictₛₗ (homOfLE hW).op
        (P.presheaf.map (homOfLE hVU).op c) =
      P.val.map (homOfLE (hW.trans hVU)).op c :=
        (P.val.map_comp_apply (homOfLE hVU).op (homOfLE hW).op c).symm
    change Function.Bijective (fun r : Γ(X, W) =>
      r • (show Γ(P, W) from
        P.val.restrictₛₗ (homOfLE hW).op (P.presheaf.map (homOfLE hVU).op c)))
    exact (congrArg (fun t : Γ(P, W) => Function.Bijective
      (fun r : Γ(X, W) => r • t)) heq).mpr hbij
  · exact fun hh => (hV (hW hy)).2
      ((Stacks.NonvanishingPullback.mem_maximalSmul_iff P y _).mpr hh)

/-- Actual frame coordinate one forces a local ordinary section to be nonvanishing
along every point of the original boundary morphism. -/
theorem top_le_preimage_localNonvanishing_of_frame
    (i : B ⟶ X) (U : X.Opens) (hU : (⊤ : B.Opens) ≤ i ⁻¹ᵁ U) (c : Γ(P, U))
    (τ : (pullback i).obj P ≅ SheafOfModules.unit B.ringCatSheaf)
    (hc : Hom.app τ.hom ⊤ (pullbackSectionHom i P U ⊤ hU c) = (1 : Γ(B, ⊤))) :
    (⊤ : B.Opens) ≤ i ⁻¹ᵁ nonvanishingOpenOn P U c := by
  intro z _
  refine ⟨hU trivial, ?_⟩
  have hpb : z ∈ Stacks.Ample.nonvanishingLocus ((pullback i).obj P)
      (pullbackSectionHom i P U ⊤ hU c) := by
    apply (Stacks.Ample.nonvanishingLocus_congr τ _).subset
    exact Stacks.Ample.Γgerm_notMem_maximalSmul_of_eq_one B z _ hc.symm
  have hg : ((pullback i).obj P).presheaf.germ ⊤ z trivial
      (pullbackSectionHom i P U ⊤ hU c) =
    ((pullback i).obj P).presheaf.germ (i ⁻¹ᵁ U) z (hU trivial)
      (Stacks.RingedSpace.pullbackUnit i.toLRSHom.toShHom P (op U) c) :=
    ((pullback i).obj P).presheaf.germ_res_apply (homOfLE hU) z trivial _
  intro hbad
  have hbad' := (Stacks.NonvanishingLocusRestrict.mem_maximalSmul_germ_pullbackUnit_iff
    i P c z (hU trivial)).mpr hbad
  exact hpb ((Iff.of_eq (congrArg (fun v =>
    v ∈ Stacks.ModuleStalk.maximalSmul ((pullback i).obj P) z) hg)).mpr hbad')

/-- The actual common nonvanishing open of the original denominator and numerator. -/
def commonSectionNonvanishingOpen (Up Uc : X.Opens) (p : Γ(P, Up)) (c : Γ(P, Uc)) : X.Opens :=
  nonvanishingOpenOn P Up p ⊓ nonvanishingOpenOn P Uc c

/-- The unit `c/p` is constructed from the actual restrictions on their common
nonvanishing open, not from a presumed ratio identity. -/
def commonNonvanishingRatioUnit (Up Uc : X.Opens) (p : Γ(P, Up)) (c : Γ(P, Uc)) :
    Γ(X, commonSectionNonvanishingOpen P Up Uc p c)ˣ :=
  Stacks.SheafOfModules.generatorRatioUnit P (commonSectionNonvanishingOpen P Up Uc p c)
    (generatorOnLocalNonvanishing P Up p _ inf_le_left)
    (generatorOnLocalNonvanishing P Uc c _ inf_le_right)

/-- The common nonvanishing open contains the entire original boundary. -/
theorem top_le_preimage_commonSectionNonvanishingOpen
    (i : B ⟶ X) (Up Uc : X.Opens)
    (hUp : (⊤ : B.Opens) ≤ i ⁻¹ᵁ Up) (hUc : (⊤ : B.Opens) ≤ i ⁻¹ᵁ Uc)
    (p : Γ(P, Up)) (c : Γ(P, Uc))
    (τ : (pullback i).obj P ≅ SheafOfModules.unit B.ringCatSheaf)
    (hp : Hom.app τ.hom ⊤ (pullbackSectionHom i P Up ⊤ hUp p) = (1 : Γ(B, ⊤)))
    (hc : Hom.app τ.hom ⊤ (pullbackSectionHom i P Uc ⊤ hUc c) = (1 : Γ(B, ⊤))) :
    (⊤ : B.Opens) ≤ i ⁻¹ᵁ commonSectionNonvanishingOpen P Up Uc p c :=
  fun _ hz => ⟨top_le_preimage_localNonvanishing_of_frame P i Up hUp p τ hp hz,
    top_le_preimage_localNonvanishing_of_frame P i Uc hUc c τ hc hz⟩

/-- The actual ordinary unit on the produced common open restricts to one on the full
boundary, including its nilpotents. -/
@[colib_tag "COL-1063",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/SectionPowerOpen.lean:204-214"
    "ingredient" "The actual nonvanishing open of each unchanged local section",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/InvertiblePullbackFlat/SectionGenerator.lean:300-322"
    "ingredient" "Local stalk nonvanishing produces actual generators on the entire open",
  colib_ref "axiom_stacks_5ed82d14"
    "AlgebraicGeometry/Divisors/NonvanishingLocusRestrict.lean:173-198"
    "ingredient" "Actual local section pullback detects nonvanishing on the full boundary"]
theorem appLE_commonNonvanishingRatioUnit_eq_one
    (i : B ⟶ X) (Up Uc : X.Opens)
    (hUp : (⊤ : B.Opens) ≤ i ⁻¹ᵁ Up) (hUc : (⊤ : B.Opens) ≤ i ⁻¹ᵁ Uc)
    (p : Γ(P, Up)) (c : Γ(P, Uc))
    (τ : (pullback i).obj P ≅ SheafOfModules.unit B.ringCatSheaf)
    (hp : Hom.app τ.hom ⊤ (pullbackSectionHom i P Up ⊤ hUp p) = (1 : Γ(B, ⊤)))
    (hc : Hom.app τ.hom ⊤ (pullbackSectionHom i P Uc ⊤ hUc c) = (1 : Γ(B, ⊤))) :
    i.appLE _ ⊤ (top_le_preimage_commonSectionNonvanishingOpen P i Up Uc hUp hUc p c τ hp hc)
      (commonNonvanishingRatioUnit P Up Uc p c).val = (1 : Γ(B, ⊤)) := by
  apply appLE_generatorRatioUnit_eq_one i P _ _ _ _ τ
  · exact (congrArg (Hom.app τ.hom ⊤) (pullbackSectionHom_map i P Up _
      (inf_le_left.trans (nonvanishingOpenOn_le P Up p)) ⊤ _ hUp p)).trans hp
  · exact (congrArg (Hom.app τ.hom ⊤) (pullbackSectionHom_map i P Uc _
      (inf_le_right.trans (nonvanishingOpenOn_le P Uc c)) ⊤ _ hUc c)).trans hc

end AlgebraicGeometry.Scheme.Modules
