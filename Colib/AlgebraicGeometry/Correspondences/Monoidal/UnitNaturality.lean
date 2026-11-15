/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Category
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.GraphTransport
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Parameter
import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction

/-!
# Naturality of the graph right unitor

On each prime, the chosen parameter product with the base projects
isomorphically to the original support. The graph of the first projection
therefore transports its whole native cycle to the original prime.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Stacks.Chow
open AlgebraicGeometry.Scheme MonoidalCategory Function.locallyFinsuppWithin

universe u

namespace AlgebraicGeometry.Cor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]

local notation "S" => Spec (CommRingCat.of k)
local notation "B" => SmoothSite.base S

private instance baseGeometricallyIntegral : GeometricallyIntegral (B).hom := by
  change GeometricallyIntegral (𝟙 S)
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ y => ?_⟩
  exact IsIntegral.of_isIso (inv (pullback.snd (𝟙 S) y))

private theorem rightUnitor_left (X : SmoothSite S) :
    (ρ_ X).hom.left = pullback.fst X.hom (B).hom :=
  congrArg (fun f => f.left) (CartesianMonoidalCategory.rightUnitor_hom X)

attribute [local instance] Classical.decEq

private theorem pushforward_nativeExteriorPrime_base (X Y : SmoothSite S)
    (z : pullback (C := Scheme) X.hom Y.hom) (hz : IsFiniteCorrespondencePoint X.hom Y.hom z) :
    letI : IsIso (SmoothSite.productMap (ρ_ X).hom (ρ_ Y).hom).left :=
      productMap_left_isIso (ρ_ X).hom (ρ_ Y).hom
    finiteCyclePushforward (SmoothSite.productMap (ρ_ X).hom (ρ_ Y).hom).left
        (nativeExteriorPrime X Y B z hz).val = single z 1 := by
  let A := integralComponentAt z
  let : IsFinite (exteriorSupportSourceProjection X Y A) := hz.1
  let : IsIntegral A.subscheme := isIntegral_integralComponentAt z
  let : IsNoetherian A.subscheme := Scheme.isNoetherian_of_finiteType_of_isNoetherian
    (exteriorSupportSourceProjection X Y A)
  let : IsNoetherian (exteriorIdentitySupport X Y B A) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (exteriorIdentitySource X Y B A)
  let p := (SmoothSite.productMap (ρ_ X).hom (ρ_ Y).hom).left
  let : IsIso p := productMap_left_isIso (ρ_ X).hom (ρ_ Y).hom
  let i := exteriorIdentityInclusion X Y B A
  let e : exteriorIdentitySupport X Y B A ≅ A.subscheme :=
    asIso (pullback.fst (exteriorSupportSourceProjection X Y A ≫ X.hom) (𝟙 S))
  have hp₁ : p ≫ pullback.fst X.hom Y.hom =
      pullback.fst (SmoothSite.product X B).hom (SmoothSite.product Y B).hom ≫
        (ρ_ X).hom.left :=
    congrArg (fun f => f.left) (SmoothSite.productMap_fst (ρ_ X).hom (ρ_ Y).hom)
  have hp₂ : p ≫ pullback.snd X.hom Y.hom =
      pullback.snd (SmoothSite.product X B).hom (SmoothSite.product Y B).hom ≫
        (ρ_ Y).hom.left :=
    congrArg (fun f => f.left) (SmoothSite.productMap_snd (ρ_ X).hom (ρ_ Y).hom)
  have hi : i ≫ p = e.hom ≫ A.subschemeι := by
    apply pullback.hom_ext
    · simp only [i, Category.assoc, hp₁, exteriorIdentityInclusion_fst_assoc]
      rw [rightUnitor_left, exteriorIdentitySource_fst]
      rfl
    · simp only [i, Category.assoc, hp₂, exteriorIdentityInclusion_snd_assoc]
      rw [rightUnitor_left, exteriorIdentityTarget_fst]
      rfl
  rw [nativeExteriorPrime_val_eq_fundamentalCycle]
  change finiteCyclePushforward p (finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle _)) =
    single z 1
  rw [finiteCyclePushforward_comp_apply]
  calc
    _ = finiteCyclePushforward (e.hom ≫ A.subschemeι) (AlgebraicCycle.fundamentalCycle _) :=
      finiteCyclePushforward_congr _ _ hi _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso,
        finiteCyclePushforward_fundamentalCycle_integral]
      exact congrArg (fun x => single x (1 : ℤ)) (genericPointOf_integralComponentAt z)

/-- The graph right unitor is natural on the actual signed finite correspondences. -/
theorem exteriorRightUnitorNaturality : ExteriorRightUnitorNaturality k := by
  classical
  rintro ⟨X⟩ ⟨Y⟩ a
  apply comp_graph_iso_eq_graph_iso_comp (ρ_ X) (ρ_ Y)
  have ha : exteriorProduct a (𝟙 (tensorUnit k)) = nativeExterior X Y B a :=
    exteriorProduct_identity_right B a
  rw [ha]
  let p := (SmoothSite.productMap (ρ_ X).hom (ρ_ Y).hom).left
  let : IsIso p := productMap_left_isIso (ρ_ X).hom (ρ_ Y).hom
  let G₀ := (finiteCorrespondences (SmoothSite.product X B).hom
    (SmoothSite.product Y B).hom).subtype
  let H : finiteCorrespondences X.hom Y.hom →+ AlgebraicCycle (pullback X.hom Y.hom) ℤ :=
    (finiteCyclePushforward p).comp (G₀.comp (nativeExterior X Y B))
  let G := (finiteCorrespondences X.hom Y.hom).subtype
  have h : H = G := by
    apply finiteCorrespondences.addHom_ext_one X.hom Y.hom
    intro z hz
    change finiteCyclePushforward p (nativeExterior X Y B
      (singleFiniteCorrespondence X.hom Y.hom z hz 1)).val = single z 1
    rw [nativeExterior_single, one_smul]
    exact pushforward_nativeExteriorPrime_base X Y z hz
  exact DFunLike.congr_fun h a

end AlgebraicGeometry.Cor
