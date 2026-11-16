/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.EtaleCohomology.FiniteEtalePushforwardLocallyFree
public import Colib.AlgebraicGeometry.EtaleCohomology.RootsOfUnityLocallyFree
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules

/-!
# Inverse image preserves locally finite free coefficients

Lightweight reuse of the site-comparison argument for locally constant sheaves,
without importing the unrelated Fourier and Lefschetz trace developments.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology
universe u
namespace Colib.EtaleLocallyFree

variable (Λ : Type) [CommRing Λ]
attribute [local instance] moduleCat_hasLimitsOfSize

local instance (S : Scheme.{u}) (V : S.Etale) :
    HasSheafify (S.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ) :=
  Stacks.ConstantSheaf.hasSheafify_over_moduleCat.{u + 1, u, 0, 0}
    S.smallEtaleTopology Λ V

/-- **Inverse image carries constant sheaves of modules to constant sheaves of modules**: both
`f^{-1} ∘ (constant sheaf on S)` and the constant sheaf on `Y` are left adjoint to evaluation at
the final object, since base change carries the final object to the final object. -/
def inverseImageConstantIso {Y S : Scheme.{u}} (f : Y ⟶ S) :
    constantSheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        etaleModuleInverseImage.{u, 0} Λ f ≅
      constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) := by
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    (HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
      RingHom.Etale.containsIdentities :
        MorphismProperty.IsMultiplicative
          (@Etale : MorphismProperty Scheme.{u})).toContainsIdentities
  let T : S.Etale := MorphismProperty.Over.mk ⊤ (𝟙 S) (by infer_instance)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let hGT := hT.isTerminalObj (smallEtaleBaseChange f)
  exact ((constantSheafAdj _ _ hT).comp (etaleModuleInverseImageAdj.{u, 0} Λ f)).leftAdjointUniq
    (constantSheafAdj _ _ hGT)

/-- **A trivialization of `w⁻¹ F` on `W_étale` is a trivialization of `F` on the slice
`X_étale / W`**, for the structure morphism `w : W ⟶ X` of an étale `X`-scheme. This is the
converse of `Stacks.EtaleCohomology.etaleModuleInverseImageIsoConstantOfOverPullback`. -/
def overPullbackIsoConstant {X : Scheme.{u}} (W : X.Etale)
    (F : EtaleModules.{u, 0} Λ X) (M : ModuleCat.{u + 1} Λ)
    (e : (etaleModuleInverseImage.{u, 0} Λ W.hom).obj F ≅
      (constantSheaf W.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :
    (constantSheaf ((smallEtaleTopology X).over W) (ModuleCat.{u + 1} Λ)).obj M ≅
      ((smallEtaleTopology X).overPullback _ W).obj F :=
  letI : (Scheme.Etale.smallEtaleCompose W.hom).IsContinuous
      W.left.smallEtaleTopology X.smallEtaleTopology :=
    Scheme.Etale.smallEtaleCompose_isContinuous _
  letI := Functor.isContinuous_comp (etaleLeftOverFunctor W) (Over.forget W)
    W.left.smallEtaleTopology ((smallEtaleTopology X).over W) X.smallEtaleTopology
  let ρ := (etaleLeftOverFunctor W).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
    W.left.smallEtaleTopology ((smallEtaleTopology X).over W)
  let hff : ρ.FullyFaithful := Functor.FullyFaithful.ofFullyFaithful ρ
  hff.preimageIso
    ((Stacks.Cohomology.DenseSubsiteGlobal.constantSheafRestrictionIso
      W.left.smallEtaleTopology ((smallEtaleTopology X).over W) (etaleLeftOverFunctor W)
      (ModuleCat.{u + 1} Λ)).app M ≪≫ e.symm ≪≫
      (etaleModuleInverseImageRestrictionIso.{u, 0} Λ W.hom).app F ≪≫
      (Functor.sheafPushforwardContinuousIso (smallEtaleComposeIsoEtaleLeftOverFunctor W)
        (ModuleCat.{u + 1} Λ) W.left.smallEtaleTopology X.smallEtaleTopology).app F)

/-- If `w = a ≫ V.hom` for an étale `Y`-scheme `V` on which `N` is trivialized by `e`, then
`w⁻¹ N` is constant. -/
private def inverseImageIsoConstantOfComp {X Y : Scheme.{u}} (V : Y.Etale)
    (N : EtaleModules.{u, 0} Λ Y) (E : ModuleCat.{u + 1} Λ)
    (e : (constantSheaf (Y.smallEtaleTopology.over V) (ModuleCat.{u + 1} Λ)).obj E ≅
      (Y.smallEtaleTopology.overPullback _ V).obj N)
    (a : X ⟶ V.left) (w : X ⟶ Y) (hw : w = a ≫ V.hom) :
    (etaleModuleInverseImage.{u, 0} Λ w).obj N ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj E :=
  eqToIso (congrArg (fun φ => (etaleModuleInverseImage.{u, 0} Λ φ).obj N) hw) ≪≫
    (etaleModuleInverseImageCompIso.{u, 0} Λ a V.hom).app N ≪≫
    (etaleModuleInverseImage.{u, 0} Λ a).mapIso
      (etaleModuleInverseImageIsoConstantOfOverPullback V Λ N E e) ≪≫
    (inverseImageConstantIso Λ a).app E

attribute [local instance] moduleCat_hasLimitsOfSize in
/-- **The inverse image of a locally constant sheaf is locally constant**, with the same local
values. -/
theorem inverseImage_locallyConstantWith (Q : ModuleCat.{u + 1} Λ → Prop) {X Y : Scheme.{u}}
    (a : X ⟶ Y) {N : EtaleModules.{u, 0} Λ Y}
    (hN : Stacks.ConstantSheaf.IsLocallyConstantWith Λ Y.smallEtaleTopology Q N) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ X.smallEtaleTopology Q
      ((etaleModuleInverseImage.{u, 0} Λ a).obj N) := by
  intro V
  obtain ⟨I, Vs, f, hcov, htriv⟩ := hN (Scheme.Etale.mk (𝟙 Y))
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hcov
  -- the base change of the covering to `V`
  have : Etale V.hom := V.prop
  have : ∀ i, Etale (Vs i).hom := fun i => (Vs i).prop
  let W : I → X.Etale := fun i =>
    Scheme.Etale.mk (pullback.fst (V.hom ≫ a) (Vs i).hom ≫ V.hom)
  let g : ∀ i, W i ⟶ V := fun i =>
    MorphismProperty.Over.homMk (pullback.fst (V.hom ≫ a) (Vs i).hom) rfl
  refine ⟨I, W, g, ?_, fun i => ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun v => ?_
    obtain ⟨i, w, hw⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ ((V.hom ≫ a) v))
    have hw' : (Vs i).hom w = (V.hom ≫ a) v := by
      rw [← hw]
      exact congrArg (fun φ : (Vs i).left ⟶ Y => φ w) ((f i).w.symm.trans (Category.comp_id _))
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback v w hw'.symm
    exact Set.mem_iUnion.2 ⟨i, z, hz⟩
  · obtain ⟨E, hE, ⟨e⟩⟩ := htriv i
    refine ⟨E, hE, ⟨overPullbackIsoConstant Λ (W i) _ E ?_⟩⟩
    have hsq : (W i).hom ≫ a = pullback.snd (V.hom ≫ a) (Vs i).hom ≫ (Vs i).hom := by
      change (pullback.fst (V.hom ≫ a) (Vs i).hom ≫ V.hom) ≫ a = _
      rw [Category.assoc]
      exact pullback.condition
    exact (etaleModuleInverseImageCompIso.{u, 0} Λ (W i).hom a).symm.app N ≪≫
      inverseImageIsoConstantOfComp Λ (Vs i) N E e _ _ hsq


attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules

/-- The actual coefficient g_*g⁻¹μ_N has exact right tensor, for finite étale g. -/
theorem exact_tensorRight_pushforward_pullback_rootsOfUnityModule
    {X Y : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k))
    (g : Y ⟶ X) [IsFinite g] [Etale g] (N : ℕ) [NeZero N] [NeZero (N : k)] :
    let G := (etaleModuleDirectImage.{u, 0} (ZMod N) g).obj
      ((etaleModuleInverseImage.{u, 0} (ZMod N) g).obj
        (Stacks.Kummer.rootsOfUnityModule.{u, 0} X N))
    (MonoidalCategory.tensorRight G).Additive ∧
      PreservesFiniteLimits (MonoidalCategory.tensorRight G) ∧
      PreservesFiniteColimits (MonoidalCategory.tensorRight G) := by
  apply exact_tensorRight_directImage_of_locallyFiniteFree
  exact inverseImage_locallyConstantWith (ZMod N) _ g
    (Stacks.Kummer.locallyFiniteFree_rootsOfUnityModule f N)

end Colib.EtaleLocallyFree
