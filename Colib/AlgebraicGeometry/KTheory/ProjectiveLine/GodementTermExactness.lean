/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import StacksFrontier.AlgebraicGeometry.Cohomology.GodementBoundedBelowResolution
public import StacksFrontier.Topology.Sheaves.RingedSpace.FlatModulePullback

/-! # Exactness of the terms of the Godement resolution

For the morphism from the discrete space, pullback is exact because its stalk ring maps
are isomorphisms. Pushforward is exact because all sheaves on the source are flasque,
so the pushforward of an epimorphism is surjective on every open.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

namespace AlgebraicGeometry.GodementResolution

universe u

variable {X Y : RingedSpace.{u, u}}

private theorem flasque_of_discrete {T : TopCat.{u}} [DiscreteTopology T]
    (F : TopCat.Sheaf AddCommGrpCat.{u} T) : F.IsFlasque := by
  constructor
  intro U V i
  let A : Opens T := unop V
  let B : Opens T := unop U
  have hle : A ≤ B := i.unop.le
  let W : Opens T := ⟨(B : Set T) \ (A : Set T), isOpen_discrete _⟩
  have hdisj : A ⊓ W = ⊥ := by
    ext x
    simp [W]
  have hunion : A ⊔ W = B := by
    ext x
    simp only [Opens.mem_sup, SetLike.mem_coe, W]
    exact ⟨fun h => h.elim (fun ha => hle ha) And.left,
      fun hb => (em (x ∈ A)).imp_right fun ha => ⟨hb, ha⟩⟩
  let L := F.isProductOfDisjoint A W hdisj
  let t := L.lift (BinaryFan.mk (𝟙 (F.obj.obj (op A)))
    (0 : F.obj.obj (op A) ⟶ F.obj.obj (op W)))
  have ht : t ≫ F.obj.map (homOfLE le_sup_left).op = 𝟙 (F.obj.obj (op A)) :=
    L.fac (BinaryFan.mk (𝟙 _) 0) ⟨WalkingPair.left⟩
  let r := t ≫ F.obj.map (eqToHom hunion.symm).op
  have hcomp : (eqToHom hunion.symm).op ≫ i = (homOfLE le_sup_left).op :=
    Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hr : r ≫ F.obj.map i = 𝟙 (F.obj.obj (op A)) := by
    dsimp [r]
    rw [Category.assoc, ← Functor.map_comp, hcomp, ht]
  exact SplitEpi.epi ⟨r, hr⟩

/-- Pushforward from a discrete ringed space preserves finite colimits. -/
theorem preservesFiniteColimits_modulePushforward_of_discrete (f : X ⟶ Y)
    [DiscreteTopology X] : PreservesFiniteColimits (modulePushforward f) := by
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi _).mpr
  intro S hS
  refine ⟨((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono _).mp
    (inferInstance : PreservesFiniteLimits (modulePushforward f)) S hS).1, ?_⟩
  let U : SheafOfModules.{u} (structureSheafRing X) ⥤ TopCat.Sheaf AddCommGrpCat.{u} X :=
    SheafOfModules.toSheaf (structureSheafRing X)
  let V : SheafOfModules.{u} (structureSheafRing Y) ⥤ TopCat.Sheaf AddCommGrpCat.{u} Y :=
    SheafOfModules.toSheaf (structureSheafRing Y)
  let : U.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : PreservesFiniteLimits U := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf (structureSheafRing X)))
  let : PreservesFiniteColimits U := inferInstanceAs
    (PreservesFiniteColimits (SheafOfModules.toSheaf (structureSheafRing X)))
  let : (S.map U).X₁.IsFlasque := flasque_of_discrete _
  have hSU : (S.map U).ShortExact := hS.map_of_exact U
  let hV : V.ReflectsEpimorphisms := inferInstanceAs
    ((SheafOfModules.toSheaf (structureSheafRing Y)).ReflectsEpimorphisms)
  apply hV.reflects
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply Presheaf.isLocallySurjective_of_surjective _ _
  intro W
  change Function.Surjective ((S.map U).g.1.app (op ((Opens.map f.hom.base).obj (unop W))))
  exact (AddCommGrpCat.epi_iff_surjective _).mp
    (TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := (Opens.map f.hom.base).obj (unop W)) hSU)

private instance fromDiscrete_pullback_preservesFiniteLimits (X : RingedSpace.{u, u}) :
    PreservesFiniteLimits (modulePullback (fromDiscrete X)) :=
  preservesFiniteLimits_modulePullback_of_isFlat (fromDiscrete X)
    (fun x => RingHom.Flat.of_bijective (fromDiscrete_stalkMap_bijective X x))

private instance fromDiscrete_pushforward_preservesFiniteColimits (X : RingedSpace.{u, u}) :
    PreservesFiniteColimits (modulePushforward (fromDiscrete X)) :=
  preservesFiniteColimits_modulePushforward_of_discrete _

private lemma iterate_preservesFiniteLimits {C : Type*} [Category C] (T : C ⥤ C)
    [PreservesFiniteLimits T] : ∀ n : ℕ, PreservesFiniteLimits (T.iterate n)
  | 0 => inferInstanceAs (PreservesFiniteLimits (𝟭 C))
  | n + 1 => by
    let := iterate_preservesFiniteLimits T n
    exact inferInstanceAs (PreservesFiniteLimits (T.iterate n ⋙ T))

private lemma iterate_preservesFiniteColimits {C : Type*} [Category C] (T : C ⥤ C)
    [PreservesFiniteColimits T] : ∀ n : ℕ, PreservesFiniteColimits (T.iterate n)
  | 0 => inferInstanceAs (PreservesFiniteColimits (𝟭 C))
  | n + 1 => by
    let := iterate_preservesFiniteColimits T n
    exact inferInstanceAs (PreservesFiniteColimits (T.iterate n ⋙ T))

private lemma iterate_preservesZeroMorphisms {C : Type*} [Category C] [HasZeroMorphisms C]
    (T : C ⥤ C) [T.PreservesZeroMorphisms] : ∀ n : ℕ, (T.iterate n).PreservesZeroMorphisms
  | 0 => inferInstanceAs (𝟭 C).PreservesZeroMorphisms
  | n + 1 => by
    let := iterate_preservesZeroMorphisms T n
    exact inferInstanceAs (T.iterate n ⋙ T).PreservesZeroMorphisms

/-- Every term of the actual Godement resolution preserves short exact sequences. -/
theorem godementTerm_shortExact {S : ShortComplex (SheafOfModules.{u} (structureSheafRing X))}
    (hS : S.ShortExact) (n : ℕ) :
    (S.map (godementComplex X ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℕ) n)).ShortExact := by
  let : (modulePullback (fromDiscrete X)).IsLeftAdjoint :=
    (modulePullbackPushforwardAdjunction (fromDiscrete X)).isLeftAdjoint
  let T := modulePullback (fromDiscrete X) ⋙ modulePushforward (fromDiscrete X)
  let : PreservesFiniteLimits T := inferInstanceAs
    (PreservesFiniteLimits (modulePullback (fromDiscrete X) ⋙ modulePushforward (fromDiscrete X)))
  let : PreservesFiniteColimits T := inferInstanceAs
    (PreservesFiniteColimits (modulePullback (fromDiscrete X) ⋙
      modulePushforward (fromDiscrete X)))
  let : T.PreservesZeroMorphisms := inferInstanceAs
    ((modulePullback (fromDiscrete X) ⋙
      modulePushforward (fromDiscrete X)).PreservesZeroMorphisms)
  let := iterate_preservesFiniteLimits T (n + 1)
  let := iterate_preservesFiniteColimits T (n + 1)
  let : ((modulePullback (fromDiscrete X) ⋙ modulePushforward
      (fromDiscrete X)).iterate (n + 1)).PreservesZeroMorphisms :=
    iterate_preservesZeroMorphisms T (n + 1)
  exact (ShortComplex.shortExact_iff_of_iso (S.mapNatIso (godementComplexEvalIso X n))).mpr
    (hS.map_of_exact (T.iterate (n + 1)))

end AlgebraicGeometry.GodementResolution
