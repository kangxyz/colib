/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.CategoryTheory.Sites.Simplicial.MappingCofiber
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Reduced suspension and the simplicial circle

The native simplicial circle is the coequalizer of the two faces of the
standard one-simplex. Smashing its quotient with a pointed presheaf
identifies the cone quotient with smash by that circle.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe w v u

namespace CategoryTheory.PointedSimplicialPresheaf

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private def stdSimplexLiftIso :
    SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{w, 0} ≅ SSet.stdSimplex.{w} :=
  NatIso.ofComponents
    (fun _ ↦ NatIso.ofComponents (fun _ ↦
      (Equiv.ulift.trans
        (SSet.stdSimplex.objEquiv.{0}.trans SSet.stdSimplex.objEquiv.{w}.symm)).toIso)
      (by intro a b f; rfl))
    (by intro a b f; apply NatTrans.ext; funext d; rfl)

private def nativeCirclePi : (Δ[1] : SSet.{0}) ⟶ SSet.S1 :=
  coequalizer.π (SSet.stdSimplex.δ (0 : Fin 2)) (SSet.stdSimplex.δ (1 : Fin 2))

variable (C : Type u) [Category.{v} C]

/-- The constant presheaf map of the original simplicial circle quotient. -/
@[no_expose]
def simplicialCircleQuotient :
    interval.{w} C ⟶ (Functor.const Cᵒᵖ).obj ((SSet.uliftFunctor.{w, 0}).obj SSet.S1) :=
  (Functor.const Cᵒᵖ).map
    ((stdSimplexLiftIso.{w}.app ⦋1⦌).inv ≫ (SSet.uliftFunctor.{w, 0}).map nativeCirclePi)

/-- The quotient sends each simplex to the native circle simplex indexed by
the same order map. -/
theorem simplicialCircleQuotient_app_app (U : Cᵒᵖ) (n : SimplexCategoryᵒᵖ)
    (a : n.unop ⟶ ⦋1⦌) :
    ((simplicialCircleQuotient.{w} C).app U).app n (SSet.stdSimplex.objEquiv.{w}.symm a) =
      ULift.up ((coequalizer.π
        (SSet.stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{0}) ⟶ Δ[1])
        (SSet.stdSimplex.δ (1 : Fin 2))).app n (SSet.stdSimplex.objEquiv.{0}.symm a)) := by
  apply ULift.ext
  rfl

theorem intervalEndpoint_simplicialCircleQuotient :
    intervalEndpoint.{w} C (0 : Fin 2) ≫ simplicialCircleQuotient C =
      intervalEndpoint.{w} C (1 : Fin 2) ≫ simplicialCircleQuotient C := by
  apply NatTrans.ext
  funext U
  have h (i : Fin 2) : (intervalEndpoint.{w} C i ≫ simplicialCircleQuotient C).app U =
      SSet.stdSimplex.isTerminalObj₀.from _ ≫ (stdSimplexLiftIso.{w}.app ⦋0⦌).inv ≫
        (SSet.uliftFunctor.{w, 0}).map (SSet.stdSimplex.δ i ≫ nativeCirclePi) := by
    have hw : SSet.stdSimplex.δ i ≫ (stdSimplexLiftIso.{w}.app ⦋1⦌).inv =
        (stdSimplexLiftIso.{w}.app ⦋0⦌).inv ≫
          (SSet.uliftFunctor.{w, 0}).map (SSet.stdSimplex.δ i) :=
      stdSimplexLiftIso.inv.naturality (SimplexCategory.δ i)
    change (SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.stdSimplex.δ i) ≫
        ((stdSimplexLiftIso.{w}.app ⦋1⦌).inv ≫ (SSet.uliftFunctor.{w, 0}).map nativeCirclePi) = _
    rw [Category.assoc, reassoc_of% hw, ← Functor.map_comp]
  rw [h, h]
  exact congrArg (fun f ↦ SSet.stdSimplex.isTerminalObj₀.from _ ≫
    (stdSimplexLiftIso.{w}.app ⦋0⦌).inv ≫ (SSet.uliftFunctor.{w, 0}).map f)
    (coequalizer.condition _ _)

/-- The constant native simplicial circle pointed by its identified vertices. -/
def pointedSimplicialCircle : PointedSimplicialPresheaf.{w} C :=
  Under.mk (intervalEndpoint C (0 : Fin 2) ≫ simplicialCircleQuotient C)

/-- The pointed quotient from the based interval to the native circle. -/
def basedIntervalToSimplicialCircle : basedInterval.{w} C ⟶ pointedSimplicialCircle.{w} C :=
  Under.homMk (simplicialCircleQuotient C) rfl

private def simplicialCircleIsCoequalizer :
    IsColimit (Cofork.ofπ (simplicialCircleQuotient.{w} C)
      (intervalEndpoint_simplicialCircleQuotient C)) := by
  let G : SSet.{w} ⥤ Cᵒᵖ ⥤ SSet.{w} := Functor.const Cᵒᵖ
  let F := SSet.uliftFunctor.{w, 0} ⋙ G
  letI : PreservesColimitsOfShape WalkingParallelPair SSet.uliftFunctor.{w, 0} := by
    unfold SSet.uliftFunctor
    infer_instance
  let a : (Δ[0] : SSet.{0}) ⟶ Δ[1] := SSet.stdSimplex.δ (0 : Fin 2)
  let b : (Δ[0] : SSet.{0}) ⟶ Δ[1] := SSet.stdSimplex.δ (1 : Fin 2)
  let t := (Functor.isTerminalConst Cᵒᵖ SSet.stdSimplex.isTerminalObj₀).uniqueUpToIso
    (terminalIsTerminal (C := Cᵒᵖ ⥤ SSet.{w}))
  let e := G.mapIso (stdSimplexLiftIso.{w}.app ⦋0⦌) ≪≫ t
  let e' := G.mapIso (stdSimplexLiftIso.{w}.app ⦋1⦌)
  have ht (i : Fin 2) : t.hom ≫ intervalEndpoint C i = G.map (SSet.stdSimplex.δ i) := by
    apply NatTrans.ext
    funext U
    change t.hom.app U ≫ SSet.stdSimplex.isTerminalObj₀.from _ ≫ SSet.stdSimplex.δ i =
      SSet.stdSimplex.δ i
    rw [← Category.assoc, SSet.stdSimplex.isTerminalObj₀.hom_ext (_ ≫ _) (𝟙 _)]
    exact Category.id_comp _
  have he (i : Fin 2) : e.hom ≫ intervalEndpoint C i =
      F.map (SSet.stdSimplex.δ i) ≫ e'.hom := by
    change (G.map (stdSimplexLiftIso.{w}.app ⦋0⦌).hom ≫ t.hom) ≫ intervalEndpoint C i =
      G.map ((SSet.uliftFunctor.{w, 0}).map (SSet.stdSimplex.δ i)) ≫
        G.map (stdSimplexLiftIso.{w}.app ⦋1⦌).hom
    rw [Category.assoc, ht, ← G.map_comp, ← G.map_comp]
    exact congrArg G.map (stdSimplexLiftIso.hom.naturality (SimplexCategory.δ i)).symm
  refine Cofork.isColimitOfIsos _ (isColimitOfHasCoequalizerOfPreservesColimit F a b)
    _ e e' (Iso.refl _) (he 0) (he 1) ?_
  change G.map (stdSimplexLiftIso.{w}.app ⦋1⦌).inv ≫
      G.map ((SSet.uliftFunctor.{w, 0}).map nativeCirclePi) ≫ 𝟙 _ =
    G.map ((stdSimplexLiftIso.{w}.app ⦋1⦌).inv ≫
      (SSet.uliftFunctor.{w, 0}).map nativeCirclePi)
  rw [Category.comp_id, G.map_comp]

variable {C}

private theorem productCircle_condition (X : PointedSimplicialPresheaf.{w} C) :
    prod.map (𝟙 X.right) (intervalEndpoint C (0 : Fin 2)) ≫
        prod.map (𝟙 X.right) (simplicialCircleQuotient C) =
      prod.map (𝟙 X.right) (intervalEndpoint C (1 : Fin 2)) ≫
        prod.map (𝟙 X.right) (simplicialCircleQuotient C) := by
  simp only [prod.map_map, Category.id_comp, intervalEndpoint_simplicialCircleQuotient]

private def productCircleIsCoequalizer (X : PointedSimplicialPresheaf.{w} C) :
    IsColimit (Cofork.ofπ (prod.map (𝟙 X.right) (simplicialCircleQuotient C))
      (productCircle_condition X)) := by
  letI : PreservesColimitsOfShape WalkingParallelPair (prod.functor.obj X.right) :=
    preservesColimitsOfShape_of_natIso (CartesianMonoidalCategory.tensorLeftIsoProd X.right)
  exact isColimitCoforkMapOfIsColimit (prod.functor.obj X.right) _
    (simplicialCircleIsCoequalizer C)

/-- The actual cone map induced by the simplicial circle quotient. -/
def reducedConeToCircleSmash (X : PointedSimplicialPresheaf.{w} C) :
    reducedCone X ⟶ Under.smash X (pointedSimplicialCircle C) :=
  Under.smashMap (𝟙 X) (basedIntervalToSimplicialCircle C)

@[reassoc]
theorem toSmash_reducedConeToCircleSmash (X : PointedSimplicialPresheaf.{w} C) :
    Under.toSmash X (basedInterval C) ≫ (reducedConeToCircleSmash X).right =
      prod.map (𝟙 X.right) (simplicialCircleQuotient C) ≫
        Under.toSmash X (pointedSimplicialCircle C) :=
  Under.toSmash_smashMap (𝟙 X) (basedIntervalToSimplicialCircle C)

private theorem endpointSlice_circleQuotient (X : PointedSimplicialPresheaf.{w} C) (i : Fin 2) :
    prod.lift (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C i) ≫
        prod.map (𝟙 X.right) (simplicialCircleQuotient C) =
      prod.lift (𝟙 X.right) (terminal.from X.right ≫ (pointedSimplicialCircle C).hom) := by
  apply prod.hom_ext
  · rw [Category.assoc, prod.map_fst, Category.comp_id, prod.lift_fst]
    exact (prod.lift_fst _ _).symm
  · rw [Category.assoc, prod.map_snd, prod.lift_snd_assoc, prod.lift_snd]
    change (terminal.from X.right ≫ intervalEndpoint C i) ≫ simplicialCircleQuotient C =
      terminal.from X.right ≫ intervalEndpoint C (0 : Fin 2) ≫ simplicialCircleQuotient C
    rw [Category.assoc]
    fin_cases i
    · rfl
    · exact congrArg (fun k ↦ terminal.from X.right ≫ k)
        (intervalEndpoint_simplicialCircleQuotient C).symm

private theorem reducedConeInclusion_comp_reducedConeToCircleSmash
    (X : PointedSimplicialPresheaf.{w} C) :
    reducedConeInclusion X ≫ reducedConeToCircleSmash X = 0 := by
  apply Under.UnderMorphism.ext
  change (prod.lift (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C (1 : Fin 2)) ≫
      Under.toSmash X (basedInterval C)) ≫ (reducedConeToCircleSmash X).right =
    terminal.from X.right ≫ (Under.smash X (pointedSimplicialCircle C)).hom
  rw [Category.assoc, toSmash_reducedConeToCircleSmash, ← Category.assoc,
    endpointSlice_circleQuotient, Under.leftAxis_toSmash]

private theorem productEndpoint_eq (X : PointedSimplicialPresheaf.{w} C) (i : Fin 2) :
    prod.map (𝟙 X.right) (intervalEndpoint C i) =
      prod.fst ≫ prod.lift (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C i) := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.map_fst, prod.lift_fst, Category.comp_id]
  · simp only [Category.assoc, prod.map_snd, prod.lift_snd, terminal.comp_from_assoc]
    exact congrArg (fun f ↦ f ≫ intervalEndpoint C i) (terminal.hom_ext _ _)

private theorem endpointSlice_comp_coneMap
    {X Z : PointedSimplicialPresheaf.{w} C} (m : reducedCone X ⟶ Z)
    (hm : reducedConeInclusion X ≫ m = 0) (i : Fin 2) :
    prod.lift (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C i) ≫
      Under.toSmash X (basedInterval C) ≫ m.right = terminal.from X.right ≫ Z.hom := by
  fin_cases i
  · change prod.lift (𝟙 X.right) (terminal.from X.right ≫ (basedInterval C).hom) ≫
      Under.toSmash X (basedInterval C) ≫ m.right = _
    rw [Under.leftAxis_toSmash_assoc, Under.w m]
  · have h := congrArg (fun k : X ⟶ Z ↦ k.right) hm
    change (prod.lift (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C (1 : Fin 2)) ≫
      Under.toSmash X (basedInterval C)) ≫ m.right = terminal.from X.right ≫ Z.hom at h
    change prod.lift (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C (1 : Fin 2)) ≫
      Under.toSmash X (basedInterval C) ≫ m.right = _
    simpa only [Category.assoc] using h

private theorem rightAxis_naturality (X : PointedSimplicialPresheaf.{w} C)
    {A B : Cᵒᵖ ⥤ SSet.{w}} (q : A ⟶ B) :
    q ≫ prod.lift (terminal.from B ≫ X.hom) (𝟙 B) =
      prod.lift (terminal.from A ≫ X.hom) (𝟙 A) ≫ prod.map (𝟙 X.right) q := by
  apply prod.hom_ext
  · simp only [Category.assoc, prod.lift_fst, prod.map_fst, Category.comp_id,
      terminal.comp_from_assoc]
  · simp only [Category.assoc, prod.lift_snd, prod.map_snd, prod.lift_snd_assoc,
      Category.comp_id, Category.id_comp]

private theorem exists_circleSmashDesc
    {X Z : PointedSimplicialPresheaf.{w} C} (m : reducedCone X ⟶ Z)
    (hm : reducedConeInclusion X ≫ m = 0) :
    ∃ a : Under.smash X (pointedSimplicialCircle C) ⟶ Z, reducedConeToCircleSmash X ≫ a = m := by
  let S := pointedSimplicialCircle.{w} C
  let q : (basedInterval.{w} C).right ⟶ S.right := simplicialCircleQuotient C
  obtain ⟨d, hd⟩ := Cofork.IsColimit.desc' (productCircleIsCoequalizer X)
    (Under.toSmash X (basedInterval C) ≫ m.right)
    (by simp only [productEndpoint_eq, Category.assoc, endpointSlice_comp_coneMap m hm])
  change prod.map (𝟙 X.right) q ≫ d = _ at hd
  have hl : prod.lift (𝟙 X.right) (terminal.from X.right ≫ S.hom) ≫ d =
      terminal.from X.right ≫ Z.hom := by
    have hs := endpointSlice_circleQuotient X (0 : Fin 2)
    change prod.lift (𝟙 X.right) (terminal.from X.right ≫ intervalEndpoint C (0 : Fin 2)) ≫
      prod.map (𝟙 X.right) q = prod.lift (𝟙 X.right) (terminal.from X.right ≫ S.hom) at hs
    rw [← hs, Category.assoc, hd, endpointSlice_comp_coneMap m hm]
  have hr : prod.lift (terminal.from S.right ≫ X.hom) (𝟙 S.right) ≫ d =
      terminal.from S.right ≫ Z.hom := by
    let : Epi q := Cofork.IsColimit.epi (simplicialCircleIsCoequalizer C)
    apply (cancel_epi q).mp
    rw [← Category.assoc, rightAxis_naturality X q, Category.assoc, hd,
      Under.rightAxis_toSmash_assoc, Under.w m, terminal.comp_from_assoc]
  have hw : Under.axesToProduct X S ≫ d = terminal.from _ ≫ Z.hom := by
    apply coprod.hom_ext
    · simpa only [Under.axesToProduct, coprod.inl_desc_assoc, terminal.comp_from_assoc] using hl
    · simpa only [Under.axesToProduct, coprod.inr_desc_assoc, terminal.comp_from_assoc] using hr
  let a : Under.smash X S ⟶ Z :=
    Under.homMk (pushout.desc d Z.hom hw) (pushout.inr_desc _ _ _)
  have ha : Under.toSmash X S ≫ a.right = d := pushout.inl_desc _ _ _
  refine ⟨a, ?_⟩
  apply Under.smash_hom_ext
  rw [Under.comp_right, toSmash_reducedConeToCircleSmash_assoc, ha, hd]

/-- Smashing with the native circle gives the pushout that collapses the
original cone inclusion to the point. -/
theorem isPushout_reducedConeToCircleSmash (X : PointedSimplicialPresheaf.{w} C) :
    IsPushout (toPoint C X) (reducedConeInclusion X)
      (fromPoint C (Under.smash X (pointedSimplicialCircle C))) (reducedConeToCircleSmash X) := by
  refine IsPushout.mk' ?_ ?_ ?_
  · rw [reducedConeInclusion_comp_reducedConeToCircleSmash]
    rw [(point_isZero C).eq_of_src (fromPoint C _) 0, comp_zero]
  · intro T a b _ hab
    apply Under.smash_hom_ext
    let : Epi (prod.map (𝟙 X.right) (simplicialCircleQuotient C)) :=
      Cofork.IsColimit.epi (productCircleIsCoequalizer X)
    apply (cancel_epi (prod.map (𝟙 X.right) (simplicialCircleQuotient C))).mp
    simpa only [Under.comp_right, toSmash_reducedConeToCircleSmash_assoc] using
      congrArg (fun m : reducedCone X ⟶ T ↦ Under.toSmash X (basedInterval C) ≫ m.right) hab
  · intro T a b hab
    have hb : reducedConeInclusion X ≫ b = 0 := by
      rw [← hab, (point_isZero C).eq_of_src a 0, comp_zero]
    obtain ⟨m, hm⟩ := exists_circleSmashDesc b hb
    exact ⟨m, (point_isZero C).eq_of_src _ _, hm⟩

/-- The reduced suspension, formed as the cofiber of the collapse to the point,
is canonically the smash with the pointed native simplicial circle. -/
def reducedSuspensionCircleIso (X : PointedSimplicialPresheaf.{w} C) :
    reducedMappingCofiber (toPoint C X) ≅ Under.smash X (pointedSimplicialCircle C) :=
  (isPushout_reducedConeToCircleSmash X).isoPushout.symm

@[reassoc]
theorem reducedConeToMappingCofiber_reducedSuspensionCircleIso_hom
    (X : PointedSimplicialPresheaf.{w} C) :
    reducedConeToMappingCofiber (toPoint C X) ≫ (reducedSuspensionCircleIso X).hom =
      reducedConeToCircleSmash X :=
  (isPushout_reducedConeToCircleSmash X).inr_isoPushout_inv

@[reassoc]
theorem reducedSuspensionCircleIso_naturality {X Y : PointedSimplicialPresheaf.{w} C}
    (f : X ⟶ Y) :
    reducedMappingCofiberMap (Arrow.homMk' f (𝟙 _)
      ((point_isZero C).isTerminal.hom_ext _ _) :
        Arrow.mk (toPoint C X) ⟶ Arrow.mk (toPoint C Y)) ≫ (reducedSuspensionCircleIso Y).hom =
      (reducedSuspensionCircleIso X).hom ≫ Under.smashMap f (𝟙 (pointedSimplicialCircle C)) := by
  let s : Arrow.mk (toPoint C X) ⟶ Arrow.mk (toPoint C Y) :=
    Arrow.homMk' f (𝟙 _) ((point_isZero C).isTerminal.hom_ext _ _)
  change reducedMappingCofiberMap s ≫ (reducedSuspensionCircleIso Y).hom = _
  apply (reducedMappingCofiber_isPushout (toPoint C X)).hom_ext
  · exact (point_isZero C).eq_of_src _ _
  · calc
      _ = reducedConeMap f ≫ reducedConeToMappingCofiber (toPoint C Y) ≫
          (reducedSuspensionCircleIso Y).hom := reducedConeToMappingCofiber_map_assoc s _
      _ = reducedConeMap f ≫ reducedConeToCircleSmash Y := by
        rw [reducedConeToMappingCofiber_reducedSuspensionCircleIso_hom]
      _ = reducedConeToCircleSmash X ≫ Under.smashMap f (𝟙 (pointedSimplicialCircle C)) := by
        simp only [reducedConeMap, reducedConeToCircleSmash, Under.smashMap_comp,
          Category.comp_id, Category.id_comp]
      _ = _ := (reducedConeToMappingCofiber_reducedSuspensionCircleIso_hom_assoc X _).symm

attribute [colib_tag "COL-1009"]
  pointedSimplicialCircle
  simplicialCircleQuotient_app_app
  isPushout_reducedConeToCircleSmash
  reducedSuspensionCircleIso
  reducedConeToMappingCofiber_reducedSuspensionCircleIso_hom
  reducedSuspensionCircleIso_naturality
attribute [colib_ref "MorelVoevodsky1999"
  "Section 3.2, Spheres, suspensions and Thom spaces, pp. 110–111" "ingredient"
  "The constant simplicial circle and the smash description of simplicial suspension"]
  pointedSimplicialCircle

end CategoryTheory.PointedSimplicialPresheaf
