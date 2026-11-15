/-
Copyright (c) 2026 Colib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Colib contributors
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatBaseChange
public import Colib.AlgebraicGeometry.Chow.FiniteOpenRestriction
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.Exterior
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.GradedCycle
public import Colib.AlgebraicGeometry.Correspondences.Monoidal.ProductPullback
public import Colib.AlgebraicGeometry.Scheme.FiniteTypeNoetherian
public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductAssociativity
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.FlatPullbackPrincipalDivisor

/-!
# Finite pushforward of exterior prime cycles

The exterior prime cycle of two points is the full fundamental cycle of
the product of their reduced closures, pushed into the ambient product.
Finite pushforward along the original product map gives the same cycle at
the two image points, with both full residue-field degrees. Stacks 02RB
identifies the whole fundamental cycles with the pullbacks used in the
two applications of Stacks 02RG.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme Function.locallyFinsuppWithin

universe u

namespace Stacks.Chow

variable {k : Type u} [Field k]

private theorem flatPullback_eq_wholeFundamentalCycle {A X : Scheme.{u}}
    [IsIntegral X] [IsNoetherian A]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (p : A ⟶ X) [LocallyOfFiniteType p] [Flat p]
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension p r)
    (n : ℤ) (hn : relativeDimension (fieldChowSituation k).dimensionFunction s
      (genericPoint X) = n) :
    (flatPullback (fieldChowSituation k) (p ≫ s) s p rfl r hr n
      (cycleAssociatedToClosedSubscheme (fieldChowSituation k) s (𝟙 X) n)).val =
        AlgebraicCycle.fundamentalCycle A := by
  let C := fieldChowSituation k
  have hX : schemeDeltaDimension C s = (n : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, hn]
  have hA (x : genericPoints A) :
      relativeDimension C.dimensionFunction (p ≫ s) x.val = n + (r : ℤ) := by
    have h := relativeDimension_genericPoint_irreducibleComponent C (p ≫ s) s p rfl r hr
      hX (genericPoints.component x)
    have hx : (genericPoints.component x).2.1.genericPoint = x.val :=
      congrArg Subtype.val (genericPoints.ofComponent_component x)
    rwa [hx] at h
  rw [fundamentalCycle_eq_graded_of_genericDimensions C (p ≫ s) _ hA]
  have hp := flatPullback_cycleAssociatedToClosedSubscheme C (p ≫ s) s p rfl r hr n
    (𝟙 X) (by simpa only [Category.id_comp] using hX)
  have hi := cycleAssociatedToClosedSubscheme_eq_of_iso C (p ≫ s)
    (pullback.fst p (𝟙 X)) (𝟙 A) (asIso (pullback.fst p (𝟙 X))) (by simp) (n + (r : ℤ))
  exact congrArg Subtype.val (hp.trans hi)

private theorem finiteCyclePushforward_wholeFundamentalCycle_of_flatBaseChange
    {X Y X' Y' : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNoetherian X'] [IsNoetherian Y']
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] (hη : f (genericPoint X) = genericPoint Y)
    (g : Y' ⟶ Y) [LocallyOfFiniteType g] [Flat g]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (hsq : IsPullback g' f' f g)
    (r : ℕ) (hr : AlgebraicGeometry.RelativeDimension g r) :
    letI : IsFinite f' := MorphismProperty.of_isPullback hsq inferInstance
    finiteCyclePushforward f' (AlgebraicCycle.fundamentalCycle X') =
      (f.residueDegree (genericPoint X) : ℤ) • AlgebraicCycle.fundamentalCycle Y' := by
  classical
  let : IsFinite f' := MorphismProperty.of_isPullback hsq inferInstance
  let : LocallyOfFiniteType g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let : Flat g' := MorphismProperty.of_isPullback hsq.flip inferInstance
  let C := fieldChowSituation k
  let n := relativeDimension C.dimensionFunction (f ≫ s) (genericPoint X)
  let d := (f.residueDegree (genericPoint X) : ℤ)
  let α := cycleAssociatedToClosedSubscheme C (f ≫ s) (𝟙 X) n
  let β := cycleAssociatedToClosedSubscheme C s (𝟙 Y) n
  have hn : relativeDimension C.dimensionFunction s (genericPoint Y) = n :=
    ((relativeDimension_eq_of_finite_residueField C.dimensionFunction s f (genericPoint X)
      (residueField_finite_of_locallyQuasiFinite f (genericPoint X))).trans
        (congrArg (relativeDimension C.dimensionFunction s) hη)).symm
  have hα : α.val = single (genericPoint X) (1 : ℤ) :=
    cycleAssociatedToClosedSubscheme_eq_single C (f ≫ s) (𝟙 X) n rfl
  have hβ : β.val = single (genericPoint Y) (1 : ℤ) :=
    cycleAssociatedToClosedSubscheme_eq_single C s (𝟙 Y) n hn
  have hpush : properPushforward C (f ≫ s) s f rfl n α = d • β := by
    apply Subtype.ext
    rw [properPushforward_val_eq_finiteCyclePushforward]
    change finiteCyclePushforward f α.val = d • β.val
    rw [hα, hβ, finiteCyclePushforward_single, one_mul, hη]
    apply Function.locallyFinsuppWithin.ext
    intro y
    by_cases hy : y = genericPoint Y <;> simp [single_apply, hy, d]
  let hr' := AlgebraicGeometry.RelativeDimension.of_isPullback hsq.flip hr
  have hsrc := flatPullback_eq_wholeFundamentalCycle (f ≫ s) g' r hr' n rfl
  have htgt := flatPullback_eq_wholeFundamentalCycle s g r hr n hn
  have hbase := finiteCyclePushforward_flatPullback C (f ≫ s) s
    (g' ≫ f ≫ s) (g ≫ s) f g g' f' hsq rfl rfl rfl r hr n α
  rw [← hsrc, hbase, hpush, map_zsmul]
  change d • (flatPullback C (g ≫ s) s g rfl r hr n β).val = _
  rw [htgt]

private theorem finiteCyclePushforward_product_of_integral
    {A B A' B' : Scheme.{u}}
    [IsIntegral A] [IsIntegral B] [IsIntegral A'] [IsIntegral B']
    (a : A ⟶ Spec (.of k)) [LocallyOfFiniteType a] [QuasiCompact a]
    (b : B ⟶ Spec (.of k)) [LocallyOfFiniteType b] [QuasiCompact b]
    (a' : A' ⟶ Spec (.of k)) [LocallyOfFiniteType a'] [QuasiCompact a']
    (b' : B' ⟶ Spec (.of k)) [LocallyOfFiniteType b'] [QuasiCompact b']
    (f : A ⟶ A') [IsFinite f] (g : B ⟶ B') [IsFinite g]
    (hf : a = f ≫ a') (hg : b = g ≫ b')
    (hηf : f (genericPoint A) = genericPoint A')
    (hηg : g (genericPoint B) = genericPoint B') :
    letI := Scheme.isNoetherian_of_finiteType_of_isNoetherian (pullback.fst a b ≫ a)
    letI := Scheme.isNoetherian_of_finiteType_of_isNoetherian (pullback.fst a' b' ≫ a')
    letI : IsFinite (pullback.map a b a' b' f g (𝟙 (Spec (.of k)))
        ((Category.comp_id _).trans hf) ((Category.comp_id _).trans hg)) :=
      MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance hf hg
    finiteCyclePushforward (pullback.map a b a' b' f g (𝟙 (Spec (.of k)))
        ((Category.comp_id _).trans hf) ((Category.comp_id _).trans hg))
        (AlgebraicCycle.fundamentalCycle (pullback a b)) =
      ((f.residueDegree (genericPoint A) : ℤ) * (g.residueDegree (genericPoint B) : ℤ)) •
        AlgebraicCycle.fundamentalCycle (pullback a' b') := by
  let : IsNoetherian (pullback a b) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (pullback.fst a b ≫ a)
  let : IsNoetherian (pullback a' b) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (pullback.fst a' b ≫ a')
  let : IsNoetherian (pullback a' b') :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (pullback.fst a' b' ≫ a')
  let mF : pullback a b ⟶ pullback a' b :=
    pullback.map a b a' b f (𝟙 _) (𝟙 _) ((Category.comp_id _).trans hf) (by simp)
  let mG : pullback a' b ⟶ pullback a' b' :=
    pullback.map a' b a' b' (𝟙 _) g (𝟙 _) (by simp) ((Category.comp_id _).trans hg)
  let m : pullback a b ⟶ pullback a' b' :=
    pullback.map a b a' b' f g (𝟙 _) ((Category.comp_id _).trans hf)
      ((Category.comp_id _).trans hg)
  have hF : IsPullback mF (pullback.fst a b) (pullback.fst a' b) f := by
    refine IsPullback.of_right ?_ (by simp [mF, pullback.map])
      (IsPullback.of_hasPullback a' b).flip
    have hm : mF ≫ pullback.snd a' b = pullback.snd a b := by simp [mF, pullback.map]
    rw [hm, ← hf]
    exact (IsPullback.of_hasPullback a b).flip
  have hG : IsPullback mG (pullback.snd a' b) (pullback.snd a' b') g := by
    refine IsPullback.of_right ?_ (by simp [mG, pullback.map])
      (IsPullback.of_hasPullback a' b')
    have hm : mG ≫ pullback.fst a' b' = pullback.fst a' b := by simp [mG, pullback.map]
    rw [hm, ← hg]
    exact IsPullback.of_hasPullback a' b
  let : IsFinite mF := MorphismProperty.of_isPullback hF.flip inferInstance
  let : IsFinite mG := MorphismProperty.of_isPullback hG.flip inferInstance
  let : IsFinite m :=
    MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance hf hg
  have hcomp : mF ≫ mG = m := by
    apply pullback.hom_ext <;> simp [mF, mG, m, pullback.map, Category.assoc]
  let hrB := AlgebraicGeometry.RelativeDimension.of_isPullback
    (IsPullback.of_hasPullback a' b).flip (relativeDimension_of_isIntegral_over_field k b)
  let hrA := AlgebraicGeometry.RelativeDimension.of_isPullback
    (IsPullback.of_hasPullback a' b') (relativeDimension_of_isIntegral_over_field k a')
  have hleft := finiteCyclePushforward_wholeFundamentalCycle_of_flatBaseChange
    a' f hηf (pullback.fst a' b) (pullback.fst a b) mF hF.flip _ hrB
  have hright := finiteCyclePushforward_wholeFundamentalCycle_of_flatBaseChange
    b' g hηg (pullback.snd a' b') (pullback.snd a' b) mG hG.flip _ hrA
  change finiteCyclePushforward m (AlgebraicCycle.fundamentalCycle (pullback a b)) = _
  calc
    _ = finiteCyclePushforward (mF ≫ mG) (AlgebraicCycle.fundamentalCycle (pullback a b)) :=
      finiteCyclePushforward_congr _ _ hcomp.symm _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, hleft, map_zsmul, hright, smul_smul]

section ExteriorPrimes

variable {A B A' B' : Scheme.{u}}
  (a : A ⟶ Spec (.of k)) [LocallyOfFiniteType a] [QuasiCompact a]
  (b : B ⟶ Spec (.of k)) [LocallyOfFiniteType b] [QuasiCompact b]

local notation3 (prettyPrint := false) "ι(" x ")" => (integralComponentAt x).subschemeι

/-- The whole fundamental cycle of the literal product of the reduced point closures. -/
def exteriorPointCycle (x : A) (y : B) : AlgebraicCycle (pullback a b) ℤ :=
  letI := Scheme.isNoetherian_of_finiteType_of_isNoetherian
    (pullback.fst (ι(x) ≫ a) (ι(y) ≫ b) ≫ ι(x) ≫ a)
  letI : IsFinite (pullback.map (ι(x) ≫ a) (ι(y) ≫ b) a b ι(x) ι(y) (𝟙 (Spec (.of k)))
      (by simp) (by simp)) :=
    MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance rfl rfl
  finiteCyclePushforward (pullback.map (ι(x) ≫ a) (ι(y) ≫ b) a b ι(x) ι(y) (𝟙 (Spec (.of k)))
      (by simp) (by simp)) (AlgebraicCycle.fundamentalCycle _)

variable (a' : A' ⟶ Spec (.of k)) [LocallyOfFiniteType a'] [QuasiCompact a']
  (b' : B' ⟶ Spec (.of k)) [LocallyOfFiniteType b'] [QuasiCompact b']
  (f : A ⟶ A') [IsFinite f] (g : B ⟶ B') [IsFinite g]
  (hf : a = f ≫ a') (hg : b = g ≫ b')

/-- Finite pushforward of the literal exterior prime keeps both full residue-field degrees. -/
theorem finiteCyclePushforward_exteriorPointCycle (x : A) (y : B) :
    letI : IsFinite (pullback.map a b a' b' f g (𝟙 (Spec (.of k)))
        ((Category.comp_id _).trans hf) ((Category.comp_id _).trans hg)) :=
      MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance hf hg
    finiteCyclePushforward (pullback.map a b a' b' f g (𝟙 (Spec (.of k)))
        ((Category.comp_id _).trans hf) ((Category.comp_id _).trans hg))
        (exteriorPointCycle a b x y) =
      ((f.residueDegree x : ℤ) * (g.residueDegree y : ℤ)) •
        exteriorPointCycle a' b' (f x) (g y) := by
  let : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  let : IsIntegral (integralComponentAt y).subscheme := isIntegral_integralComponentAt y
  let : IsIntegral (integralComponentAt (f x)).subscheme := isIntegral_integralComponentAt (f x)
  let : IsIntegral (integralComponentAt (g y)).subscheme := isIntegral_integralComponentAt (g y)
  let fx := integralComponentMap f x
  let gy := integralComponentMap g y
  have hfx : fx ≫ ι(f x) = ι(x) ≫ f := integralComponentMap_subschemeι f x
  have hgy : gy ≫ ι(g y) = ι(y) ≫ g := integralComponentMap_subschemeι g y
  let : IsFinite fx := by
    have : IsFinite (fx ≫ ι(f x)) := by rw [hfx]; infer_instance
    exact IsFinite.of_comp fx ι(f x)
  let : IsFinite gy := by
    have : IsFinite (gy ≫ ι(g y)) := by rw [hgy]; infer_instance
    exact IsFinite.of_comp gy ι(g y)
  have hfx' : ι(x) ≫ a = fx ≫ (ι(f x) ≫ a') := by
    rw [← Category.assoc, hfx, Category.assoc, hf]
  have hgy' : ι(y) ≫ b = gy ≫ (ι(g y) ≫ b') := by
    rw [← Category.assoc, hgy, Category.assoc, hg]
  let m : pullback a b ⟶ pullback a' b' :=
    pullback.map a b a' b' f g (𝟙 _) ((Category.comp_id _).trans hf)
      ((Category.comp_id _).trans hg)
  let m' : pullback (ι(x) ≫ a) (ι(y) ≫ b) ⟶ pullback (ι(f x) ≫ a') (ι(g y) ≫ b') :=
    pullback.map _ _ _ _ fx gy (𝟙 _) ((Category.comp_id _).trans hfx')
      ((Category.comp_id _).trans hgy')
  let i : pullback (ι(x) ≫ a) (ι(y) ≫ b) ⟶ pullback a b :=
    pullback.map _ _ _ _ ι(x) ι(y) (𝟙 _) (by simp) (by simp)
  let j : pullback (ι(f x) ≫ a') (ι(g y) ≫ b') ⟶ pullback a' b' :=
    pullback.map _ _ _ _ ι(f x) ι(g y) (𝟙 _) (by simp) (by simp)
  let : IsFinite m :=
    MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance hf hg
  let : IsFinite m' :=
    MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance hfx' hgy'
  let : IsFinite i :=
    MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance rfl rfl
  let : IsFinite j := by
    dsimp only [j]
    exact MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance rfl rfl
  let : IsNoetherian (pullback (ι(x) ≫ a) (ι(y) ≫ b)) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (pullback.fst _ _ ≫ ι(x) ≫ a)
  let : IsNoetherian (pullback (ι(f x) ≫ a') (ι(g y) ≫ b')) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (pullback.fst _ _ ≫ ι(f x) ≫ a')
  have hsq : i ≫ m = m' ≫ j := by
    apply pullback.hom_ext <;> simp [i, j, m, m', pullback.map, Category.assoc, hfx, hgy]
  have hproduct := finiteCyclePushforward_product_of_integral
    (ι(x) ≫ a) (ι(y) ≫ b) (ι(f x) ≫ a') (ι(g y) ≫ b') fx gy hfx' hgy'
    (integralComponentMap_base_genericPoint f x) (integralComponentMap_base_genericPoint g y)
  change finiteCyclePushforward m
      (finiteCyclePushforward i (AlgebraicCycle.fundamentalCycle _)) =
    _ • finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle _)
  rw [finiteCyclePushforward_comp_apply]
  calc
    _ = finiteCyclePushforward (m' ≫ j) (AlgebraicCycle.fundamentalCycle _) :=
      finiteCyclePushforward_congr _ _ hsq _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, hproduct, map_zsmul,
        residueDegree_integralComponentMap f x, residueDegree_integralComponentMap g y]

end ExteriorPrimes

section CorrespondencePrime

variable (X Y U V : SmoothSite (Spec (.of k)))
  (z : pullback (C := Scheme) X.hom Y.hom)
  (w : pullback (C := Scheme) U.hom V.hom)
  (hz : IsFiniteCorrespondencePoint X.hom Y.hom z)
  (hw : IsFiniteCorrespondencePoint U.hom V.hom w)

local notation3 (prettyPrint := false) "a₀" => pullback.fst X.hom Y.hom ≫ X.hom
local notation3 (prettyPrint := false) "b₀" => pullback.fst U.hom V.hom ≫ U.hom

/-- The outer product of the actual correspondence ambients, with the middle factors exchanged. -/
abbrev correspondenceExteriorShuffle :
    pullback a₀ b₀ ≅ pullback (SmoothSite.product X U).hom (SmoothSite.product Y V).hom :=
  pullbackFourShuffleIso X.hom Y.hom U.hom V.hom

local notation3 (prettyPrint := false) "Ambient" =>
  pullback (SmoothSite.product X U).hom (SmoothSite.product Y V).hom

/-- The middle-factor shuffle carries the whole exterior prime to the native correspondence
prime, with the original closed supports and their generic multiplicities. -/
theorem finiteCyclePushforward_shuffle_exteriorPointCycle :
    (finiteCyclePushforward (correspondenceExteriorShuffle X Y U V).hom
      (exteriorPointCycle a₀ b₀ z w) : AlgebraicCycle Ambient ℤ) =
        (correspondenceExteriorPrime X Y U V z w hz hw).val := by
  let : IsFinite (exteriorSupportSourceProjection X Y (integralComponentAt z)) := hz.1
  let : IsFinite (exteriorSupportSourceProjection U V (integralComponentAt w)) := hw.1
  let az := (integralComponentAt z).subschemeι ≫ a₀
  let bw := (integralComponentAt w).subschemeι ≫ b₀
  let cz := exteriorSupportSourceProjection X Y (integralComponentAt z) ≫ X.hom
  let dw := exteriorSupportSourceProjection U V (integralComponentAt w) ≫ U.hom
  let j : pullback az bw ⟶ pullback a₀ b₀ :=
    pullback.map az bw a₀ b₀ (integralComponentAt z).subschemeι (integralComponentAt w).subschemeι
      (𝟙 _) (by simp [az]) (by simp [bw])
  let : IsFinite j := by
    dsimp only [j]
    exact MorphismProperty.pullbackMap (P := @IsFinite) inferInstance inferInstance rfl rfl
  let : IsNoetherian (pullback az bw) :=
    Scheme.isNoetherian_of_finiteType_of_isNoetherian (Y := Spec (.of k))
      (pullback.fst az bw ≫ az)
  let : IsNoetherian (pullback cz dw) :=
    correspondenceExteriorSupport_isNoetherian X Y U V z w hz hw
  have hcz : az = cz := (Category.assoc _ _ _).symm
  have hdw : bw = dw := (Category.assoc _ _ _).symm
  let e : pullback az bw ≅ pullback cz dw := pullback.congrHom hcz hdw
  let shuffle := correspondenceExteriorShuffle X Y U V
  let r := correspondenceExteriorInclusion X Y U V (integralComponentAt z) (integralComponentAt w)
  have he₁ : e.hom ≫ pullback.fst cz dw = pullback.fst az bw := by
    simp [e, pullback.congrHom_hom, pullback.map]
  have he₂ : e.hom ≫ pullback.snd cz dw = pullback.snd az bw := by
    simp [e, pullback.congrHom_hom, pullback.map]
  have hcomp : j ≫ shuffle.hom = e.hom ≫ r := by
    apply pullback.hom_ext (f := (SmoothSite.product X U).hom) (g := (SmoothSite.product Y V).hom)
    · simp only [Category.assoc, r, correspondenceExteriorInclusion_fst]
      apply pullback.hom_ext (f := X.hom) (g := U.hom)
      · simp only [Category.assoc, correspondenceExteriorSource_fst]
        change j ≫ (pullbackFourShuffleIso X.hom Y.hom U.hom V.hom).hom ≫
            pullback.fst (pullback.fst X.hom U.hom ≫ X.hom)
              (pullback.fst Y.hom V.hom ≫ Y.hom) ≫ pullback.fst X.hom U.hom =
          e.hom ≫ pullback.fst cz dw ≫ exteriorSupportSourceProjection X Y (integralComponentAt z)
        rw [pullbackFourShuffleIso_hom_fst_fst, reassoc_of% he₁]
        exact pullback.lift_fst_assoc _ _ _ _
      · simp only [Category.assoc, correspondenceExteriorSource_snd]
        change j ≫ (pullbackFourShuffleIso X.hom Y.hom U.hom V.hom).hom ≫
            pullback.fst (pullback.fst X.hom U.hom ≫ X.hom)
              (pullback.fst Y.hom V.hom ≫ Y.hom) ≫ pullback.snd X.hom U.hom =
          e.hom ≫ pullback.snd cz dw ≫ exteriorSupportSourceProjection U V (integralComponentAt w)
        rw [pullbackFourShuffleIso_hom_fst_snd, reassoc_of% he₂]
        exact pullback.lift_snd_assoc _ _ _ _
    · simp only [Category.assoc, r, correspondenceExteriorInclusion_snd]
      apply pullback.hom_ext (f := Y.hom) (g := V.hom)
      · simp only [Category.assoc, correspondenceExteriorTarget_fst]
        change j ≫ (pullbackFourShuffleIso X.hom Y.hom U.hom V.hom).hom ≫
            pullback.snd (pullback.fst X.hom U.hom ≫ X.hom)
              (pullback.fst Y.hom V.hom ≫ Y.hom) ≫ pullback.fst Y.hom V.hom =
          e.hom ≫ pullback.fst cz dw ≫ exteriorSupportTargetProjection X Y (integralComponentAt z)
        rw [pullbackFourShuffleIso_hom_snd_fst, reassoc_of% he₁]
        exact pullback.lift_fst_assoc _ _ _ _
      · simp only [Category.assoc, correspondenceExteriorTarget_snd]
        change j ≫ (pullbackFourShuffleIso X.hom Y.hom U.hom V.hom).hom ≫
            pullback.snd (pullback.fst X.hom U.hom ≫ X.hom)
              (pullback.fst Y.hom V.hom ≫ Y.hom) ≫ pullback.snd Y.hom V.hom =
          e.hom ≫ pullback.snd cz dw ≫ exteriorSupportTargetProjection U V (integralComponentAt w)
        rw [pullbackFourShuffleIso_hom_snd_snd, reassoc_of% he₂]
        exact pullback.lift_snd_assoc _ _ _ _
  rw [correspondenceExteriorPrime_val]
  change finiteCyclePushforward shuffle.hom
      (finiteCyclePushforward j (AlgebraicCycle.fundamentalCycle _)) =
    finiteCyclePushforward r (AlgebraicCycle.fundamentalCycle _)
  rw [finiteCyclePushforward_comp_apply]
  calc
    _ = finiteCyclePushforward (e.hom ≫ r) (AlgebraicCycle.fundamentalCycle _) :=
      finiteCyclePushforward_congr _ _ hcomp _
    _ = _ := by
      rw [← finiteCyclePushforward_comp_apply, finiteCyclePushforward_fundamentalCycle_iso]

end CorrespondencePrime

end Stacks.Chow
