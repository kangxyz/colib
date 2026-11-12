/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RelativeBase.CanonicalFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.FullGraphBoundaryFrame
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.BoundaryCoordinateUnit
public import Colib.AlgebraicGeometry.RelativeCurve.Pencils.RetainedSourceChange

/-!
# Genuine graph-coordinate transport for an arbitrary smooth relative curve

The target need not be a polynomial line. A native target graph frame transports
through the full original marked Cartesian square to the compactification graph.
Its coordinate gives the actual unit on the independent disjoint correction
source. The neighborhood producer constructs this intermediate frame.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Divisors
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase

variable {S X C Y Z A : Scheme.{u}} (q : X ⟶ S) (π : C ⟶ S) (j : Y ⟶ C)
  (p : Y ⟶ X) (hq : j ≫ π = p ≫ q) (z : Z ⟶ X)
  (s : Z ⟶ Y) (hs : s ≫ p = z)

include hq hs in
/-- The original structural map of the mark is unchanged by the coordinate presentation. -/
theorem markedBase_eq :
    s ≫ j ≫ π = z ≫ q := by
  rw [hq, ← Category.assoc, hs]

include hq hs in
/-- The actual map from the whole marked product to the original target-curve product. -/
def markedProductToTarget :
    pullback (j ≫ π) (s ≫ j ≫ π) ⟶
      pullback (q) (z ≫ q) :=
  pullback.lift (pullback.fst _ _ ≫ p) (pullback.snd _ _) (by
    rw [Category.assoc, ← hq, ← markedBase_eq q π j p hq z s hs]
    exact pullback.condition)

@[reassoc (attr := simp)]
theorem markedProductToTarget_fst :
    markedProductToTarget q π j p hq z s hs ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ p := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem markedProductToTarget_snd :
    markedProductToTarget q π j p hq z s hs ≫ pullback.snd _ _ =
      pullback.snd _ _ := pullback.lift_snd _ _ _

/-- The complete mark square induces a Cartesian square of the two literal graph schemes. -/
theorem markedGraphToTarget_isPullback
    (H : IsPullback s (𝟙 Z) p z) :
    IsPullback (𝟙 (Z)) (markedProductGraph π j s)
      (relativeBoundaryGraph q z) (markedProductToTarget q π j p hq z s hs) where
  w := by
    apply pullback.hom_ext <;>
      simp [markedProductGraph, relativeBoundaryGraph, markedProductToTarget, hs]
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun t => by
    have hc : (t.snd ≫ pullback.fst (j ≫ π) (s ≫ j ≫ π)) ≫ p =
        t.fst ≫ z := by
      have ht := congrArg (fun v => v ≫ pullback.fst (q)
        (z ≫ q)) t.condition
      simpa [relativeBoundaryGraph, markedProductToTarget] using ht.symm
    have hy : t.fst ≫ s = t.snd ≫ pullback.fst (j ≫ π) (s ≫ j ≫ π) := by
      have he := H.lift_snd (t.snd ≫ pullback.fst (j ≫ π) (s ≫ j ≫ π)) t.fst hc
      simp only [Category.comp_id] at he
      rw [← he]
      exact H.lift_fst _ _ hc
    refine ⟨t.fst, by simp, ?_, ?_⟩
    · apply pullback.hom_ext
      · change (t.fst ≫ markedProductGraph π j s) ≫ pullback.fst (j ≫ π) (s ≫ j ≫ π) = _
        rw [Category.assoc, markedProductGraph, pullback.lift_fst]
        exact hy
      · change (t.fst ≫ markedProductGraph π j s) ≫ pullback.snd (j ≫ π) (s ≫ j ≫ π) = _
        have ht := congrArg (fun v => v ≫ pullback.snd (q)
          (z ≫ q)) t.condition
        simpa [markedProductGraph, relativeBoundaryGraph, markedProductToTarget] using ht
    · intro v hv _
      simpa using hv)⟩


variable [IsSeparated q] [SmoothOfRelativeDimension 1 q] [IsSeparated π]
  [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ π)]
  (H : IsPullback s (𝟙 Z) p z)

include H in
omit [SmoothOfRelativeDimension 1 q] [IsSeparated π] [IsOpenImmersion j]
  [SmoothOfRelativeDimension 1 (j ≫ π)] in
/-- The actual marked graph ideal is the entire inverse image of the target graph ideal. -/
theorem markedTarget_ideal :
    (relativeBoundaryGraph q z).ker.comap (markedProductToTarget q π j p hq z s hs) =
      (markedProductGraph π j s).ker :=
  (ker_eq_comap_of_cartesian (markedGraphToTarget_isPullback q π j p hq z s hs H).flip).symm

variable (e : divisorSheaf (relativeBoundaryGraph q z).ker ≅
  SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf)

/-- The exact target graph coordinate in its constructed native frame. -/
def targetCoordinate : Γ(pullback q (z ≫ q), ⊤) :=
  e.hom.app ⊤ (divisorSheafGlobalSection (relativeBoundaryGraph q z).ker)

/-- The native compactification graph frame on the complete marked product. -/
def compactificationMarkedFrame :
    (Modules.pullback (markedProductMap π j s)).obj
      (divisorSheaf (compactificationGraph π j).ker) ≅
        SheafOfModules.unit (pullback (j ≫ π) (s ≫ j ≫ π)).ringCatSheaf := by
  haveI := compactificationGraphIdeal_isEffectiveCartierDivisor π j
  exact divisorComapEqIso (markedProductMap π j s) (compactificationGraph π j).ker
      (markedProductGraph π j s).ker (compactificationGraphIdeal_comap_markedProductMap π j s) ≪≫
    (divisorComapEqIso (markedProductToTarget q π j p hq z s hs)
      (relativeBoundaryGraph q z).ker (markedProductGraph π j s).ker
      (markedTarget_ideal q π j p hq z s hs H)).symm ≪≫
    Modules.framePullback (markedProductToTarget q π j p hq z s hs) e

/-- The transported frame preserves the actual canonical-section coordinate. -/
theorem compactificationMarkedFrame_coordinate :
    (compactificationMarkedFrame q π j p hq z s hs H e).hom.app ⊤
      (pullbackGlobalSections (markedProductMap π j s)
        (divisorSheaf (compactificationGraph π j).ker)
        (divisorSheafGlobalSection (compactificationGraph π j).ker)) =
      (markedProductToTarget q π j p hq z s hs).appTop (targetCoordinate q z e) := by
  have := compactificationGraphIdeal_isEffectiveCartierDivisor π j
  let f := markedProductToTarget q π j p hq z s hs
  let D := (relativeBoundaryGraph q z).ker
  let E := (markedProductGraph π j s).ker
  let i := divisorComapEqIso f D E (markedTarget_ideal q π j p hq z s hs H)
  have hi : i.inv.app ⊤ (divisorSheafGlobalSection E) =
      pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D) := by
    let t := pullbackGlobalSections f (divisorSheaf D) (divisorSheafGlobalSection D)
    have hs : i.hom.app ⊤ t = divisorSheafGlobalSection E :=
      divisorComapEqIso_canonicalSection f D E (markedTarget_ideal q π j p hq z s hs H)
    have he := congrArg (fun m => m.app ⊤ t) i.hom_inv_id
    exact (congrArg (fun x => i.inv.app ⊤ x) hs).symm.trans he
  change (Modules.framePullback f e).hom.app ⊤
    (i.inv.app ⊤ ((divisorComapEqIso (markedProductMap π j s)
      (compactificationGraph π j).ker E
      (compactificationGraphIdeal_comap_markedProductMap π j s)).hom.app ⊤
      (pullbackGlobalSections (markedProductMap π j s)
        (divisorSheaf (compactificationGraph π j).ker)
        (divisorSheafGlobalSection (compactificationGraph π j).ker)))) = _
  rw [divisorComapEqIso_canonicalSection, hi, Modules.framePullback_coordinate]
  rfl

variable (a : A ⟶ X) (ha : Disjoint (Set.range a) (Set.range z))

/-- The independent correction product changes the first factor only. -/
abbrev correctionProductToTarget : pullback (a ≫ q) (z ≫ q) ⟶ pullback q (z ≫ q) :=
  retainedSourceChange q (a ≫ q) (z ≫ q) a rfl

include ha in
omit [SmoothOfRelativeDimension 1 q] in
/-- The correction product is disjoint from the whole target graph. -/
theorem correctionProduct_disjoint_graph :
    Disjoint (Set.range (correctionProductToTarget q z a))
      ((relativeBoundaryGraph q z).ker.support : Set (pullback q (z ≫ q) : Scheme)) := by
  rw [Scheme.Hom.support_ker,
    (IsClosedImmersion.isClosedEmbedding (relativeBoundaryGraph q z)).isClosed_range.closure_eq]
  apply Set.disjoint_left.mpr
  rintro t ⟨w, rfl⟩ ⟨b, hb⟩
  apply Set.disjoint_left.mp ha ⟨pullback.fst (a ≫ q) (z ≫ q) w, rfl⟩
  refine ⟨b, ?_⟩
  have hh := congrArg (fun x => pullback.fst q (z ≫ q) x) hb
  simpa only [← Scheme.Hom.comp_apply, relativeBoundaryGraph_fst,
    correctionProductToTarget, retainedSourceChange_fst] using hh

/-- The actual coordinate on the entire correction product. -/
def correctionCoordinate : Γ(pullback (a ≫ q) (z ≫ q), ⊤) :=
  (correctionProductToTarget q z a).appTop (targetCoordinate q z e)

/-- The genuine scalar automorphism; its unit property follows from disjointness. -/
def correctionUnit :
    SheafOfModules.unit (pullback (a ≫ q) (z ≫ q)).ringCatSheaf ≅
      SheafOfModules.unit (pullback (a ≫ q) (z ≫ q)).ringCatSheaf :=
  boundaryCoordinateUnit (relativeBoundaryGraph q z).ker (correctionProductToTarget q z a)
    (correctionProduct_disjoint_graph q z a ha)
    (Modules.framePullback (correctionProductToTarget q z a) e)

@[simp]
theorem correctionUnit_coordinate :
    Modules.Hom.app (X := pullback (a ≫ q) (z ≫ q)) (correctionUnit q z e a ha).hom ⊤
      (1 : Γ((pullback (a ≫ q) (z ≫ q) : Scheme), ⊤)) = correctionCoordinate q z e a := by
  let f := correctionProductToTarget q z a
  let D := (relativeBoundaryGraph q z).ker
  exact (boundaryCoordinateUnit_coordinate D f (correctionProduct_disjoint_graph q z a ha)
    (Modules.framePullback f e)).trans
      (Modules.framePullback_coordinate f e (divisorSheafGlobalSection D))

end AlgebraicGeometry.Scheme.RelativeCurvePencil.RelativeBase
