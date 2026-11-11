/-
Copyright (c) 2026 Colib contributors and Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Colib.AlgebraicGeometry.Chow.FiniteFlatFundamental
public import Colib.AlgebraicGeometry.Correspondences.Graph.Functor
public import Colib.AlgebraicGeometry.Sites.Smooth.Noetherian

/-!
# Actual finite flat spans

A span with finite flat left leg determines a signed finite correspondence by
pushing its whole fundamental cycle to the source-first ambient product.
Finiteness over the smooth source supplies Noetherianness. No integral or
reduced hypothesis is imposed on the span scheme. The identity-left span is
the actual full graph, including disconnected and empty sources.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Chow
open AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Cor

variable {k : Type u} [Field k] {X Y : SmoothSite (Spec (.of k))} {A : Scheme.{u}}

/-- Separatedness of the target makes the span map finite over its finite source leg. -/
theorem isFinite_spanMap (f : A ⟶ X.left) [IsFinite f] (g : A ⟶ Y.left)
    (h : f ≫ X.hom = g ≫ Y.hom) : IsFinite (pullback.lift f g h) := by
  have : IsFinite (pullback.lift f g h ≫ pullback.fst X.hom Y.hom) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsFinite.of_comp _ (pullback.fst X.hom Y.hom)

/-- The native correspondence of the whole actual finite flat span. -/
def ofFiniteFlatSpan (f : A ⟶ X.left) [IsFinite f] [Flat f]
    (g : A ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom) : Cor.mk X ⟶ Cor.mk Y := by
  letI : IsNoetherian A := isNoetherian_of_finiteType f
  letI : IsFinite (pullback.lift f g h) := isFinite_spanMap f g h
  letI : IsFinite (pullback.lift f g h ≫ pullback.fst X.hom Y.hom) := by
    simpa only [pullback.lift_fst] using (inferInstance : IsFinite f)
  letI : Flat (pullback.lift f g h ≫ pullback.fst X.hom Y.hom) := by
    simpa only [pullback.lift_fst] using (inferInstance : Flat f)
  exact finiteFlatSpanFundamental X.hom Y.hom (pullback.lift f g h)

/-- Its value is the genuine finite pushforward, with every generic stalk length. -/
theorem ofFiniteFlatSpan_val [IsNoetherian A]
    (f : A ⟶ X.left) [IsFinite f] [Flat f]
    (g : A ⟶ Y.left) (h : f ≫ X.hom = g ≫ Y.hom) :
    letI := isFinite_spanMap f g h
    (ofFiniteFlatSpan f g h).val =
      finiteCyclePushforward (pullback.lift f g h) (AlgebraicCycle.fundamentalCycle A) := rfl

/-- An identity-left span is the existing full graph correspondence. -/
theorem ofFiniteFlatSpan_id_left (a : X ⟶ Y) :
    ofFiniteFlatSpan (𝟙 X.left) a.left (by simp) =
      (graphFunctor k).map a := by
  letI : IsReduced ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
    inferInstanceAs (IsReduced (Spec (.of k)))
  letI : IsLocallyNoetherian ((Functor.fromPUnit (Spec (.of k))).obj X.right) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))
  letI : IsNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsNoetherian X.left)
  have : GeometricallyReduced X.hom := geometricallyReduced_of_smooth _
  letI : IsReduced ((𝟭 Scheme).obj X.left) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian X.hom
  apply Subtype.ext
  exact finiteCyclePushforward_fundamentalCycle_graph X.hom Y.hom a.left
    (MorphismProperty.Over.w a)

/-- The literal diagonal span is the identity on the original object. -/
theorem ofFiniteFlatSpan_id (X : SmoothSite (Spec (.of k))) :
    ofFiniteFlatSpan (𝟙 X.left) (𝟙 X.left) (by simp) = 𝟙 (Cor.mk X) := by
  simpa using ofFiniteFlatSpan_id_left (𝟙 X)

end AlgebraicGeometry.Cor
