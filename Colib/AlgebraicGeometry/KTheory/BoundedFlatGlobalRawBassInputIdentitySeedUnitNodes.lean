/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.AlgebraicGeometry.KTheory.BoundedFlatGlobalRawBassInputIdentitySeedUnitSimplex
public import Colib.KTheory.Waldhausen.Iterated.ModelReferenceReanchor
public import Colib.KTheory.Waldhausen.Iterated.SimplexPathEmbedding
public import Colib.KTheory.Waldhausen.Iterated.UnitPrismParameters

/-!
# The ten chosen references of the global Laurent unit pair

The actual scheme-square equality transports the new family to the original old reference.
The two complete source nodes, including their scalar automorphisms, are identified using
the actual pulled-back Laurent unit. Both original six-node families are then whole faces.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity Topology
open Topology.LoopPrespectrum
open AlgebraicGeometry.RingedSpace Scheme.PolynomialLaurent.GlobalIndex
open CategoryTheory.Waldhausen.IteratedS CategoryTheory.Waldhausen.IteratedS.SimplexParameters
open scoped Simplicial Topology unitInterval

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedUnitNodes

open InputIdentitySeedUnitSimplex
open CategoryTheory.Waldhausen.SmallWaldhausenCategory

local notation "WC" => BoundedFlatPerfectTripleSimplex.structureOn

private def sourceAt {X Y : Scheme.{u}} (f : X ⟶ Y) :
    asSmallCategory (WC Y) ⟶ asSmallCategory (WC X) :=
  asSmallCategoryMap (WC Y) (WC X) (boundedAboveFlatPerfectNormalizedPullback_exact f)
    (boundedAboveFlatPerfectNormalizedPullback_obj_zero f)

private def unitAt {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ) :
    (sourceAt f).hom.toFunctor ≅ (sourceAt f).hom.toFunctor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    ((boundedAboveFlatPerfectPullbackNormalizationIso f).symm ≪≫
      boundedAboveFlatPerfectPullbackUnitIso f r ≪≫
      boundedAboveFlatPerfectPullbackNormalizationIso f) AsSmall.up)

private theorem unit_transport {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) (r : (Γ(X, ⊤))ˣ) :
    unitAt f r ≪≫ eqToIso (congrArg (fun q ↦ (sourceAt q).hom.toFunctor) h) =
      eqToIso (congrArg (fun q ↦ (sourceAt q).hom.toFunctor) h) ≪≫ unitAt g r := by
  subst g
  simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans]

private theorem source_unit_node_eq {V T : WideSubcategory preservesZero.{u}} {F G : V ⟶ T}
    (h : F.hom.toFunctor = G.hom.toFunctor) (α : F.hom.toFunctor ≅ F.hom.toFunctor)
    (β : G.hom.toFunctor ≅ G.hom.toFunctor)
    (he : α ≪≫ eqToIso h = eqToIso h ≪≫ β) :
    (⟨F, α⟩ : Σ H : V ⟶ T, F.hom.toFunctor ≅ H.hom.toFunctor) =
      ⟨G, eqToIso h ≪≫ β⟩ := by
  apply ModelSimplex.reference_node_eq h
  exact congrArg Iso.hom he

private theorem precomp_simplex_nodes {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : (Γ(X, ⊤))ˣ) :
    ModelSimplex.ofIsos (BoundedFlatPerfectBinarySimplex.sourceMap f g)
      (fun i ↦ (UnitTrackPrecompSimplex.nodes f g r i).1)
      (fun i ↦ (UnitTrackPrecompSimplex.nodes f g r i).2) =
        UnitTrackPrecompSimplex.simplex f g r := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original old composite is the common reference, without choosing a new anchor. -/
abbrev source := BoundedFlatPerfectBinarySimplex.sourceMap
  (laurent.map g) (laurentProjection.app Y)

/-- The precise original scheme-square equality identifies the two reference functors. -/
theorem source_eq : (source g).hom.toFunctor =
    (BoundedFlatPerfectBinarySimplex.sourceMap (laurentProjection.app X) g).hom.toFunctor :=
  congrArg (fun q ↦ (sourceAt q).hom.toFunctor)
    (laurentProjection.naturality g)

/-- This equality-induced isomorphism is the only reanchoring used on the new family. -/
def sourceIso := eqToIso (source_eq g)

/-- A model-map node with an isomorphism from the original Laurent unit reference. -/
abbrev Node := Σ F : asSmallCategory (WC Y) ⟶
    asSmallCategory (WC (laurent.obj X)),
    (source g).hom.toFunctor ≅ F.hom.toFunctor

/-- All six original old nodes retain their actual reference isomorphisms. -/
def oldNodes := UnitTrackPostcompSimplex.nodes
  (laurent.map g) (laurentProjection.app Y)
  (laurentScalar (op Y))

/-- All six original new nodes, before applying the actual source equality. -/
def newNativeNodes := UnitTrackPrecompSimplex.nodes
  (laurentProjection.app X) g
  (laurentScalar (op X))

/-- Reanchoring retains the full new node, including its original reference isomorphism. -/
def newNodes : Fin 6 → Node g :=
  ModelSimplex.reanchorNodes (sourceIso g) (newNativeNodes g)

/-- The common source is an equality of complete dependent nodes. -/
theorem source_node_join : oldNodes g 0 = newNodes g 0 := by
  apply ModelSimplex.reference_node_eq (source_eq g)
  change (𝟙 _) ≫ eqToHom (source_eq g) = (sourceIso g ≪≫ Iso.refl _).hom
  simp only [sourceIso, Iso.trans_hom, Iso.refl_hom, eqToIso.hom,
    Category.id_comp, Category.comp_id]

/-- The actual unit equality and scheme-square transport commute on full source references. -/
theorem source_unit_reference :
    UnitTrackPostcompSimplex.sourceUnit
        (laurent.map g) (laurentProjection.app Y)
        (laurentScalar (op Y)) ≪≫ sourceIso g =
      sourceIso g ≪≫ UnitTrackPrecompSimplex.sourceUnit
        (laurentProjection.app X) g
        (laurentScalar (op X)) := by
  change unitAt _ (Units.map
      (laurent.map g).appTop.hom.toMonoidHom
      (laurentScalar (op Y))) ≪≫
      eqToIso (congrArg (fun q ↦ (sourceAt q).hom.toFunctor)
        (laurentProjection.naturality g)) =
    eqToIso (congrArg (fun q ↦ (sourceAt q).hom.toFunctor)
      (laurentProjection.naturality g)) ≪≫ unitAt _ _
  rw [laurentUnit_map]
  exact unit_transport (laurentProjection.naturality g) _

/-- The unit-shifted source also joins as a full dependent reference node. -/
theorem source_unit_node_join : oldNodes g 3 = newNodes g 3 :=
  source_unit_node_eq (source_eq g) _ _ (source_unit_reference g)

/-- Ten representatives retain both raw normalization intermediates and every shifted reference. -/
def nodes : Fin 10 → Node g :=
  ![oldNodes g 0, oldNodes g 1, oldNodes g 2, newNodes g 1, newNodes g 2,
    oldNodes g 3, oldNodes g 4, oldNodes g 5, newNodes g 4, newNodes g 5]

/-- The complete old six-node order embeds in the common ten-node order. -/
def oldFace : ⦋5⦌ ⟶ ⦋9⦌ := SimplexCategory.Hom.mk ⟨![0, 1, 2, 5, 6, 7], by decide⟩

/-- The complete new six-node order embeds separately in that same order. -/
def newFace : ⦋5⦌ ⟶ ⦋9⦌ := SimplexCategory.Hom.mk ⟨![0, 3, 4, 5, 8, 9], by decide⟩

/-- The old embedding keeps all six exact nodes. -/
theorem old_nodes (i : Fin 6) : nodes g (oldFace.toOrderHom i) = oldNodes g i := by
  fin_cases i <;> rfl

/-- The new embedding uses only the two proved complete-node joins. -/
theorem new_nodes (i : Fin 6) : nodes g (newFace.toOrderHom i) = newNodes g i := by
  fin_cases i
  · exact source_node_join g
  · rfl
  · rfl
  · exact source_unit_node_join g
  · rfl
  · rfl

/-- The actual ten-node common-reference simplex. -/
@[colib_ref "quillen"
  "Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/\
    GlobalRawBassInputIdentitySeedUnitNodes.lean:95-166"
  "adaptation" "Both original normalized Laurent-unit prisms in their ten full reference nodes"]
def simplex : ModelSimplex (asSmallCategory (WC Y))
    (asSmallCategory (WC (laurent.obj X))) 9 :=
  ModelSimplex.ofIsos (source g) (fun i ↦ (nodes g i).1) (fun i ↦ (nodes g i).2)

/-- Reanchoring preserves the entire original new six-node diagram. -/
theorem new_reference : ModelSimplex.ofIsos (source g)
    (fun i ↦ (newNodes g i).1) (fun i ↦ (newNodes g i).2) = newSimplex g :=
  (ModelSimplex.reanchorSimplex_eq (sourceIso g) (newNativeNodes g)).trans
    (precomp_simplex_nodes (laurentProjection.app X) g
      (laurentScalar (op X)))

/-- The full old diagram, rather than just its endpoint maps, is an ordered face. -/
theorem old_face : (simplex g).face oldFace = oldSimplex g := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact ModelSimplex.ofIsos_nodes_congr _ _ (old_nodes g)

/-- The full reanchored new diagram is the other ordered face. -/
theorem new_face : (simplex g).face newFace = newSimplex g := by
  unfold simplex
  rw [ModelSimplex.ofIsos_face]
  exact (ModelSimplex.ofIsos_nodes_congr _ _ (new_nodes g)).trans (new_reference g)

/-- Lower old binary route; its unit-shifted copy has different reference nodes. -/
abbrev C0 := binaryPath (k := 9) 0 1 2
/-- Unit-shifted old binary route. -/
abbrev C1 := binaryPath (k := 9) 5 6 7
/-- Lower new binary route. -/
abbrev D0 := binaryPath (k := 9) 0 3 4
/-- Unit-shifted new binary route, kept separately from D0. -/
abbrev D1 := binaryPath (k := 9) 5 8 9
/-- Common source-unit edge between the two distinct source references. -/
abbrev U := edge (k := 9) 0 5
/-- Actual old terminal-unit edge. -/
abbrev V := edge (k := 9) 2 7
/-- Actual new terminal-unit edge. -/
abbrev W := edge (k := 9) 4 9

/-- The original five-piece old parameter, with its two binary routes kept distinct. -/
def oldParameter : (C0.trans V).Homotopy (U.trans C1) :=
  Path.Homotopy.mapOfPaths (embed oldFace) UnitPrismParameters.parameter _ _
    (map_trans_values _ _ _ _ _ (map_binaryPath oldFace 0 1 2) (map_edge oldFace 2 5))
    (map_trans_values _ _ _ _ _ (map_edge oldFace 0 3) (map_binaryPath oldFace 3 4 5))

/-- The original five-piece new parameter, with its own lower and shifted binary routes. -/
def newParameter : (D0.trans W).Homotopy (U.trans D1) :=
  Path.Homotopy.mapOfPaths (embed newFace) UnitPrismParameters.parameter _ _
    (map_trans_values _ _ _ _ _ (map_binaryPath newFace 0 1 2) (map_edge newFace 2 5))
    (map_trans_values _ _ _ _ _ (map_edge newFace 0 3) (map_binaryPath newFace 3 4 5))

private theorem face_lift {V T : WideSubcategory preservesZero.{u}} {k l : ℕ}
    (S : ModelSimplex V T k) (Sface : ModelSimplex V T l)
    (α : ⦋l⦌ ⟶ ⦋k⦌) (hface : S.face α = Sface)
    {a b : StdSimplex ℝ (Fin (l + 1))} {p q : Path a b} (J : p.Homotopy q)
    {a' b' : StdSimplex ℝ (Fin (k + 1))} {p' q' : Path a' b'}
    (J' : p'.Homotopy q') (hj : ∀ r s, J' (r, s) = embed α (J (r, s)))
    {f h : prespectrum V ⟶ prespectrum T} {H K : Homotopy f h}
    (M : H.RelHomotopy K) (hlift : HomotopyLift Sface J M) : HomotopyLift S J' M := by
  intro n r s x
  rw [hj]
  exact (prespectrumSimplexFamily_face S α n (J (r, s)) x).trans
    ((congrArg (fun R ↦ prespectrumSimplexFamily R n (J (r, s), x)) hface).trans
      (hlift n r s x))

/-- The whole existing oldComparison is the old face of the common family. -/
theorem old_comparison_lift : HomotopyLift (simplex g) oldParameter
    (InputUnit.oldComparison g) :=
  face_lift (simplex g) (oldSimplex g) oldFace (old_face g)
    UnitPrismParameters.parameter oldParameter (fun _ _ ↦ rfl)
    (InputUnit.oldComparison g) (InputIdentitySeedUnitSimplex.old_comparison_lift g)

/-- The whole existing newComparison retains its actual transport in the other face. -/
theorem new_comparison_lift : HomotopyLift (simplex g) newParameter
    (InputUnit.newComparison g) :=
  face_lift (simplex g) (newSimplex g) newFace (new_face g)
    UnitPrismParameters.parameter newParameter (fun _ _ ↦ rfl)
    (InputUnit.newComparison g) (InputIdentitySeedUnitSimplex.new_comparison_lift g)

/-- C0 realizes the actual old composition track. -/
theorem C0_native : PathLift (simplex g) C0
    (InputUnit.oldComposition g) :=
  PathLift.trans_left _ (HomotopyLift.source _ (old_comparison_lift g))

/-- C1 realizes that same native track through its distinct shifted reference nodes. -/
theorem C1_native : PathLift (simplex g) C1
    (InputUnit.oldComposition g) :=
  PathLift.trans_right _ (HomotopyLift.target _ (old_comparison_lift g))

/-- D0 realizes the actual new composition, including its original endpoint cast. -/
theorem D0_native : PathLift (simplex g) D0
    (InputUnit.newComposition g) :=
  PathLift.trans_left _ (HomotopyLift.source _ (new_comparison_lift g))

/-- D1 retains its distinct shifted references and the same original new native track. -/
theorem D1_native : PathLift (simplex g) D1
    (InputUnit.newComposition g) :=
  PathLift.trans_right _ (HomotopyLift.target _ (new_comparison_lift g))

/-- The common forward unit retains the two distinct source references. -/
theorem U_native : PathLift (simplex g) U (InputUnit.commonUnit g) :=
  PathLift.trans_left _ (HomotopyLift.target _ (old_comparison_lift g))

/-- The old terminal edge is the actual postcomposed forward Laurent unit. -/
theorem V_native : PathLift (simplex g) V (InputUnit.oldUnit g) :=
  PathLift.trans_right _ (HomotopyLift.source _ (old_comparison_lift g))

/-- The new terminal edge is the actual precomposed forward Laurent unit. -/
theorem W_native : PathLift (simplex g) W (InputUnit.newUnit g) :=
  PathLift.trans_right _ (HomotopyLift.source _ (new_comparison_lift g))

/-- The lower route retains the original Laurent movement and its endpoint transport. -/
theorem lower_movement_native : PathLift (simplex g) (C0.symm.trans D0)
    (laurentSquareHomotopy g) := by
  intro n s x
  rw [laurentSquareHomotopy_level]
  exact PathLift.trans (simplex g) (PathLift.symm _ (C0_native g))
    (D0_native g) n s x

/-- The shifted reference route recovers that same whole native Laurent movement. -/
theorem shifted_movement_native : PathLift (simplex g) (C1.symm.trans D1)
    (laurentSquareHomotopy g) := by
  intro n s x
  rw [laurentSquareHomotopy_level]
  exact PathLift.trans (simplex g) (PathLift.symm _ (C1_native g))
    (D1_native g) n s x

end AlgebraicGeometry.Scheme.Modules.GlobalRawBass.InputIdentitySeedUnitNodes
