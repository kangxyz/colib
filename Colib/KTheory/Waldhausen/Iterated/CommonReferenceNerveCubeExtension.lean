/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Colib.KTheory.Waldhausen.Iterated.CommonReferenceNerveCompactFamily
public import Colib.Topology.ClassifyingSpace.Contraction
public import Colib.Topology.HELP.Nullhomotopic
public import Colib.Topology.Realization.SimplexCubeFaces

/-!
# Exact extension of actual common-reference boundaries

The canonical full reference node contracts its codiscrete nerve. The existing HEP theorem
then extends every actual continuous cube boundary exactly, including the empty zero-boundary.
Only isomorphism-reference diagrams are covered; compatibility of prescribed faces is not
inferred from their underlying functors or their induced K-maps.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Waldhausen Convexity Topology SSet
open scoped Simplicial Topology unitInterval
universe u
namespace CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
variable {V W : WideSubcategory SmallWaldhausenCategory.preservesZero.{u}} (F : V ⟶ W)

/-- The contraction is on the identical nerve realization used by compact evaluation. -/
def referenceContraction :
    (ContinuousMap.const |nerve (Codiscrete (Node F))|
      (classifyingSpacePoint (referenceNode F))).Homotopy
      (ContinuousMap.id |nerve (Codiscrete (Node F))|) :=
  classifyingSpaceInitialContraction (referenceNodeInitial F)

/-- Every actual boundary map has an exact extension; all dimensions are retained. -/
theorem exists_cube_extension (d : ℕ)
    (b : C({z : Fin d → I // z ∈ Cube.boundary (Fin d)},
      |nerve (Codiscrete (Node F))|)) :
    ∃ E : C(Fin d → I, |nerve (Codiscrete (Node F))|),
      E.restrict (Cube.boundary (Fin d)) = b := by
  let b' : C(CubicalTests.boundary.{u} d, |nerve (Codiscrete (Node F))|) :=
    b.comp ⟨CubicalTests.boundaryULiftHomeomorph d,
      (CubicalTests.boundaryULiftHomeomorph d).continuous⟩
  have hb : b'.Nullhomotopic :=
    ⟨classifyingSpacePoint (referenceNode F),
      ⟨(referenceContraction F).symm.compContinuousMap b'⟩⟩
  obtain ⟨E, hE⟩ := Topology.exists_extend_of_nullhomotopic
    (CubicalTests.boundaryInclusion d) (CubicalTests.boundaryInclusion_hep d) b' hb
  refine ⟨E.comp ⟨ULift.up, continuous_uliftUp⟩, ?_⟩
  ext z
  exact DFunLike.congr_fun hE ⟨⟨z.val⟩, z.property⟩

/-- A chosen extension of the specified whole boundary, without modifying it. -/
def cubeExtension (d : ℕ)
    (b : C({z : Fin d → I // z ∈ Cube.boundary (Fin d)},
      |nerve (Codiscrete (Node F))|)) :
    C(Fin d → I, |nerve (Codiscrete (Node F))|) :=
  (exists_cube_extension F d b).choose

/-- The complete original boundary is recovered literally. -/
theorem cubeExtension_restrict (d : ℕ)
    (b : C({z : Fin d → I // z ∈ Cube.boundary (Fin d)},
      |nerve (Codiscrete (Node F))|)) :
    (cubeExtension F d b).restrict (Cube.boundary (Fin d)) = b :=
  (exists_cube_extension F d b).choose_spec

/-- Compact evaluation depends on the actual nerve point, with its full reference data. -/
theorem compactFamily_of_point_eq
    {T U : Type*} [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace U] [CompactSpace U]
    (p : C(T, |nerve (Codiscrete (Node F))|))
    (q : C(U, |nerve (Codiscrete (Node F))|))
    (s : T) (t : U) (h : p s = q t) (n : ℕ) (x : (prespectrum V).space n) :
    compactPrespectrumFamily F p n (s, x) = compactPrespectrumFamily F q n (t, x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter F (q t)
  exact (compactPrespectrumFamily_eq_simplex F p N s z (h.trans hz.symm) n x).trans
    (compactPrespectrumFamily_eq_simplex F q N t z hz.symm n x).symm

/-- Precomposition changes only the compact parameter, at every original level. -/
theorem compactFamily_precomp
    {T U : Type*} [TopologicalSpace T] [CompactSpace T]
    [TopologicalSpace U] [CompactSpace U]
    (p : C(T, |nerve (Codiscrete (Node F))|)) (q : C(U, T))
    (n : ℕ) (t : U) (x : (prespectrum V).space n) :
    compactPrespectrumFamily F (p.comp q) n (t, x) =
      compactPrespectrumFamily F p n (q t, x) :=
  compactFamily_of_point_eq F (p.comp q) p t (q t) rfl n x

/-- Glue six actual carrier faces using their twelve complete edge identities. -/
def gluedCubeBoundary
    (f : ∀ a : Fin 3 × Bool,
      C(SimplexCubeExtension.face a, |nerve (Codiscrete (Node F))|))
    (hf : SimplexCubeExtension.EdgeCompatible (fun a ↦ f a)) :
    C(SimplexCubeExtension.boundary, |nerve (Codiscrete (Node F))|) :=
  SimplexCubeExtension.glueClosedCover _ SimplexCubeExtension.isClosed_face
    SimplexCubeExtension.faces_cover f
    (SimplexCubeExtension.edgeCompatible_pairwise (fun a ↦ f a) hf)

/-- The chosen filling starts only after the whole prescribed boundary has been glued. -/
def fillCubeFaces
    (f : ∀ a : Fin 3 × Bool,
      C(SimplexCubeExtension.face a, |nerve (Codiscrete (Node F))|))
    (hf : SimplexCubeExtension.EdgeCompatible (fun a ↦ f a)) :
    C(Fin 3 → I, |nerve (Codiscrete (Node F))|) :=
  cubeExtension F 3 (gluedCubeBoundary F f hf)

/-- Every point of every prescribed face is unchanged. -/
theorem fillCubeFaces_face
    (f : ∀ a : Fin 3 × Bool,
      C(SimplexCubeExtension.face a, |nerve (Codiscrete (Node F))|))
    (hf : SimplexCubeExtension.EdgeCompatible (fun a ↦ f a))
    (a : Fin 3 × Bool) (x : SimplexCubeExtension.face a) :
    fillCubeFaces F f hf x.val.val = f a x := by
  exact (DFunLike.congr_fun
    (cubeExtension_restrict F 3 (gluedCubeBoundary F f hf)) x.val).trans
    (SimplexCubeExtension.glueClosedCover_apply _ _ _ f
      (SimplexCubeExtension.edgeCompatible_pairwise (fun a ↦ f a) hf) a x)

end CategoryTheory.Waldhausen.IteratedS.CommonReferenceNerve
