import PfaffianDescent.GrassmannianFrameProjectiveTransition
import PfaffianDescent.GrassmannianFrameParameterTransition
import PfaffianDescent.GrassmannianScheme
import AllCharacteristics.OverlapCompositionGluing
import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the projective Grassmannian-frame charts

The pairwise projective frame transitions are lifted over the existing
Grassmannian triple intersections.  The projective coefficient square is
Cartesian, so the base triple-overlap map and the map into the next local
projective chart determine the required third-overlap crossing uniquely.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

variable (K : Type u) [CommRing K] {m n : ℕ}
variable {τ : Type} [Finite τ] (d : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false

/-- The universal graph matrix on the common affine model of every standard
Grassmannian chart. -/
noncomputable def grassmannianFrameChartUniversalMatrix :
    Matrix (Fin n) (Fin m) (GrassmannianChartRing K m n) :=
  fun a b => MvPolynomial.X (a, b)

/-- The local projective-frame chart embedded in the ambient projective
space of degree-`d` equations over `K`. -/
noncomputable def grassmannianFrameProjectiveChartToGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d)
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveChartSpace K m n ⟶ projectiveParameters K τ d :=
  grassmannianChartHomogeneousFrameToGlobalParameters d
    (algebraMap K (GrassmannianChartRing K m n)) e i
    (grassmannianFrameChartUniversalMatrix K)

/-- The second inclusion of a projective-frame overlap, obtained by changing
frame coordinates and then entering the opposite local chart. -/
noncomputable def grassmannianFrameProjectiveAtlasRight
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveOverlapSpace K i j ⟶
      grassmannianFrameProjectiveChartSpace K m n :=
  grassmannianFrameProjectiveAtlasTransition K d e i j ≫
    grassmannianFrameProjectiveAtlasι K j i

/-- The projective right-overlap map lies above the corresponding right map
of the Grassmannian atlas. -/
theorem grassmannianFrameProjectiveAtlasRight_toBase
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasRight K d e i j ≫
      toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) =
    toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m)
          (GrassmannianOverlapRing K (grassmannianChartChange i j)))) ≫
      grassmannianAtlasTransition K i j ≫ grassmannianAtlasι K j i := by
  unfold grassmannianFrameProjectiveAtlasRight
  rw [Category.assoc, grassmannianFrameProjectiveAtlasι_toBase]
  exact congrArg (fun q => q ≫ grassmannianAtlasι K j i)
    (grassmannianFrameProjectiveAtlasTransition_toBase K d e i j)

/-- Restricting a chart's ambient equation map to an overlap is the same as
forming that equation map directly over the localized coefficient ring. -/
theorem grassmannianFrameProjectiveAtlasι_toGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasι K i j ≫
      grassmannianFrameProjectiveChartToGlobalParameters K d e i =
    grassmannianChartHomogeneousFrameToGlobalParameters d
      (algebraMap K
        (GrassmannianOverlapRing K (grassmannianChartChange i j))) e i
      (grassmannianOverlapUniversalMatrix K (grassmannianChartChange i j)) := by
  let A := GrassmannianChartRing K m n
  let B := GrassmannianOverlapRing K (grassmannianChartChange i j)
  let a : A →+* B := algebraMap A B
  let b : K →+* A := algebraMap K A
  let c : K →+* B := algebraMap K B
  have hT : (grassmannianFrameChartUniversalMatrix K).map a =
      grassmannianOverlapUniversalMatrix K (grassmannianChartChange i j) := by
    rfl
  have hcomp : a.comp b = c := by
    apply RingHom.ext
    intro x
    exact (IsScalarTower.algebraMap_apply K A B x).symm
  have hn := grassmannianChartHomogeneousFrameToGlobalParameters_naturality
    (R := A) d b a e i (grassmannianFrameChartUniversalMatrix K)
  unfold grassmannianFrameProjectiveAtlasι
    grassmannianFrameProjectiveChartToGlobalParameters
  simpa only [hT, hcomp] using hn

/-- The right overlap map represents the same ambient equation as the left
overlap map, after its frame and coefficient changes. -/
theorem grassmannianFrameProjectiveAtlasRight_toGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasRight K d e i j ≫
      grassmannianFrameProjectiveChartToGlobalParameters K d e j =
    grassmannianChartHomogeneousFrameToGlobalParameters d
      (algebraMap K
        (GrassmannianOverlapRing K (grassmannianChartChange i j))) e i
      (grassmannianOverlapUniversalMatrix K (grassmannianChartChange i j)) := by
  let σ := grassmannianChartChange i j
  let A := GrassmannianChartRing K m n
  let B := GrassmannianOverlapRing K σ
  let B' := GrassmannianOverlapRing K σ.symm
  let b : K →+* A := algebraMap K A
  let a : A →+* B' := algebraMap A B'
  let f : B' →+* B := (grassmannianOverlapTransitionAlgHom K σ).toRingHom
  let c : K →+* B := algebraMap K B
  let C := grassmannianFrameProjectiveOverlapCoordinateTransition K d e i j
  have hUa : (grassmannianFrameChartUniversalMatrix K).map a =
      grassmannianOverlapUniversalMatrix K σ.symm := by
    rfl
  have hUf : ((grassmannianFrameChartUniversalMatrix K).map a).map f =
      grassmannianOverlapTransitionMatrix K σ := by
    rw [hUa]
    exact grassmannianOverlapTransitionAlgHom_map_universal K σ
  have hcomp : f.comp (a.comp b) = c := by
    apply RingHom.ext
    intro x
    change grassmannianOverlapTransitionAlgHom K σ
      (algebraMap A B' (algebraMap K A x)) = algebraMap K B x
    rw [← IsScalarTower.algebraMap_apply K A B']
    exact (grassmannianOverlapTransitionAlgHom K σ).commutes x
  have hna := grassmannianChartHomogeneousFrameToGlobalParameters_naturality
    (R := A) d b a e j (grassmannianFrameChartUniversalMatrix K)
  have hnf := grassmannianChartHomogeneousFrameToGlobalParameters_naturality
    (R := B') d (a.comp b) f e j
      ((grassmannianFrameChartUniversalMatrix K).map a)
  have hC := grassmannianChartHomogeneousFrameProjectiveTransition_toParameters
    (R := B) d e i j
    (grassmannianOverlapUniversalMatrix K σ)
    (grassmannianOverlapTransitionMatrix K σ)
    (grassmannianFrameProjectiveOverlap_submodule_eq K i j)
  unfold grassmannianFrameProjectiveAtlasRight
    grassmannianFrameProjectiveAtlasTransition
    grassmannianFrameProjectiveChartToGlobalParameters
  calc
    (C ≫ projectiveFrameCoordinateCoefficientMap (m := m) f ≫
        projectiveFrameCoordinateCoefficientMap (m := m) a) ≫
      grassmannianChartHomogeneousFrameToGlobalParameters d b e j
        (grassmannianFrameChartUniversalMatrix K) =
      C ≫ projectiveFrameCoordinateCoefficientMap (m := m) f ≫
        (projectiveFrameCoordinateCoefficientMap (m := m) a ≫
          grassmannianChartHomogeneousFrameToGlobalParameters d b e j
            (grassmannianFrameChartUniversalMatrix K)) := by
      simp only [Category.assoc]
    _ = C ≫ projectiveFrameCoordinateCoefficientMap (m := m) f ≫
        grassmannianChartHomogeneousFrameToGlobalParameters d (a.comp b) e j
          ((grassmannianFrameChartUniversalMatrix K).map a) := by
      rw [hna]
    _ = C ≫ (projectiveFrameCoordinateCoefficientMap (m := m) f ≫
        grassmannianChartHomogeneousFrameToGlobalParameters d (a.comp b) e j
          ((grassmannianFrameChartUniversalMatrix K).map a)) := by
      rw [← Category.assoc]
    _ = C ≫ grassmannianChartHomogeneousFrameToGlobalParameters
        d (f.comp (a.comp b)) e j
          (((grassmannianFrameChartUniversalMatrix K).map a).map f) := by
      rw [hnf]
    _ = C ≫ grassmannianChartHomogeneousFrameToGlobalParameters d c e j
        (grassmannianOverlapTransitionMatrix K σ) := by
      rw [hcomp, hUf]
    _ = grassmannianChartHomogeneousFrameToGlobalParameters d c e i
        (grassmannianOverlapUniversalMatrix K σ) := by
      unfold grassmannianChartHomogeneousFrameToGlobalParameters
      rw [← Category.assoc]
      dsimp only [C, grassmannianFrameProjectiveOverlapCoordinateTransition]
      rw [hC]

/-- The two embeddings of a pairwise overlap into the ambient equation
space agree. -/
theorem grassmannianFrameProjectiveAtlas_pairwise_toGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasRight K d e i j ≫
      grassmannianFrameProjectiveChartToGlobalParameters K d e j =
    grassmannianFrameProjectiveAtlasι K i j ≫
      grassmannianFrameProjectiveChartToGlobalParameters K d e i := by
  rw [grassmannianFrameProjectiveAtlasRight_toGlobalParameters,
    grassmannianFrameProjectiveAtlasι_toGlobalParameters]

/-- The pullback of two projective-frame overlaps maps to the pullback of
their two underlying Grassmannian overlaps. -/
noncomputable def grassmannianFrameProjectiveTripleToBase
    (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    pullback (grassmannianFrameProjectiveAtlasι K i j)
        (grassmannianFrameProjectiveAtlasι K i k) ⟶
      pullback (grassmannianAtlasι K i j) (grassmannianAtlasι K i k) :=
  pullback.lift
    (pullback.fst _ _ ≫ toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m)
        (GrassmannianOverlapRing K (grassmannianChartChange i j)))))
    (pullback.snd _ _ ≫ toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m)
        (GrassmannianOverlapRing K (grassmannianChartChange i k)))))
    (by
      let aij := toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m)
          (GrassmannianOverlapRing K (grassmannianChartChange i j))))
      let aik := toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m)
          (GrassmannianOverlapRing K (grassmannianChartChange i k))))
      let b := toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n)))
      have hij : grassmannianFrameProjectiveAtlasι K i j ≫ b =
          aij ≫ grassmannianAtlasι K i j :=
        grassmannianFrameProjectiveAtlasι_toBase K i j
      have hik : grassmannianFrameProjectiveAtlasι K i k ≫ b =
          aik ≫ grassmannianAtlasι K i k :=
        grassmannianFrameProjectiveAtlasι_toBase K i k
      change (pullback.fst _ _ ≫ aij) ≫ grassmannianAtlasι K i j =
        (pullback.snd _ _ ≫ aik) ≫ grassmannianAtlasι K i k
      rw [Category.assoc, ← hij, ← Category.assoc, pullback.condition,
        Category.assoc, hik, ← Category.assoc])

@[reassoc]
theorem grassmannianFrameProjectiveTripleToBase_fst
    (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveTripleToBase K i j k ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m)
          (GrassmannianOverlapRing K (grassmannianChartChange i j)))) :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem grassmannianFrameProjectiveTripleToBase_snd
    (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveTripleToBase K i j k ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m)
          (GrassmannianOverlapRing K (grassmannianChartChange i k)))) :=
  pullback.lift_snd _ _ _

/-- The underlying point of the third projective overlap on a triple
intersection. -/
noncomputable def grassmannianFrameProjectiveTripleBaseCross
    (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    pullback (grassmannianFrameProjectiveAtlasι K i j)
        (grassmannianFrameProjectiveAtlasι K i k) ⟶
      grassmannianAtlasOverlap K (j, k) :=
  grassmannianFrameProjectiveTripleToBase K i j k ≫
    grassmannianAtlasTripleFirst K i j k

/-- The map into the `j`-th projective chart and the underlying
Grassmannian triple-overlap point have the same base point. -/
theorem grassmannianFrameProjectiveTripleBaseCross_compat
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    (pullback.fst (grassmannianFrameProjectiveAtlasι K i j)
        (grassmannianFrameProjectiveAtlasι K i k) ≫
      grassmannianFrameProjectiveAtlasRight K d e i j) ≫
        toBase (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) =
    grassmannianFrameProjectiveTripleBaseCross K i j k ≫
      grassmannianAtlasι K j k := by
  rw [Category.assoc, grassmannianFrameProjectiveAtlasRight_toBase]
  unfold grassmannianFrameProjectiveTripleBaseCross
  rw [Category.assoc, grassmannianAtlasTripleFirst_fac]
  rw [grassmannianFrameProjectiveTripleToBase_fst_assoc]

/-- The third projective overlap crossing, obtained from the Cartesian
projective coefficient square over the base Grassmannian crossing. -/
noncomputable def grassmannianFrameProjectiveTripleCross
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    pullback (grassmannianFrameProjectiveAtlasι K i j)
        (grassmannianFrameProjectiveAtlasι K i k) ⟶
      grassmannianFrameProjectiveOverlapSpace K j k :=
  (isPullback_projectiveCoefficientMap
    (algebraMap (GrassmannianChartRing K m n)
      (GrassmannianOverlapRing K (grassmannianChartChange j k)))
    (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n)))
    (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m)
        (GrassmannianOverlapRing K (grassmannianChartChange j k))))
    (by simp)).lift
      (pullback.fst _ _ ≫ grassmannianFrameProjectiveAtlasRight K d e i j)
      (grassmannianFrameProjectiveTripleBaseCross K i j k)
      (grassmannianFrameProjectiveTripleBaseCross_compat K d e i j k)

/-- The third-overlap crossing has the required first projection. -/
@[reassoc]
theorem grassmannianFrameProjectiveTripleCross_fac
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveTripleCross K d e i j k ≫
      grassmannianFrameProjectiveAtlasι K j k =
    pullback.fst _ _ ≫ grassmannianFrameProjectiveAtlasRight K d e i j := by
  exact (isPullback_projectiveCoefficientMap
    (algebraMap (GrassmannianChartRing K m n)
      (GrassmannianOverlapRing K (grassmannianChartChange j k)))
    (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n)))
    (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m)
        (GrassmannianOverlapRing K (grassmannianChartChange j k))))
    (by simp)).lift_fst _ _ _

/-- The third-overlap crossing has the prescribed underlying Grassmannian
triple-overlap point. -/
@[reassoc]
theorem grassmannianFrameProjectiveTripleCross_toBase
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveTripleCross K d e i j k ≫
      toBase (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin m)
          (GrassmannianOverlapRing K (grassmannianChartChange j k)))) =
    grassmannianFrameProjectiveTripleBaseCross K i j k := by
  exact (isPullback_projectiveCoefficientMap
    (algebraMap (GrassmannianChartRing K m n)
      (GrassmannianOverlapRing K (grassmannianChartChange j k)))
    (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n)))
    (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m)
        (GrassmannianOverlapRing K (grassmannianChartChange j k))))
    (by simp)).lift_snd _ _ _

/-- The third-overlap crossing is also compatible with the right overlap
maps.  The proof compares the underlying Grassmannian point and the ambient
equation parameter separately, using the Cartesian coefficient square for
the ambient projective equation space. -/
theorem grassmannianFrameProjectiveTripleCross_right
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j k : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveTripleCross K d e i j k ≫
      grassmannianFrameProjectiveAtlasRight K d e j k =
    pullback.snd _ _ ≫ grassmannianFrameProjectiveAtlasRight K d e i k := by
  let A := GrassmannianChartRing K m n
  let b : K →+* A := algebraMap K A
  let E := grassmannianChartHomogeneousFrameToParameters (R := A) d e k
    (grassmannianFrameChartUniversalMatrix K)
  have hglobal :
      (grassmannianFrameProjectiveTripleCross K d e i j k ≫
          grassmannianFrameProjectiveAtlasRight K d e j k) ≫
        grassmannianFrameProjectiveChartToGlobalParameters K d e k =
      (pullback.snd _ _ ≫ grassmannianFrameProjectiveAtlasRight K d e i k) ≫
        grassmannianFrameProjectiveChartToGlobalParameters K d e k := by
    rw [Category.assoc,
      grassmannianFrameProjectiveAtlas_pairwise_toGlobalParameters]
    rw [← Category.assoc,
      grassmannianFrameProjectiveTripleCross_fac]
    rw [Category.assoc,
      grassmannianFrameProjectiveAtlas_pairwise_toGlobalParameters]
    rw [← Category.assoc, pullback.condition]
    rw [Category.assoc,
      ← grassmannianFrameProjectiveAtlas_pairwise_toGlobalParameters]
    exact (Category.assoc _ _ _).symm
  have hbase :
      (grassmannianFrameProjectiveTripleCross K d e i j k ≫
          grassmannianFrameProjectiveAtlasRight K d e j k) ≫
        toBase (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin m) A)) =
      (pullback.snd _ _ ≫ grassmannianFrameProjectiveAtlasRight K d e i k) ≫
        toBase (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin m) A)) := by
    rw [Category.assoc, grassmannianFrameProjectiveAtlasRight_toBase]
    rw [← Category.assoc,
      grassmannianFrameProjectiveTripleCross_toBase]
    unfold grassmannianFrameProjectiveTripleBaseCross
    rw [Category.assoc, grassmannianAtlasTripleFirst_other]
    rw [grassmannianFrameProjectiveTripleToBase_snd_assoc]
    rw [Category.assoc, grassmannianFrameProjectiveAtlasRight_toBase]
  have hE : E ≫ projectiveParametersToBase A τ d =
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) A)) :=
    grassmannianChartHomogeneousFrameToParameters_toBase
      (R := A) d e k (grassmannianFrameChartUniversalMatrix K)
  apply (cancel_mono E).mp
  apply (isPullback_projectiveCoefficientMap b
    (ParameterIdeal K τ d) (ParameterIdeal A τ d) (by simp)).hom_ext
  · change
      (grassmannianFrameProjectiveTripleCross K d e i j k ≫
          grassmannianFrameProjectiveAtlasRight K d e j k) ≫
          (E ≫ projectiveParametersCoefficientMap d b) =
        (pullback.snd _ _ ≫ grassmannianFrameProjectiveAtlasRight K d e i k) ≫
          (E ≫ projectiveParametersCoefficientMap d b)
    exact hglobal
  · change
      (grassmannianFrameProjectiveTripleCross K d e i j k ≫
          grassmannianFrameProjectiveAtlasRight K d e j k) ≫
          (E ≫ projectiveParametersToBase A τ d) =
        (pullback.snd _ _ ≫ grassmannianFrameProjectiveAtlasRight K d e i k) ≫
          (E ≫ projectiveParametersToBase A τ d)
    rw [hE]
    exact hbase

/-- The projective-frame charts and their explicit overlaps form categorical
gluing data. -/
noncomputable def grassmannianFrameProjectiveCategoryGlueData
    (e : Fin (m + n) ≃ Monomials τ d) :
    CategoryTheory.GlueData Scheme.{u} :=
  AllCharacteristics.OverlapComposition.glueData
    (fun _ : ULift.{u} (Equiv.Perm (Fin m ⊕ Fin n)) =>
      grassmannianFrameProjectiveChartSpace K m n)
    (fun i j => grassmannianFrameProjectiveOverlapSpace K i.down j.down)
    (fun i j => grassmannianFrameProjectiveAtlasι K i.down j.down)
    (fun i j => grassmannianFrameProjectiveAtlasRight K d e i.down j.down)
    (fun i j => grassmannianFrameProjectiveAtlasTransition K d e i.down j.down)
    (fun _ _ => rfl)
    (fun i j k => grassmannianFrameProjectiveTripleCross K d e i.down j.down k.down)
    (fun i j k => grassmannianFrameProjectiveTripleCross_fac K d e i.down j.down k.down)
    (fun i j k => grassmannianFrameProjectiveTripleCross_right K d e i.down j.down k.down)
    (fun i j => grassmannianFrameProjectiveAtlasTransition_comp K d e i.down j.down)
    (fun i => grassmannianFrameProjectiveAtlasTransition_self K d e i.down)

/-- Genuine scheme glue data for the relative projective bundle of
Grassmannian homogeneous frames. -/
noncomputable def grassmannianFrameProjectiveGlueData
    (e : Fin (m + n) ≃ Monomials τ d) : Scheme.GlueData.{u} where
  toGlueData := grassmannianFrameProjectiveCategoryGlueData K d e
  f_open i j := grassmannianFrameProjectiveAtlasι_isOpenImmersion K i.down j.down

/-- The global scheme obtained by gluing the local projective-frame charts. -/
noncomputable def grassmannianFrameProjectiveScheme
    (e : Fin (m + n) ≃ Monomials τ d) : Scheme.{u} :=
  (grassmannianFrameProjectiveGlueData K d e).glued

/-- A local projective-frame chart in the globally glued family. -/
noncomputable def grassmannianFrameProjectiveChartι
    (e : Fin (m + n) ≃ Monomials τ d)
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveChartSpace K m n ⟶
      grassmannianFrameProjectiveScheme K d e :=
  (grassmannianFrameProjectiveGlueData K d e).ι (ULift.up i)

instance grassmannianFrameProjectiveChartι_isOpenImmersion
    (e : Fin (m + n) ≃ Monomials τ d)
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    IsOpenImmersion (grassmannianFrameProjectiveChartι K d e i) :=
  Scheme.GlueData.ι_isOpenImmersion
    (grassmannianFrameProjectiveGlueData K d e) (ULift.up i)

/-- The local projective-frame charts cover the globally glued family. -/
theorem grassmannianFrameProjectiveChartι_jointly_surjective
    (e : Fin (m + n) ≃ Monomials τ d)
    (x : grassmannianFrameProjectiveScheme K d e) :
    ∃ (i : Equiv.Perm (Fin m ⊕ Fin n))
      (y : grassmannianFrameProjectiveChartSpace K m n),
      grassmannianFrameProjectiveChartι K d e i y = x := by
  obtain ⟨i, y, hy⟩ := Scheme.GlueData.ι_jointly_surjective
    (grassmannianFrameProjectiveGlueData K d e) x
  exact ⟨i.down, y, hy⟩

/-- The two presentations of a projective-frame overlap agree in the glued
family. -/
theorem grassmannianFrameProjectiveChartι_glue
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasTransition K d e i j ≫
        grassmannianFrameProjectiveAtlasι K j i ≫
        grassmannianFrameProjectiveChartι K d e j =
      grassmannianFrameProjectiveAtlasι K i j ≫
        grassmannianFrameProjectiveChartι K d e i :=
  Scheme.GlueData.glue_condition
    (grassmannianFrameProjectiveGlueData K d e) (ULift.up i) (ULift.up j)

/-- The local structural maps of the projective-frame charts agree on every
pairwise overlap after passage to the global Grassmannian. -/
theorem grassmannianFrameProjectiveChart_toGrassmannian_glue
    (e : Fin (m + n) ≃ Monomials τ d)
    (i j : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveAtlasι K i j ≫
        toBase (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) ≫
        grassmannianChartι K i =
      (grassmannianFrameProjectiveAtlasTransition K d e i j ≫
        grassmannianFrameProjectiveAtlasι K j i) ≫
        toBase (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) ≫
        grassmannianChartι K j := by
  let a := toBase (⊥ : HomogeneousIdeal
    (homogeneousSubmodule (Fin m)
      (GrassmannianOverlapRing K (grassmannianChartChange i j))))
  let b := toBase (⊥ : HomogeneousIdeal
    (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n)))
  have hl : grassmannianFrameProjectiveAtlasι K i j ≫ b =
      a ≫ grassmannianAtlasι K i j :=
    grassmannianFrameProjectiveAtlasι_toBase K i j
  have hr : grassmannianFrameProjectiveAtlasRight K d e i j ≫ b =
      a ≫ grassmannianAtlasTransition K i j ≫ grassmannianAtlasι K j i :=
    grassmannianFrameProjectiveAtlasRight_toBase K d e i j
  change (grassmannianFrameProjectiveAtlasι K i j ≫ b) ≫
      grassmannianChartι K i =
    (grassmannianFrameProjectiveAtlasRight K d e i j ≫ b) ≫
      grassmannianChartι K j
  calc
    (grassmannianFrameProjectiveAtlasι K i j ≫ b) ≫
        grassmannianChartι K i =
      (a ≫ grassmannianAtlasι K i j) ≫ grassmannianChartι K i :=
        congrArg (fun q => q ≫ grassmannianChartι K i) hl
    _ = a ≫ (grassmannianAtlasι K i j ≫ grassmannianChartι K i) :=
      Category.assoc _ _ _
    _ = a ≫ (grassmannianAtlasTransition K i j ≫
        grassmannianAtlasι K j i ≫ grassmannianChartι K j) :=
      congrArg (fun q => a ≫ q) (grassmannianChartι_glue K i j).symm
    _ = (a ≫ grassmannianAtlasTransition K i j ≫
        grassmannianAtlasι K j i) ≫ grassmannianChartι K j := by
      simp only [Category.assoc]
    _ = (grassmannianFrameProjectiveAtlasRight K d e i j ≫ b) ≫
        grassmannianChartι K j :=
      congrArg (fun q => q ≫ grassmannianChartι K j) hr.symm

/-- The global projective-frame family over the glued Grassmannian. -/
noncomputable def grassmannianFrameProjectiveToGrassmannian
    (e : Fin (m + n) ≃ Monomials τ d) :
    grassmannianFrameProjectiveScheme K d e ⟶ grassmannianScheme K m n :=
  Multicoequalizer.desc
    (grassmannianFrameProjectiveGlueData K d e).toGlueData.diagram _
    (fun i => toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) ≫
        grassmannianChartι K i.down) (by
      rintro ⟨i, j⟩
      change grassmannianFrameProjectiveAtlasι K i.down j.down ≫
          (toBase (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) ≫
            grassmannianChartι K i.down) =
        (grassmannianFrameProjectiveAtlasTransition K d e i.down j.down ≫
          grassmannianFrameProjectiveAtlasι K j.down i.down) ≫
          (toBase (⊥ : HomogeneousIdeal
            (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) ≫
            grassmannianChartι K j.down)
      simpa only [Category.assoc] using
        grassmannianFrameProjectiveChart_toGrassmannian_glue
          K d e i.down j.down)

/-- On each local chart, the global projection is the usual projective
structure map followed by the corresponding Grassmannian chart inclusion. -/
theorem grassmannianFrameProjectiveChartι_toGrassmannian
    (e : Fin (m + n) ≃ Monomials τ d)
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveChartι K d e i ≫
      grassmannianFrameProjectiveToGrassmannian K d e =
    toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin m) (GrassmannianChartRing K m n))) ≫
      grassmannianChartι K i := by
  unfold grassmannianFrameProjectiveToGrassmannian
  exact Multicoequalizer.π_desc
    (grassmannianFrameProjectiveGlueData K d e).toGlueData.diagram _ _ _
    (ULift.up i)

/-- The ambient equation represented by a point of the globally glued
projective-frame family. -/
noncomputable def grassmannianFrameProjectiveToGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d) :
    grassmannianFrameProjectiveScheme K d e ⟶ projectiveParameters K τ d :=
  Multicoequalizer.desc
    (grassmannianFrameProjectiveGlueData K d e).toGlueData.diagram _
    (fun i => grassmannianFrameProjectiveChartToGlobalParameters K d e i.down) (by
      rintro ⟨i, j⟩
      change grassmannianFrameProjectiveAtlasι K i.down j.down ≫
          grassmannianFrameProjectiveChartToGlobalParameters K d e i.down =
        (grassmannianFrameProjectiveAtlasTransition K d e i.down j.down ≫
          grassmannianFrameProjectiveAtlasι K j.down i.down) ≫
          grassmannianFrameProjectiveChartToGlobalParameters K d e j.down
      simpa only [grassmannianFrameProjectiveAtlasRight, Category.assoc] using
        (grassmannianFrameProjectiveAtlas_pairwise_toGlobalParameters
          K d e i.down j.down).symm)

/-- The global ambient-equation map restricts on every local chart to the
frame's explicit homogeneous coefficient map. -/
theorem grassmannianFrameProjectiveChartι_toGlobalParameters
    (e : Fin (m + n) ≃ Monomials τ d)
    (i : Equiv.Perm (Fin m ⊕ Fin n)) :
    grassmannianFrameProjectiveChartι K d e i ≫
      grassmannianFrameProjectiveToGlobalParameters K d e =
    grassmannianFrameProjectiveChartToGlobalParameters K d e i := by
  unfold grassmannianFrameProjectiveToGlobalParameters
  exact Multicoequalizer.π_desc
    (grassmannianFrameProjectiveGlueData K d e).toGlueData.diagram _ _ _
    (ULift.up i)

end PfaffianDescent
