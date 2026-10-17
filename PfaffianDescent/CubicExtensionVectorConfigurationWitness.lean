import PfaffianDescent.VoisinGroundFieldCommonChart
import PfaffianDescent.CubicPolynomialJetMinorTransport
import PfaffianDescent.VoisinDegreeTenSelectedAvoidanceGridOriginalCoordinates
import PfaffianDescent.CubicClosedPointSerreSurfaceJetCotangentNormalizationResidue

/-!
Extension-field vector witnesses give points of the ORIGINAL ground-field
ordered configuration scheme, using one linear chart defined over K.
-/

noncomputable section
namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics AllCharacteristics.HomogeneousProjective

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

def cubicGroundChartNormalizedVector (c : Fin 4 → K) (v : Fin 4 → L) : Fin 4 → L :=
  fun j => ((homogeneousLinearForm c).eval₂ (algebraMap K L) v)⁻¹ * v j

theorem cubicGroundChartNormalizedVector_linearForm
    (c : Fin 4 → K) (v : Fin 4 → L)
    (hc : (homogeneousLinearForm c).eval₂ (algebraMap K L) v ≠ 0) :
    (homogeneousLinearForm c).eval₂ (algebraMap K L)
      (cubicGroundChartNormalizedVector c v) = 1 := by
  have h := cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
    (((homogeneousLinearForm c).eval₂ (algebraMap K L) v)⁻¹) v
  change (homogeneousLinearForm c).eval₂ (algebraMap K L)
    (cubicGroundChartNormalizedVector c v) = _ at h
  rw [h, pow_one]
  exact inv_mul_cancel₀ hc

theorem cubicGroundChartNormalizedVector_cubic
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (v : Fin 4 → L)
    (hv : p.eval₂ (algebraMap K L) v = 0) :
    p.eval₂ (algebraMap K L) (cubicGroundChartNormalizedVector c v) = 0 := by
  have h := cubicClosedPointSerreSurfaceJetCotangent_aeval_mul_homogeneous p hp
    (((homogeneousLinearForm c).eval₂ (algebraMap K L) v)⁻¹) v
  change p.eval₂ (algebraMap K L) (cubicGroundChartNormalizedVector c v) = _ at h
  change aeval v p = 0 at hv
  rw [h, hv, mul_zero]

/-- A common actual ground-field chart detects equality of extension-field
normalized vectors by its actual chart-coordinate ring maps. -/
theorem linearNormalizedPointAt_extension_injective
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (z : CoordinateRing I) (hz : z ∈ grading I 1)
    (v w : Fin 4 → L)
    (hev : ∀ q ∈ I.toIdeal, (eval₂Hom (algebraMap K L) v) q = 0)
    (hew : ∀ q ∈ I.toIdeal, (eval₂Hom (algebraMap K L) w) q = 0)
    (hv1 : (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K L) v) hev) z = 1)
    (hw1 : (Ideal.Quotient.lift I.toIdeal (eval₂Hom (algebraMap K L) w) hew) z = 1)
    (h : linearNormalizedPointAt I v hev z hz hv1 =
      linearNormalizedPointAt I w hew z hz hw1) : v = w := by
  simp only [linearNormalizedPointAt] at h
  have hm := (cancel_mono (Proj.awayι (grading I) z hz
    (by decide : 0 < 1))).mp h
  have hr := Spec.map_injective hm
  funext j
  have hj := congrArg (fun g : CommRingCat.of (Away (grading I) z) ⟶ CommRingCat.of L =>
    g (linearChartCoordinate I z hz j)) hr
  change linearNormalizedPointChartMapAt I v hev z hz hv1
      (linearChartCoordinate I z hz j) =
    linearNormalizedPointChartMapAt I w hew z hz hw1
      (linearChartCoordinate I z hz j) at hj
  rw [linearNormalizedPointChartMapAt_coordinate, linearNormalizedPointChartMapAt_coordinate] at hj
  exact hj

def cubicExtensionVectorPointInGroundChart
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (v : Fin 4 → L)
    (hv : p.eval₂ (algebraMap K L) v = 0)
    (hc : (homogeneousLinearForm c).eval₂ (algebraMap K L) v ≠ 0) :
    Spec (.of L) ⟶ hypersurface p hp :=
  linearNormalizedPointAt (equationIdeal p hp) (cubicGroundChartNormalizedVector c v)
    (voisinDegreeTenSelectedAvoidance_equationIdeal_eval₂_zero p hp _
      (cubicGroundChartNormalizedVector_cubic p hp c v hv))
    (Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c))
    (polynomial_class_mem_grading (equationIdeal p hp) (homogeneousLinearForm c)
      (homogeneousLinearForm_isHomogeneous c))
    (by exact cubicGroundChartNormalizedVector_linearForm c v hc)

theorem cubicExtensionVectorPointInGroundChart_toBase
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (v : Fin 4 → L)
    (hv : p.eval₂ (algebraMap K L) v = 0)
    (hc : (homogeneousLinearForm c).eval₂ (algebraMap K L) v ≠ 0) :
    cubicExtensionVectorPointInGroundChart p hp c v hv hc ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  exact linearNormalizedPointAt_toBase (equationIdeal p hp) _ _ _ _ _

theorem cubicExtensionVectorPointInGroundChart_ne_of_directions
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (c : Fin 4 → K) (v w : Fin 4 → L)
    (hv : p.eval₂ (algebraMap K L) v = 0) (hw : p.eval₂ (algebraMap K L) w = 0)
    (hcv : (homogeneousLinearForm c).eval₂ (algebraMap K L) v ≠ 0)
    (hcw : (homogeneousLinearForm c).eval₂ (algebraMap K L) w ≠ 0)
    (hdir : ∀ a : L, a • v ≠ w) :
    cubicExtensionVectorPointInGroundChart p hp c v hv hcv ≠
      cubicExtensionVectorPointInGroundChart p hp c w hw hcw := by
  intro h
  have hnorm : cubicGroundChartNormalizedVector c v = cubicGroundChartNormalizedVector c w :=
    linearNormalizedPointAt_extension_injective (equationIdeal p hp) _ _ _ _ _ _ _ _ h
  apply hdir ((homogeneousLinearForm c).eval₂ (algebraMap K L) w *
    ((homogeneousLinearForm c).eval₂ (algebraMap K L) v)⁻¹)
  funext j
  have hj := congrFun hnorm j
  change ((homogeneousLinearForm c).eval₂ (algebraMap K L) v)⁻¹ * v j =
    ((homogeneousLinearForm c).eval₂ (algebraMap K L) w)⁻¹ * w j at hj
  change _ * v j = w j
  calc
    _ = (homogeneousLinearForm c).eval₂ (algebraMap K L) w *
        (((homogeneousLinearForm c).eval₂ (algebraMap K L) v)⁻¹ * v j) := by ring
    _ = (homogeneousLinearForm c).eval₂ (algebraMap K L) w *
        (((homogeneousLinearForm c).eval₂ (algebraMap K L) w)⁻¹ * w j) := congrArg _ hj
    _ = w j := by rw [← mul_assoc, mul_inv_cancel₀ hcw, one_mul]

/-- Original-K ordered configuration, with literal common-chart marked
points, from any projectively distinct extension-field vector family. -/
theorem cubicExtensionVector_exists_orderedConfiguration
    [Infinite K] (n : ℕ)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (v : Fin n → Fin 4 → L)
    (hv : ∀ i, p.eval₂ (algebraMap K L) (v i) = 0)
    (hv0 : ∀ i, v i ≠ 0)
    (hdir : ∀ i j, i ≠ j → ∀ a : L, a • v i ≠ v j) :
    ∃ (c : Fin 4 → K)
      (hc : ∀ i, (homogeneousLinearForm c).eval₂ (algebraMap K L) (v i) ≠ 0)
      (A : Spec (.of L) ⟶
        (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).left),
      A ≫ (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) n).hom =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) ∧
      ∀ i, (A ≫ Over.Hom.left (orderedFamilyConfigurationι (hypersurfaceToBase p hp) n)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) n i).left =
          cubicExtensionVectorPointInGroundChart p hp c (v i) (hv i) (hc i) := by
  obtain ⟨c, hc⟩ := exists_common_groundField_linear_chart_for_nonzero_vectors (K := K) v hv0
  let q : Fin n → (Spec (.of L) ⟶ hypersurface p hp) := fun i =>
    cubicExtensionVectorPointInGroundChart p hp c (v i) (hv i) (hc i)
  have hbase : ∀ i, q i ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := fun i =>
    cubicExtensionVectorPointInGroundChart_toBase p hp c (v i) (hv i) (hc i)
  have hdist : ∀ i j, i ≠ j → q i ≠ q j := fun i j hij =>
    cubicExtensionVectorPointInGroundChart_ne_of_directions p hp c (v i) (v j)
      (hv i) (hv j) (hc i) (hc j) (hdir i j hij)
  letI : IsSeparated (hypersurfaceToBase p hp) :=
    isSeparated_homogeneousToBase (equationIdeal p hp)
  obtain ⟨A, hA, hcoords⟩ := exists_orderedConfigurationFieldPoint
    (hypersurfaceToBase p hp) n (Spec.map (CommRingCat.ofHom (algebraMap K L))) q hbase hdist
  exact ⟨c, hc, A, hA, hcoords⟩

end PfaffianDescent
