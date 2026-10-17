import PfaffianDescent.VoisinProjectiveLinearSystem
import PfaffianDescent.VoisinQuotientNormalizedAmbientChart

/-!
# Detected projective points exclude a common frame incidence

This is the coordinate-level converse needed in the arbitrary-field part of
Voisin's construction: a simultaneous universal-incidence lift produces a
nonzero frame combination vanishing on every marked coordinate vector.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Simultaneous universal-family lifts over one frame parameter produce a
nonzero coefficient vector whose frame combination vanishes at every marked
coordinate vector.  Each vector is allowed its own standard affine chart. -/
theorem exists_nonzero_frameCombination_vanishing_of_universalFamily_lifts
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {d m n : ℕ}
    (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hframe : LinearIndependent K frame)
    (t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)))
    {ι : Type}
    (y : ι → Fin 4 → L) (j : ι → Fin 4)
    (hyj : ∀ a, y a (j a) = 1)
    (u : ι → (Spec (.of L) ⟶
      projectiveUniversalFamily K (Fin 4) d))
    (hu : ∀ a, u a ≫ projectiveUniversalToBase K (Fin 4) d =
      t ≫ homogeneousFrameToParameters d e frame hframe)
    (hambient : ∀ a,
      u a ≫ projectiveUniversalToAmbient K (Fin 4) d =
        let I : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) K) := ⊥
        let he : ∀ q ∈ I.toIdeal,
            (eval₂Hom (algebraMap K L) (y a)) q = 0 := by
          intro q hq
          exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
        let ell := X (j a)
        let z := Ideal.Quotient.mk I.toIdeal ell
        let hz : z ∈ grading I 1 :=
          polynomial_class_mem_grading I ell (isHomogeneous_X K (j a))
        let hzOne : (Ideal.Quotient.lift I.toIdeal
            (eval₂Hom (algebraMap K L) (y a)) he) z = 1 := by
          simpa [I, z, ell] using hyj a
        linearNormalizedPointAt I (y a) he z hz hzOne ≫
          quotientProjMap I) :
    ∃ c : Fin n → L, c ≠ 0 ∧
      ∀ a, MvPolynomial.eval (y a)
        (∑ k, MvPolynomial.C (c k) *
          (frame k).1.map (algebraMap K L)) = 0 := by
  obtain ⟨i, g, hbase, roots, hrootsBase, hrootsAmbient⟩ :=
    exists_homogeneousFrame_parameterization_universalFamily_lifts
      d (algebraMap K L) e frame hframe t ht u hu
  let c : Fin n → L := fun k => g (linearChartCoordinate
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
    ((polynomialQuotientGradingMap (ParameterIdeal K (Fin 4) d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e frame)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e frame)))
      (coordinate (ParameterIdeal K (Fin 4) d) (e i)))
    ((polynomialQuotientGradingMap (ParameterIdeal K (Fin 4) d)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K))
      (projectiveLinearSystemMatrixSubstitution d e
        (homogeneousFrameCoefficientMatrix d e frame)) bot_le
      (projectiveLinearSystemMatrixSubstitution_homogeneous d e
        (homogeneousFrameCoefficientMatrix d e frame))).map_mem
      (coordinate_mem (ParameterIdeal K (Fin 4) d) (e i))) k)
  let p : MvPolynomial (Fin 4) L :=
    ∑ k, MvPolynomial.C (c k) * (frame k).1.map (algebraMap K L)
  have hp : p.IsHomogeneous d := by
    apply MvPolynomial.IsHomogeneous.sum
    intro k _
    exact ((frame k).2.map (algebraMap K L)).C_mul _
  have hpne : p ≠ 0 := homogeneousFrame_awayMap_combination_ne_zero
    d e frame hframe i g (algebraMap K L) hbase
  have hc : c ≠ 0 := by
    intro hc
    apply hpne
    simp [p, hc]
  refine ⟨c, hc, ?_⟩
  intro a
  let I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K) := ⊥
  let he : ∀ q ∈ I.toIdeal,
      (eval₂Hom (algebraMap K L) (y a)) q = 0 := by
    intro q hq
    exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
  let ell : MvPolynomial (Fin 4) K := X (j a)
  let z : CoordinateRing I := Ideal.Quotient.mk I.toIdeal ell
  have hz : z ∈ grading I 1 :=
    polynomial_class_mem_grading I ell (isHomogeneous_X K (j a))
  have hzOne : (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap K L) (y a)) he) z = 1 := by
    simpa [I, z, ell] using hyj a
  have hyjne : y a (j a) ≠ 0 := by rw [hyj a]; exact one_ne_zero
  obtain ⟨ga, hgaPoint, hgaCoordinates⟩ :=
    exists_ambientCoordinateChart_of_quotientNormalizedPointAt
      I (y a) ell (isHomogeneous_X K (j a)) he hzOne (j a) hyjne
  have hrootBase : roots a ≫ hypersurfaceToBase p hp =
      Spec.map (CommRingCat.ofHom (RingHom.id L)) := by
    have hid : CommRingCat.ofHom (RingHom.id L) = 𝟙 _ := rfl
    rw [hid, Spec.map_id]
    exact hrootsBase a
  have hrootAmbient : roots a ≫ hypersurfaceToAmbient p hp ≫
      ambientCoefficientMap (algebraMap K L) =
      Spec.map (CommRingCat.ofHom ga) ≫
        Proj.awayι (homogeneousSubmodule (Fin 4) K) (X (j a))
          (isHomogeneous_X K (j a)) (by decide : 0 < 1) := by
    calc
      roots a ≫ hypersurfaceToAmbient p hp ≫
          ambientCoefficientMap (algebraMap K L) =
          u a ≫ projectiveUniversalToAmbient K (Fin 4) d :=
        hrootsAmbient a
      _ = linearNormalizedPointAt I (y a) he z hz hzOne ≫
          quotientProjMap I := by
        simpa only [I, he, ell, z, hz, hzOne] using hambient a
      _ = Spec.map (CommRingCat.ofHom ga) ≫
          Proj.awayι (homogeneousSubmodule (Fin 4) K) (X (j a))
            (isHomogeneous_X K (j a)) (by decide : 0 < 1) := hgaPoint.symm
  have hzero :=
    AllCharacteristics.HomogeneousProjective.aeval_map_eq_zero_of_ambient_eq
      (algebraMap K L) p hp (RingHom.id L) (roots a) hrootBase
        (j a) ga hrootAmbient
  have hcoords : (fun k => ga
      (AllCharacteristics.GradedChart.normalized
        (homogeneousSubmodule (Fin 4) K) (isHomogeneous_X K (j a))
        (X k) (isHomogeneous_X K k))) = y a := by
    funext k
    rw [hgaCoordinates k, hyj a, inv_one, one_mul]
  change MvPolynomial.aeval (y a) p = 0
  rw [← hcoords]
  simpa only [MvPolynomial.map_id] using hzero

/-- A detecting family of marked coordinate vectors cannot admit simultaneous
universal-family lifts over one parameter of the same frame. -/
theorem universalFamily_lifts_impossible_of_frameDetection
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {d m n : ℕ}
    (e : Fin m ≃ Monomials (Fin 4) d)
    (frame : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hframe : LinearIndependent K frame)
    (t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)))
    {ι : Type}
    (y : ι → Fin 4 → L) (j : ι → Fin 4)
    (hyj : ∀ a, y a (j a) = 1)
    (u : ι → (Spec (.of L) ⟶
      projectiveUniversalFamily K (Fin 4) d))
    (hu : ∀ a, u a ≫ projectiveUniversalToBase K (Fin 4) d =
      t ≫ homogeneousFrameToParameters d e frame hframe)
    (hambient : ∀ a,
      u a ≫ projectiveUniversalToAmbient K (Fin 4) d =
        let I : HomogeneousIdeal
          (homogeneousSubmodule (Fin 4) K) := ⊥
        let he : ∀ q ∈ I.toIdeal,
            (eval₂Hom (algebraMap K L) (y a)) q = 0 := by
          intro q hq
          exact (Ideal.mem_bot.mp hq).symm ▸ map_zero _
        let ell := X (j a)
        let z := Ideal.Quotient.mk I.toIdeal ell
        let hz : z ∈ grading I 1 :=
          polynomial_class_mem_grading I ell (isHomogeneous_X K (j a))
        let hzOne : (Ideal.Quotient.lift I.toIdeal
            (eval₂Hom (algebraMap K L) (y a)) he) z = 1 := by
          simpa [I, z, ell] using hyj a
        linearNormalizedPointAt I (y a) he z hz hzOne ≫
          quotientProjMap I)
    (hdetect : ∀ c : Fin n → L,
      (∀ a, MvPolynomial.eval (y a)
        (∑ k, MvPolynomial.C (c k) *
          (frame k).1.map (algebraMap K L)) = 0) → c = 0) :
    False := by
  obtain ⟨c, hc, hzero⟩ :=
    exists_nonzero_frameCombination_vanishing_of_universalFamily_lifts
      e frame hframe t ht y j hyj u hu hambient
  exact hc (hdetect c hzero)

end PfaffianDescent
