import PfaffianDescent.VoisinSmoothOriginalEightFiniteDatum
import PfaffianDescent.VoisinFiniteWitnessResidueCoordinates
import PfaffianDescent.VoisinResidueSelectedPairFinite

/-!
# A finite selected residue specialization for a smooth cubic

The explicit algebraic-closure witness is viewed as a point of the original
ordered configuration.  Its residue coordinates retain the finite geometric
cubic--two-quadrics intersection, and hence give a finite canonical selected
pair over the residue field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

def SmoothCubicResidueSelectedPairFiniteAt
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) : Prop :=
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let Q := O.residueField z
  letI : Algebra K Q := pointAlgebra
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
  ∃ (j : Fin 8 → Fin 4) (x₀ : Fin 8 → Fin 4 → Q)
    (c : Fin 4 → K) (m : Fin 8 ↪ Monomials (Fin 4) 2),
    (∀ i, x₀ i (j i) = 1) ∧
    (∀ i, ∃ (he0 : ∀ r ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) K)).toIdeal,
        r.eval₂ (algebraMap K Q) (x₀ i) = 0)
      (hX : (X (j i)).eval₂ (algebraMap K Q) (x₀ i) = 1),
      linearNormalizedPoint
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
          (x₀ i) (X (j i)) (isHomogeneous_X K (j i)) hX he0 ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) =
        O.fromSpecResidueField z ≫
          (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
            (isSeparated_homogeneousToBase (equationIdeal p hp)) 8
            (hypersurfaceToAmbient p hp) i)) ∧
    let cQ : Fin 4 → Q := fun k => algebraMap K Q (c k)
    let x : Fin 8 → Fin 4 → Q := fun i =>
      normalizedVectorInLinearChart cQ (x₀ i)
    ∃ hm : IsUnit (eightPointQuadraticEvaluationMinor m x).det,
      (∀ i, (homogeneousLinearForm cQ).eval (x₀ i) ≠ 0) ∧
      (∀ i f, f ∈ (equationIdeal p hp).toIdeal →
        f.eval₂ (algebraMap K Q) (x i) = 0) ∧
      let pQ := p.map (algebraMap K Q)
      let hpQ := hp.map (algebraMap K Q)
      let hid : IsUnit (eightPointQuadraticEvaluationMinor m
        (fun i k => (RingHom.id Q) (x i k))).det := by simpa using hm
      let b := quadraticSelectedOpenBasisSpecializedBasis
        m x (RingHom.id Q) hid
      IsFinite (relativeTripleIntersectionToBase pQ
        (quadraticPolynomialOfCoefficients (b 0).1)
        (quadraticPolynomialOfCoefficients (b 1).1) hpQ
        (quadraticPolynomialOfCoefficients_isHomogeneous (b 0).1)
        (quadraticPolynomialOfCoefficients_isHomogeneous (b 1).1))

theorem residueCoordinates_mem_commonLinearBasicOpen
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left
    let Q := O.residueField z
    letI : Algebra K Q := pointAlgebra
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
    ∀ (j : Fin 8 → Fin 4) (x₀ : Fin 8 → Fin 4 → Q)
      (c : Fin 4 → K),
      (∀ i, x₀ i (j i) = 1) →
      (∀ i, ∃ (he0 : ∀ r ∈ (⊥ : HomogeneousIdeal
        (homogeneousSubmodule (Fin 4) K)).toIdeal,
        r.eval₂ (algebraMap K Q) (x₀ i) = 0)
        (hX : (X (j i)).eval₂ (algebraMap K Q) (x₀ i) = 1),
        linearNormalizedPoint
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
          (x₀ i) (X (j i)) (isHomogeneous_X K (j i)) hX he0 ≫
        quotientProjMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)) =
        O.fromSpecResidueField z ≫
          (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
            (isSeparated_homogeneousToBase (equationIdeal p hp)) 8
            (hypersurfaceToAmbient p hp) i)) →
      (∀ i, (homogeneousLinearForm
        (fun k => algebraMap K Q (c k))).eval (x₀ i) ≠ 0) →
      z.val ∈ orderedFamilyCommonOpen (hypersurfaceToBase p hp)
        (Proj.basicOpen (grading (equationIdeal p hp))
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
            (homogeneousLinearForm c))) 8 := by
  dsimp only
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let Q := O.residueField z
  letI : Algebra K Q := pointAlgebra
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
  intro j x₀ c hxj hmarked hc
  refine (mem_orderedFamilyCommonOpen_iff
    (hypersurfaceToBase p hp)
    (Proj.basicOpen (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
        (homogeneousLinearForm c))) 8 z.val).mpr ?_
  intro i
  obtain ⟨he0, hX, hmarked_i⟩ := hmarked i
  have hc' : (homogeneousLinearForm c).eval₂
      (algebraMap K Q) (x₀ i) ≠ 0 := by
    simpa only [homogeneousLinearForm, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X] using hc i
  have hambient :
      (O.fromSpecResidueField z ≫
        (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
          (isSeparated_homogeneousToBase (equationIdeal p hp)) 8
          (hypersurfaceToAmbient p hp) i))
          (IsLocalRing.closedPoint Q) ∈
        Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
          (homogeneousLinearForm c) := by
    rw [← hmarked_i]
    exact linearNormalizedPoint_mem_basicOpen_of_eval₂_ne_zero
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
      (x₀ i) (j i) (hxj i) he0 (homogeneousLinearForm c)
      (homogeneousLinearForm_isHomogeneous c) hc'
  have hambient' :
      hypersurfaceToAmbient p hp
          (Over.Hom.left
            (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i) z.val) ∈
        Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
          (homogeneousLinearForm c) := by
    have hr : O.fromSpecResidueField z (IsLocalRing.closedPoint Q) = z :=
      Scheme.fromSpecResidueField_apply z (IsLocalRing.closedPoint Q)
    rw [show (O.fromSpecResidueField z ≫
      (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
        (isSeparated_homogeneousToBase (equationIdeal p hp)) 8
        (hypersurfaceToAmbient p hp) i))
          (IsLocalRing.closedPoint Q) =
        (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
          (isSeparated_homogeneousToBase (equationIdeal p hp)) 8
          (hypersurfaceToAmbient p hp) i) z by
      exact congrArg (fun w : O =>
        (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
          (isSeparated_homogeneousToBase (equationIdeal p hp)) 8
          (hypersurfaceToAmbient p hp) i) w) hr] at hambient
    change hypersurfaceToAmbient p hp
        (Over.Hom.left
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i)
            ((orderedFamilyConfigurationOpen
              (hypersurfaceToBase p hp) 8).ι z)) ∈
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
        (homogeneousLinearForm c) at hambient
    simpa only [show (orderedFamilyConfigurationOpen
      (hypersurfaceToBase p hp) 8).ι z = z.val by rfl] using hambient
  change Over.Hom.left
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i) z.val ∈
    hypersurfaceToAmbient p hp ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
        (homogeneousLinearForm c) at hambient'
  change Over.Hom.left
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i) z.val ∈
    Proj.basicOpen (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
        (homogeneousLinearForm c))
  change Over.Hom.left
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i) z.val ∈
    quotientProjMap (equationIdeal p hp) ⁻¹ᵁ
      Proj.basicOpen (homogeneousSubmodule (Fin 4) K)
        (homogeneousLinearForm c)
  exact hambient'

theorem SmoothCubicResidueSelectedPairFiniteAt.mem_commonLinearBasicOpen
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (h : SmoothCubicResidueSelectedPairFiniteAt p hp z) :
    ∃ c : Fin 4 → K,
      z.val ∈ orderedFamilyCommonOpen (hypersurfaceToBase p hp)
        (Proj.basicOpen (grading (equationIdeal p hp))
          (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
            (homogeneousLinearForm c))) 8 := by
  rcases h with ⟨j, x₀, c, m, hxj, hmarked, hm, hc, he, hfinite⟩
  exact ⟨c, residueCoordinates_mem_commonLinearBasicOpen
    p hp z j x₀ c hxj hmarked hc⟩

theorem exists_smoothCubic_residueSelectedPairFinite
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (cubic : Cubic K 4) (hcubic : cubic.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    ∃ z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase F hF) 8).left,
      SmoothCubicResidueSelectedPairFiniteAt F hF z := by
  let L : Type u := AlgebraicClosure K
  let b : K →+* L := algebraMap K L
  letI : Algebra K L := b.toAlgebra
  let pL : MvPolynomial (Fin 4) L := (cubic.map b).toMvPolynomial
  let hpL : pL.IsHomogeneous 3 :=
    cubic_toMvPolynomial_isHomogeneous_three (cubic.map b)
  obtain ⟨y, q, r, hq, hr, hsurj, hincidence, hy0, hdistinct,
    hq0, hr0, hlin, hfinite, htripleEtale⟩ :=
    exists_original_geometricEight_and_etale_quadratic_pair_of_smooth
      F hF hF0 cubic hcubic
  have hpmap : F.map b = pL := by
    dsimp only [pL]
    rw [← hcubic, cubic_toMvPolynomial_map]
  have hzeroF : ∀ i, (F.map b).eval (y i) = 0 := by
    intro i
    rw [hpmap]
    exact (hincidence i).1
  letI : Infinite L := CharZero.infinite L
  obtain ⟨ell, hell, points, A, B, D, hpoints, hpointsInj, hAbase,
    hAB, hBbase, hD, hDetale, ⟨E, hE⟩, hcoords⟩ :=
    exists_ordered_eight_finite_datum_of_cubic_vectors
      (F.map b) (hF.map b) y hzeroF hy0 hdistinct
  have hcoordA : ∀ i, (A ≫ Over.Hom.left
        (orderedFamilyConfigurationι
          (hypersurfaceToBase (F.map b) (hF.map b)) 8)) ≫
        (orderedFamilyCoordinate
          (hypersurfaceToBase (F.map b) (hF.map b)) 8 i).left =
      projectiveVectorSchemePointInLinearChart
        (equationIdeal (F.map b) (hF.map b)) ell (y i)
        (cubicVector_zero_equationIdeal
          (F.map b) (hF.map b) (y i) (hzeroF i)) (hell i) := by
    intro i
    exact (hcoords i).trans (hpoints i)
  obtain ⟨aK, haK, hcoordK₀⟩ :=
    exists_orderedCubicConfigurationFieldPoint_of_baseChangedConfiguration
      b F hF A (by simpa using hAbase)
  have hcoordK : ∀ i, (aK ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase F hF) 8)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase F hF) 8 i).left =
      cubicSurfaceAffinePointLinearNormalizedProjectivePoint
        (F.map b) (hF.map b) ell
        (⟨y i, by simpa using hzeroF i, hy0 i⟩ :
          cubicSurfaceAffinePoints (F.map b))
        (by simpa using hell i) ≫
      projectiveCoefficientMap b (equationIdeal F hF)
        (equationIdeal (F.map b) (hF.map b))
        (equationIdeal_map b F hF) := by
    intro i
    rw [hcoordK₀ i, hcoordA i]
    rfl
  obtain ⟨z, e, j, x₀, heSpec, hxj, hxmap, hmarked⟩ :=
    exists_residueCoordinates_of_originalCubic_geometricConfiguration
      b F hF y hzeroF hy0 ell hell
      aK haK hcoordK
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase F hF) 8).left
  let Q := O.residueField z
  letI : Algebra K Q := pointAlgebra
    (orderedFamilyConfigurationOver (hypersurfaceToBase F hF) 8).hom z
  letI : Algebra Q L := e.toRingHom.toAlgebra
  have htower : ∀ a : K,
      algebraMap Q L (algebraMap K Q a) = algebraMap K L a := by
    intro a
    change e (algebraMap K Q a) = algebraMap K L a
    exact e.commutes a
  let n : Fin 8 → Fin 4 → L := fun i =>
    cubicSurfaceAffinePointNormalizedConeCoordinates ell (y i)
  have hnj : ∀ i, n i (j i) ≠ 0 := by
    intro i hzeroj
    have h := hxmap i (j i)
    change e (x₀ i (j i)) = (n i (j i))⁻¹ * n i (j i) at h
    rw [hxj i, map_one, hzeroj, inv_zero, zero_mul] at h
    exact one_ne_zero h
  let s : Fin 8 → L := fun i =>
    (n i (j i))⁻¹ * ((homogeneousLinearForm ell).eval (y i))⁻¹
  have hs : ∀ i, s i ≠ 0 := by
    intro i
    exact mul_ne_zero (inv_ne_zero (hnj i)) (inv_ne_zero (hell i))
  have hscale : ∀ i k, algebraMap Q L (x₀ i k) = s i * y i k := by
    intro i k
    change e.toRingHom (x₀ i k) = s i * y i k
    have h := hxmap i k
    change e.toRingHom (x₀ i k) = _ at h
    rw [h]
    change (n i (j i))⁻¹ * n i k = s i * y i k
    dsimp only [n, s, cubicSurfaceAffinePointNormalizedConeCoordinates]
    simp only [Pi.smul_apply, smul_eq_mul, MvPolynomial.aeval_def,
      Algebra.algebraMap_self, MvPolynomial.eval₂_id]
    ring
  let pQ : MvPolynomial (Fin 4) Q := F.map (algebraMap K Q)
  let hpQ : pQ.IsHomogeneous 3 := hF.map (algebraMap K Q)
  have hpQL : pQ.map (algebraMap Q L) = pL := by
    calc
      pQ.map (algebraMap Q L) =
          F.map ((algebraMap Q L).comp (algebraMap K Q)) := by
        simp only [pQ, MvPolynomial.map_map]
      _ = F.map (algebraMap K L) := by
        rw [show (algebraMap Q L).comp (algebraMap K Q) =
            algebraMap K L by
          ext a
          exact htower a]
      _ = pL := hpmap
  have hIdeal : tripleCompleteIntersectionHomogeneousIdeal
      (pQ.map (algebraMap Q L)) q r
      (hpQ.map (algebraMap Q L)) hq hr =
      tripleCompleteIntersectionHomogeneousIdeal pL q r hpL hq hr := by
    apply HomogeneousIdeal.ext
    change Ideal.span ({pQ.map (algebraMap Q L), q, r} : Set _) =
      Ideal.span ({pL, q, r} : Set _)
    rw [hpQL]
  letI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (pQ.map (algebraMap Q L)) q r
      (hpQ.map (algebraMap Q L)) hq hr)) := by
    rw [hIdeal]
    exact hfinite
  obtain ⟨c, m, hm, hcQ, hcL, hxy, hfin⟩ :=
    residueCoordinates_selectedQuadraticPair_isFinite
      (K := K) htower x₀ j hxj y s hs hscale q r hq hr hlin hsurj
        (fun i => ⟨(hincidence i).2.1, (hincidence i).2.2⟩) pQ hpQ
  let cQ : Fin 4 → Q := fun k => algebraMap K Q (c k)
  let cL : Fin 4 → L := fun k => algebraMap K L (c k)
  let x : Fin 8 → Fin 4 → Q := fun i =>
    normalizedVectorInLinearChart cQ (x₀ i)
  have hxzero (i : Fin 8) : F.eval₂ (algebraMap K Q) (x i) = 0 := by
    rw [MvPolynomial.eval₂_eq_eval_map]
    apply (algebraMap Q L).injective
    rw [map_zero]
    calc
      algebraMap Q L (pQ.eval (x i)) =
          pQ.eval₂ (algebraMap Q L)
            (fun k => algebraMap Q L (x i k)) := by
        simpa only [MvPolynomial.eval₂_id, RingHom.comp_id] using
          (MvPolynomial.hom_eval₂ pQ (RingHom.id Q)
            (algebraMap Q L) (x i))
      _ = (pQ.map (algebraMap Q L)).eval
          (fun k => algebraMap Q L (x i k)) :=
        MvPolynomial.eval₂_eq_eval_map _ _ _
      _ = pL.eval (normalizedVectorInLinearChart cL (y i)) := by
        rw [hpQL]
        apply congrArg (fun v => pL.eval v)
        funext k
        exact hxy i k
      _ = 0 := by
        exact normalizedVectorInLinearChart_zero
          (equationIdeal pL hpL) cL (y i)
          (cubicVector_zero_equationIdeal pL hpL (y i)
            (hincidence i).1) pL (Ideal.mem_span_singleton_self pL)
  have he : ∀ i f, f ∈ (equationIdeal F hF).toIdeal →
      f.eval₂ (algebraMap K Q) (x i) = 0 := by
    intro i f hf
    change f ∈ Ideal.span ({F} : Set _) at hf
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
    rw [MvPolynomial.eval₂_mul, hxzero i, zero_mul]
  refine ⟨z, j, x₀, c, m, hxj, hmarked, hm, hcQ, he, ?_⟩
  exact hfin

end PfaffianDescent
