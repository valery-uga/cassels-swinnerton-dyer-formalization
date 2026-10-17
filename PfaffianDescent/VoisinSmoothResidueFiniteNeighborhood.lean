import PfaffianDescent.VoisinSmoothResidueSelectedPairFinite
import PfaffianDescent.VoisinSmoothCompatibleAffineCharts
import PfaffianDescent.VoisinSelectedVectorCoordinateSpecialization
import PfaffianDescent.VoisinSmoothSelectedFiniteNeighborhood
import PfaffianDescent.VoisinProjectivePointRenormalization
import PfaffianDescent.NormalizedProjectiveQuotientFactor

/-!
# Spreading the finite residue specialization

A finite canonical two-quadric intersection at the residue field of an
ordered configuration point spreads to an affine neighborhood over the
original cubic's ground field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The finite residue witness, expressed in the common ground-field linear
chart and identified with the actual eight marked points of the cubic. -/
def SmoothCubicResidueNormalizedPresentationAt
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left) : Prop :=
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let Q := O.residueField z
  letI : Algebra K Q := pointAlgebra
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
  ∃ (c : Fin 4 → K) (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → Q)
    (he : ∀ i f, f ∈ (equationIdeal p hp).toIdeal →
      f.eval₂ (algebraMap K Q) (x i) = 0),
    let zc := Ideal.Quotient.mk (equationIdeal p hp).toIdeal
      (homogeneousLinearForm c)
    let hzc := polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
    ∃ (hzOne : ∀ i, (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
        (eval₂Hom (algebraMap K Q) (x i)) (he i)) zc = 1)
      (hm : IsUnit (eightPointQuadraticEvaluationMinor m x).det),
      z.val ∈ orderedFamilyCommonOpen (hypersurfaceToBase p hp)
        (Proj.basicOpen (grading (equationIdeal p hp)) zc) 8 ∧
      (∀ i,
        (O.fromSpecResidueField z ≫ Over.Hom.left
          (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
          (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
        linearNormalizedPointAt (equationIdeal p hp) (x i) (he i)
          zc hzc (hzOne i)) ∧
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

/-- Renormalizing the descended coordinates by their common linear form
identifies them with the actual marked cubic points, while retaining the
finite selected quadratic pair. -/
theorem SmoothCubicResidueSelectedPairFiniteAt.normalizedPresentation
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (h : SmoothCubicResidueSelectedPairFiniteAt p hp z) :
    SmoothCubicResidueNormalizedPresentationAt p hp z := by
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let Q := O.residueField z
  letI : Algebra K Q := pointAlgebra
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
  rcases h with ⟨j, x₀, c, m, hxj, hmarked, hm, hc, he, hfinite⟩
  let cQ : Fin 4 → Q := fun k => algebraMap K Q (c k)
  let x : Fin 8 → Fin 4 → Q := fun i =>
    normalizedVectorInLinearChart cQ (x₀ i)
  let zc := Ideal.Quotient.mk (equationIdeal p hp).toIdeal
    (homogeneousLinearForm c)
  let hzc := polynomial_class_mem_grading (equationIdeal p hp)
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  have hzOne : ∀ i, (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K Q) (x i)) (he i)) zc = 1 := by
    intro i
    change (homogeneousLinearForm c).eval₂ (algebraMap K Q) (x i) = 1
    simpa only [homogeneousLinearForm, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
      map_sum, map_mul, map_one] using
      normalizedVectorInLinearChart_eval_one cQ (x₀ i) (hc i)
  have hcoord : ∀ i,
      (O.fromSpecResidueField z ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 i).left =
      linearNormalizedPointAt (equationIdeal p hp) (x i) (he i)
        zc hzc (hzOne i) := by
    intro i
    obtain ⟨he0, hX, hmarked_i⟩ := hmarked i
    obtain ⟨hvone, hvzero, hrenorm⟩ :=
      linearNormalizedPoint_eq_normalizedVectorInLinearChart
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
        (x₀ i) (j i) (hxj i) he0 c (hc i)
    have hellne : (homogeneousLinearForm c).eval₂
        (algebraMap K Q) (x₀ i) ≠ 0 := by
      simpa only [homogeneousLinearForm, MvPolynomial.eval_sum,
        MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
        MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
        MvPolynomial.eval₂_C, MvPolynomial.eval₂_X] using hc i
    have hxscale : x₀ i =
        (homogeneousLinearForm c).eval₂ (algebraMap K Q) (x₀ i) • x i := by
      funext k
      simp only [x, normalizedVectorInLinearChart, Pi.smul_apply,
        smul_eq_mul]
      have ha : (homogeneousLinearForm cQ).eval (x₀ i) =
          (homogeneousLinearForm c).eval₂ (algebraMap K Q) (x₀ i) := by
        simp only [homogeneousLinearForm, MvPolynomial.eval_sum,
          MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
          MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
          MvPolynomial.eval₂_C, MvPolynomial.eval₂_X]
        rfl
      rw [ha, ← mul_assoc, mul_inv_cancel₀ hellne, one_mul]
    have hraw : ∀ f ∈ (equationIdeal p hp).toIdeal,
        f.eval₂ (algebraMap K Q) (x₀ i) = 0 := by
      intro f hf
      change f ∈ Ideal.span ({p} : Set _) at hf
      obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hf
      rw [MvPolynomial.eval₂_mul]
      have hpraw : p.eval₂ (algebraMap K Q) (x₀ i) = 0 := by
        rw [hxscale, AllCharacteristics.eval₂_homogeneous_smul p hp,
          he i p (Ideal.mem_span_singleton_self p), mul_zero]
      rw [hpraw, zero_mul]
    obtain ⟨hwone, hwzero, hrenormI⟩ :=
      linearNormalizedPoint_eq_normalizedVectorInLinearChart
        (equationIdeal p hp) (x₀ i) (j i) (hxj i) hraw c (hc i)
    apply (cancel_mono (hypersurfaceToAmbient p hp)).mp
    rw [linearNormalizedPointAt_mk_eq_linearNormalizedPoint
      (equationIdeal p hp) (x i) (he i) (homogeneousLinearForm c)
      (homogeneousLinearForm_isHomogeneous c) (hzOne i)]
    change (O.fromSpecResidueField z ≫
      (@orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal p hp)) _ (hypersurfaceToBase p hp)
        (isSeparated_homogeneousToBase (equationIdeal p hp)) 8
        (hypersurfaceToAmbient p hp) i)) = _
    rw [← hmarked_i]
    have hamb := linearNormalizedPoint_quotientProjMap_eq_bot
      (equationIdeal p hp) (x₀ i) (j i) hraw (hxj i)
    rw [← hamb, hrenormI]
    rfl
  have hmem : z.val ∈ orderedFamilyCommonOpen (hypersurfaceToBase p hp)
      (Proj.basicOpen (grading (equationIdeal p hp)) zc) 8 :=
    residueCoordinates_mem_commonLinearBasicOpen
      p hp z j x₀ c hxj hmarked hc
  exact ⟨c, m, x, he, hzOne, hm, hmem, hcoord, hfinite⟩

/-- A finite canonical selected pair at a field-valued specialization
spreads to a generic finite neighborhood of the selected frame. -/
theorem homogeneousSectionRestriction_surjective_of_unit_minor
    {F : Type u} [Field F]
    (x : Fin 8 → Fin 4 → F)
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m x).det) :
    Function.Surjective (homogeneousSectionRestriction (K := F)
      (fun j i => x i j : Fin 4 → Fin 8 → F) 2) := by
  let M := eightPointQuadraticEvaluationMatrix x
  have hunit : IsUnit (M.submatrix id m) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr hm
  have hminor : (M.submatrix id m).rank = 8 := by
    simpa using Matrix.rank_of_isUnit (M.submatrix id m) hunit
  have hlow : 8 ≤ M.rank := by
    simpa only [hminor] using Matrix.rank_submatrix_le M id m
  have hhigh : M.rank ≤ 8 := by
    simpa using Matrix.rank_le_card_height M
  have hrank : M.rank = 8 := le_antisymm hhigh hlow
  have hrange : Module.finrank F
      (LinearMap.range (Matrix.toLin' M)) = 8 :=
    (Matrix.rank_eq_finrank_range_toLin M
      (Pi.basisFun F (Fin 8))
      (Pi.basisFun F (Monomials (Fin 4) 2))).symm.trans hrank
  have hsurjM : Function.Surjective (Matrix.toLin' M) := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    exact hrange.trans (by simp)
  intro z
  obtain ⟨a, ha⟩ := hsurjM z
  let q : MvPolynomial (Fin 4) F :=
    ∑ n : Monomials (Fin 4) 2, MvPolynomial.monomial n.1 (a n)
  have hq : q.IsHomogeneous 2 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro n hn
    exact MvPolynomial.isHomogeneous_monomial (a n) n.2
  refine ⟨⟨q, hq⟩, ?_⟩
  funext i
  calc
    homogeneousSectionRestriction (K := F)
        (fun j i => x i j : Fin 4 → Fin 8 → F) 2 ⟨q, hq⟩ i =
        q.eval (x i) := by
      simp [homogeneousSectionRestriction_apply,
        finite_product_evaluation_apply]
    _ = (Matrix.toLin' M a) i := by
      simp [q, M, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        eightPointQuadraticEvaluationMatrix,
        MvPolynomial.eval_monomial, mul_comm]
    _ = z i := congrFun ha i

theorem quadraticSelectedOpenFrame_exists_genericFiniteNeighborhood_of_canonical
    {R : Type u} [CommRing R] [IsDomain R]
    {F : Type u} [Field F]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (y : Fin 8 → Fin 4 → R) (f : R →+* F)
    (hm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (y k j))).det)
    [IsDomain (Localization.Away (quadraticMinorDet m y))]
    (x : Fin 8 → Fin 4 → F)
    (hx : ∀ k j, f (y k j) = x k j)
    (c : Fin 4 → F)
    (hcOne : ∀ k, (homogeneousLinearForm c).eval (x k) = 1)
    (hid : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i k => (RingHom.id F) (x i k))).det)
    (p : MvPolynomial (Fin 4)
      (Localization.Away (quadraticMinorDet m y)))
    (hp : p.IsHomogeneous 3)
    (pF : MvPolynomial (Fin 4) F) (hpF : pF.IsHomogeneous 3)
    (hpmap : p.map (quadraticMinorSelectedPointLift m y f hm) = pF)
    (hfinite :
      let b := quadraticSelectedOpenBasisSpecializedBasis
        m x (RingHom.id F) hid
      IsFinite (relativeTripleIntersectionToBase
        pF
        (quadraticPolynomialOfCoefficients (b 0).1)
        (quadraticPolynomialOfCoefficients (b 1).1) hpF
        (quadraticPolynomialOfCoefficients_isHomogeneous (b 0).1)
        (quadraticPolynomialOfCoefficients_isHomogeneous (b 1).1))) :
    ∃ V : (Spec (.of
        (Localization.Away (quadraticMinorDet m y)))).Opens,
      genericPoint (Spec (.of
        (Localization.Away (quadraticMinorDet m y)))) ∈ V ∧
      IsFinite ((relativeTripleIntersectionToBase p
        (quadraticSelectedOpenPolynomial m y 0)
        (quadraticSelectedOpenPolynomial m y 1) hp
        (quadraticSelectedOpenPolynomial_isHomogeneous m y 0)
        (quadraticSelectedOpenPolynomial_isHomogeneous m y 1)) ∣_ V) := by
  have hxy : (fun k j => f (y k j)) = x := by
    funext k j
    exact hx k j
  subst x
  subst pF
  let g := quadraticMinorSelectedPointLift m y f hm
  let b := quadraticSelectedOpenBasisSpecializedBasis
    m (fun k j => f (y k j)) (RingHom.id F) hid
  let q := quadraticPolynomialOfCoefficients (b 0).1
  let r := quadraticPolynomialOfCoefficients (b 1).1
  let hq := quadraticPolynomialOfCoefficients_isHomogeneous (b 0).1
  let hr := quadraticPolynomialOfCoefficients_isHomogeneous (b 1).1
  have hbfun :
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) F 2), ⟨r, hr⟩] =
        quadraticSelectedOpenBasisSpecializedHomogeneous
          m (fun k j => f (y k j)) (RingHom.id F) hid := by
    funext i
    fin_cases i <;>
      simp [q, r, hq, hr, b,
        quadraticSelectedOpenBasisSpecializedHomogeneous,
        quadraticSelectedOpenBasisSpecializedBasis_apply]
  have hlin : LinearIndependent F
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) F 2), ⟨r, hr⟩] := by
    rw [hbfun]
    exact quadraticSelectedOpenBasisSpecializedHomogeneous_linearIndependent
      m (fun k j => f (y k j)) (RingHom.id F) hid
  have hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := F)
        (fun j k => f (y k j) : Fin 4 → Fin 8 → F) 2) :=
    homogeneousSectionRestriction_surjective_of_unit_minor
      (fun k j => f (y k j)) m (by simpa only [RingHom.id_apply] using hid)
  have hquad : ∀ k,
      q.eval ((fun k j => f (y k j)) k) = 0 ∧
      r.eval ((fun k j => f (y k j)) k) = 0 := by
    have hqeq : q = quadraticPolynomialOfCoefficients
        (quadraticSelectedOpenBasisSpecializedVector
          m (fun k j => f (y k j)) (RingHom.id F) hid 0).1 := by
      simp only [q, b, quadraticSelectedOpenBasisSpecializedBasis_apply]
    have hreq : r = quadraticPolynomialOfCoefficients
        (quadraticSelectedOpenBasisSpecializedVector
          m (fun k j => f (y k j)) (RingHom.id F) hid 1).1 := by
      simp only [r, b, quadraticSelectedOpenBasisSpecializedBasis_apply]
    rw [hqeq, hreq]
    intro k
    exact ⟨
      (quadraticSelectedOpenBasisSpecializedVector_polynomial_data
        m (fun k j => f (y k j)) (RingHom.id F) hid 0).2 k,
      (quadraticSelectedOpenBasisSpecializedVector_polynomial_data
        m (fun k j => f (y k j)) (RingHom.id F) hid 1).2 k⟩
  have hc : ∀ k, (homogeneousLinearForm c).eval
      ((fun k j => f (y k j)) k) ≠ 0 := by
    intro k
    rw [hcOne k]
    exact one_ne_zero
  have hfx : ∀ k j, f (y k j) =
      normalizedVectorInLinearChart c ((fun k j => f (y k j)) k) j := by
    intro k j
    simp only [normalizedVectorInLinearChart, Pi.smul_apply, smul_eq_mul,
      hcOne k, inv_one, one_mul]
  haveI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map g) q r (hp.map g) hq hr)) := by
    exact hfinite
  exact quadraticSelectedOpenFrame_exists_genericFiniteNeighborhood_of_pair
    m y f hm (fun k j => f (y k j)) c hc hfx hsurj
      q r hq hr hlin hquad p hp

/-- The finite selected residue specialization of a smooth cubic spreads
over an affine chart of the original ordered configuration space. -/
theorem nonempty_selectedActualFiniteNeighborhoodData_of_residue
    {K : Type u} [Field K] [CharZero K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).left)
    (h : SmoothCubicResidueSelectedPairFiniteAt p hp z) :
    Nonempty (SelectedActualFiniteNeighborhoodData p hp) := by
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  let E := O.residueField z
  letI : Algebra K E := pointAlgebra
    (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom z
  obtain ⟨c, m, xE, he, hzOne, hm, hmem, hcoord, hfinite⟩ :=
    h.normalizedPresentation p hp z
  let hInt : IsIntegral (cubicConfigurationBase p hp 8) :=
    isIntegral_cubicConfigurationBase_of_smooth p hp hp0
  letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
  let hOrdered : IsIntegral O :=
    isIntegral_orderedCubicConfiguration_of_smooth p hp hp0
  letI : IsIntegral O := hOrdered
  let zc := Ideal.Quotient.mk (equationIdeal p hp).toIdeal
    (homogeneousLinearForm c)
  let hzc := polynomial_class_mem_grading (equationIdeal p hp)
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  let V : (hypersurface p hp).affineOpens :=
    ⟨Proj.basicOpen (grading (equationIdeal p hp)) zc,
      Proj.isAffineOpen_basicOpen (grading (equationIdeal p hp)) zc
        hzc (by decide : 0 < 1)⟩
  obtain ⟨U, Q, hUa, hQa, i, j, r, hi, hj, hsurjr, hintr, hfinr,
      hzi, hzj, hgeneric, hcomm, hinside⟩ :=
    exists_cubicConfiguration_compatible_affineCharts_inside_commonOpen_at_point
      p hp V z (by simpa only [V] using hmem)
  letI : IsOpenImmersion i := hi
  letI : IsOpenImmersion j := hj
  letI : Nonempty U := ⟨Classical.choose hzi⟩
  letI : Nonempty Q := ⟨Classical.choose hzj⟩
  let hUi : IsIntegral U := isIntegral_of_isOpenImmersion i
  let hQi : IsIntegral Q := isIntegral_of_isOpenImmersion j
  let jlin := Proj.awayι (grading (equationIdeal p hp)) zc hzc
    (by decide : 0 < 1)
  haveI : IsOpenImmersion jlin := by
    dsimp only [jlin]
    infer_instance
  have hcommon : ∀ u : U, (i u).val ∈
      orderedFamilyCommonOpen (hypersurfaceToBase p hp)
        jlin.opensRange 8 := by
    intro u
    rw [Proj.opensRange_awayι]
    exact hinside u
  have hlifts := @exists_orderedConfiguration_coordinate_lifts
    _ _ U _ (hypersurfaceToBase p hp)
    (isSeparated_homogeneousToBase (equationIdeal p hp))
    jlin (show IsOpenImmersion jlin from inferInstance) i hcommon
  let t : Fin 8 → (U ⟶ Spec (.of (Away
      (grading (equationIdeal p hp)) zc))) := fun k =>
    Classical.choose (hlifts k)
  have ht : ∀ k, t k ≫ Proj.awayι
      (grading (equationIdeal p hp)) zc hzc (by decide : 0 < 1) =
      (i ≫ Over.Hom.left
        (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left := by
    intro k
    exact Classical.choose_spec (hlifts k)
  have hrange : Set.range (O.fromSpecResidueField z) ⊆ Set.range i := by
    rintro w ⟨s, rfl⟩
    have hs : O.fromSpecResidueField z s = z :=
      Scheme.fromSpecResidueField_apply z s
    rw [hs]
    exact hzi
  let a : Spec (.of E) ⟶ U :=
    IsOpenImmersion.lift i (O.fromSpecResidueField z) hrange
  have ha : a ≫ i = O.fromSpecResidueField z :=
    IsOpenImmersion.lift_fac i (O.fromSpecResidueField z) hrange
  let x := pulledEightLinearChartCoordinates
    (equationIdeal p hp) zc hzc U t
  have hxval : ∀ k l, a.appTop.hom (x k l) =
      (StructureSheaf.globalSectionsIso E).hom (xE k l) :=
    pulledEightLinearChartCoordinates_value_of_normalizedConfiguration
      (equationIdeal p hp) zc hzc xE he hzOne U i
      (O.fromSpecResidueField z) a ha t ht hcoord
  let f : Γ(U, ⊤) →+* E :=
    (Scheme.ΓSpecIso (.of E)).hom.hom.comp a.appTop.hom
  have hf : ∀ k l, f (x k l) = xE k l := by
    intro k l
    have hv := congrArg
      (fun v : Γ(Spec (.of E), ⊤) =>
        (Scheme.ΓSpecIso (.of E)).hom.hom v) (hxval k l)
    exact hv.trans ((Scheme.ΓSpecIso (.of E)).inv_hom_id_apply _)
  have hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k l => f (x k l))).det := by
    convert hm using 1
    congr 2
    funext k l
    exact hf k l
  have hdet : quadraticMinorDet m x ≠ 0 :=
    quadraticMinorDet_ne_zero_of_specialized_unit m x f hminor
  let S := Localization.Away (quadraticMinorDet m x)
  letI : IsDomain S := Localization.Away.isDomain hdet
  let tBase : U ⟶ Spec (.of K) :=
    i ≫ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).hom
  have hat : a ≫ tBase = Spec.map (CommRingCat.ofHom (algebraMap K E)) := by
    dsimp only [tBase]
    rw [← Category.assoc, ha]
    exact (pointAlgebra_spec
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom z).symm
  let β : K →+* Γ(U, ⊤) := affineFunctionHom tBase
  have hβ : f.comp β = algebraMap K E := by
    ext v
    have hh := congrArg affineFunctionHom hat
    rw [affineFunctionHom_comp] at hh
    have hv := RingHom.congr_fun hh v
    have hv' := congrArg
      (fun w : Γ(Spec (.of E), ⊤) =>
        (Scheme.ΓSpecIso (.of E)).hom.hom w) hv
    calc
      f (β v) = (Scheme.ΓSpecIso (.of E)).hom.hom
          (affineFunctionHom
            (Spec.map (CommRingCat.ofHom (algebraMap K E))) v) := by
        simpa only [f, β, RingHom.comp_apply] using hv'
      _ = algebraMap K E v := by
        have hs := RingHom.congr_fun
          (affineFunctionHom_comp_Spec (𝟙 (Spec (.of E)))
            (algebraMap K E)) v
        simp only [Category.id_comp] at hs
        rw [hs]
        change (Scheme.ΓSpecIso (.of E)).hom.hom
          ((Scheme.ΓSpecIso (.of E)).inv.hom (algebraMap K E v)) = _
        exact (Scheme.ΓSpecIso (.of E)).inv_hom_id_apply _
  let βS : K →+* S := (algebraMap Γ(U, ⊤) S).comp β
  let pS := p.map βS
  let hpS := hp.map βS
  let g := quadraticMinorSelectedPointLift m x f hminor
  have hg : g.comp (algebraMap Γ(U, ⊤) S) = f :=
    quadraticMinorSelectedPointLift_comp m x f hminor
  have hgβ : g.comp βS = algebraMap K E := by
    rw [show g.comp βS =
      (g.comp (algebraMap Γ(U, ⊤) S)).comp β by rfl, hg, hβ]
  let pE := p.map (algebraMap K E)
  let hpE := hp.map (algebraMap K E)
  have hpmap : pS.map g = pE := by
    change (p.map βS).map g = p.map (algebraMap K E)
    rw [MvPolynomial.map_map, hgβ]
  let cE : Fin 4 → E := fun k => algebraMap K E (c k)
  have hcOne : ∀ k, (homogeneousLinearForm cE).eval (xE k) = 1 := by
    intro k
    have hk := hzOne k
    change (homogeneousLinearForm c).eval₂
      (algebraMap K E) (xE k) = 1 at hk
    simpa only [cE, homogeneousLinearForm, MvPolynomial.eval_sum,
      MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul,
      MvPolynomial.eval₂_C, MvPolynomial.eval₂_X] using hk
  let hid : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i k => (RingHom.id E) (xE i k))).det := by
    change IsUnit (eightPointQuadraticEvaluationMinor m xE).det
    exact hm
  obtain ⟨W, hW, hfin⟩ :=
    quadraticSelectedOpenFrame_exists_genericFiniteNeighborhood_of_canonical
      m x f hminor xE hf cE hcOne hid pS hpS pE hpE hpmap hfinite
  exact ⟨{
    baseIntegral := hInt
    U := U
    Q := Q
    integralU := hUi
    integralQ := hQi
    i := i
    j := j
    s := r
    openI := hi
    openJ := hj
    surjectiveS := hsurjr
    comm := hcomm
    c := c
    m := m
    t := t
    x := x
    x_eq := rfl
    lifts := ht
    minor_ne := hdet
    V := W
    generic_mem := hW
    finite := hfin }⟩

end PfaffianDescent
