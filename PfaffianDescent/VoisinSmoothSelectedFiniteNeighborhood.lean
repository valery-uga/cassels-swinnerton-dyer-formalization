import PfaffianDescent.VoisinSelectedEightCoordinateSectionWitness
import PfaffianDescent.VoisinSelectedRelativeFiniteNeighborhood
import PfaffianDescent.VoisinSelectedCubicCoefficientMap
import PfaffianDescent.VoisinSmoothOriginalEightFiniteDatum

/-!
# A finite selected neighborhood from an arbitrary smooth-cubic witness

An arbitrary independent quadratic pair cutting out a finite specialization
of eight selected points spreads to the regular selected frame on an affine
ordered-configuration chart.  This removes the former dependence on the
hard-coded generic cubic and split quadratic pair.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem smooth_hypersurfaceToBase_of_polynomial_eq
    {L : Type u} [Field L]
    (p q : MvPolynomial (Fin 4) L)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (h : p = q) [Smooth (hypersurfaceToBase p hp)] :
    Smooth (hypersurfaceToBase q hq) := by
  subst q
  infer_instance

/-- The chart, coordinate, minor, and relative-finiteness data needed by the
actual canonical generic-eight comparison. -/
structure SelectedActualFiniteNeighborhoodData
    {L : Type u} [Field L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) where
  baseIntegral : IsIntegral (cubicConfigurationBase p hp 8)
  U : Scheme.{u}
  Q : Scheme.{u}
  integralU : IsIntegral U
  integralQ : IsIntegral Q
  i : U ⟶ (orderedFamilyConfigurationOver
    (hypersurfaceToBase p hp) 8).left
  j : Q ⟶ cubicConfigurationBase p hp 8
  s : U ⟶ Q
  openI : IsOpenImmersion i
  openJ : IsOpenImmersion j
  surjectiveS : Surjective s
  comm : i ≫ configurationQuotientMap (equationIdeal p hp) 8 = s ≫ j
  c : Fin 4 → L
  m : Fin 8 ↪ Monomials (Fin 4) 2
  t : Fin 8 → (U ⟶ Spec (.of
    (Away (grading (equationIdeal p hp))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
        (homogeneousLinearForm c)))))
  x : Fin 8 → Fin 4 → Γ(U, ⊤)
  x_eq : x = pulledEightLinearChartCoordinates
    (equationIdeal p hp)
    (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
      (homogeneousLinearForm c))
    (polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)) U t
  lifts : ∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp))
    (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
      (homogeneousLinearForm c))
    (polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c))
    (by decide : 0 < 1) =
      (i ≫ Over.Hom.left (orderedFamilyConfigurationι
        (hypersurfaceToBase p hp) 8)) ≫
        (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left
  minor_ne : quadraticMinorDet m x ≠ 0
  V : (Spec (.of (Localization.Away (quadraticMinorDet m x)))).Opens
  generic_mem :
    let S := Localization.Away (quadraticMinorDet m x)
    letI : IsDomain S := Localization.Away.isDomain minor_ne
    genericPoint (Spec (.of S)) ∈ V
  finite :
    let S := Localization.Away (quadraticMinorDet m x)
    letI : IsDomain S := Localization.Away.isDomain minor_ne
    let β : L →+* Γ(U, ⊤) := affineFunctionHom
      (i ≫ (orderedFamilyConfigurationOver
        (hypersurfaceToBase p hp) 8).hom)
    let βS : L →+* S := (algebraMap Γ(U, ⊤) S).comp β
    IsFinite ((relativeTripleIntersectionToBase (p.map βS)
      (quadraticSelectedOpenPolynomial m x 0)
      (quadraticSelectedOpenPolynomial m x 1) (hp.map βS)
      (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
      (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)) ∣_ V)

theorem exists_selected_actual_finiteNeighborhood_of_quadratic_pair
    {L : Type u} [Field L] [CharZero L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (y : Fin 8 → Fin 4 → L) (hzero : ∀ k, p.eval (y k) = 0)
    (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (q r : MvPolynomial (Fin 4) L)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩])
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => y k j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ k, q.eval (y k) = 0 ∧ r.eval (y k) = 0)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
    (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcoord : ∀ k, (A ≫ Over.Hom.left
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left =
        projectiveVectorSchemePointInLinearChart
          (equationIdeal p hp) c (y k)
          (cubicVector_zero_equationIdeal p hp (y k) (hzero k)) (hc k))
    (hAbase : A ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom = 𝟙 _)
    (hAB : A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B)
    (hEt : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp))
    (htriple : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    ∃ (hInt : IsIntegral (cubicConfigurationBase p hp 8)),
      letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
      ∃ (U Q : Scheme.{u})
        (hU : IsIntegral U) (hQ : IsIntegral Q)
        (i : U ⟶ (orderedFamilyConfigurationOver
          (hypersurfaceToBase p hp) 8).left)
        (j : Q ⟶ cubicConfigurationBase p hp 8)
        (s : U ⟶ Q)
        (hi : IsOpenImmersion i) (hj : IsOpenImmersion j)
        (hsurjs : Surjective s)
        (hcomm : i ≫ configurationQuotientMap (equationIdeal p hp) 8 =
          s ≫ j)
        (m : Fin 8 ↪ Monomials (Fin 4) 2)
        (t : Fin 8 → (U ⟶ Spec (.of
          (Away (grading (equationIdeal p hp))
            (Ideal.Quotient.mk (equationIdeal p hp).toIdeal
              (homogeneousLinearForm c)))))),
        let zc := Ideal.Quotient.mk (equationIdeal p hp).toIdeal
          (homogeneousLinearForm c)
        let hzc := polynomial_class_mem_grading (equationIdeal p hp)
          (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
        let x := pulledEightLinearChartCoordinates
          (equationIdeal p hp) zc hzc U t
        (∀ k, t k ≫ Proj.awayι (grading (equationIdeal p hp)) zc hzc
          (by decide : 0 < 1) =
            (i ≫ Over.Hom.left (orderedFamilyConfigurationι
              (hypersurfaceToBase p hp) 8)) ≫
              (orderedFamilyCoordinate
                (hypersurfaceToBase p hp) 8 k).left) ∧
        ∃ hdet : quadraticMinorDet m x ≠ 0,
          let S := Localization.Away (quadraticMinorDet m x)
          letI : IsDomain S := Localization.Away.isDomain hdet
          let β : L →+* Γ(U, ⊤) := affineFunctionHom
            (i ≫ (orderedFamilyConfigurationOver
              (hypersurfaceToBase p hp) 8).hom)
          let βS : L →+* S := (algebraMap Γ(U, ⊤) S).comp β
          let pS := p.map βS
          let hpS := hp.map βS
          ∃ V : (Spec (.of S)).Opens,
            genericPoint (Spec (.of S)) ∈ V ∧
            IsFinite ((relativeTripleIntersectionToBase pS
              (quadraticSelectedOpenPolynomial m x 0)
              (quadraticSelectedOpenPolynomial m x 1) hpS
              (quadraticSelectedOpenPolynomial_isHomogeneous m x 0)
              (quadraticSelectedOpenPolynomial_isHomogeneous m x 1)) ∣_ V) := by
  letI : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp) := hEt
  obtain ⟨hInt, U, Q, hUa, hQa, i, j, s, hi, hj, hsurjs, hints, hfins,
    hU, hQ, hAi, hBj, hgeneric, hcomm, hinside, ⟨a, ha⟩, ht⟩ :=
    exists_selectedEight_commonAffineCharts_of_smooth
      p hp hp0 D y hzero c hc A B hcoord hAB
  letI : IsIntegral (cubicConfigurationBase p hp 8) := hInt
  letI : IsIntegral U := hU
  letI : IsIntegral Q := hQ
  letI : IsOpenImmersion i := hi
  letI : IsOpenImmersion j := hj
  letI : Surjective s := hsurjs
  obtain ⟨m, hm⟩ :=
    exists_unit_eightPointQuadraticEvaluationMinor_of_surjective y
      (eightPointQuadraticEvaluationMatrix_surjective_of_restriction y hsurj)
  let t (k : Fin 8) := Classical.choose (ht k)
  have ht' (k : Fin 8) := Classical.choose_spec (ht k)
  let zc : CoordinateRing (equationIdeal p hp) :=
    Ideal.Quotient.mk (equationIdeal p hp).toIdeal (homogeneousLinearForm c)
  have hzc : zc ∈ grading (equationIdeal p hp) 1 :=
    polynomial_class_mem_grading (equationIdeal p hp)
      (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  let x := pulledEightLinearChartCoordinates
    (equationIdeal p hp) zc hzc U t
  have hy (k : Fin 8) :
      ∀ v ∈ (equationIdeal p hp).toIdeal, v.eval (y k) = 0 :=
    cubicVector_zero_equationIdeal p hp (y k) (hzero k)
  have hx : ∀ k j, a.appTop.hom (x k j) =
      (StructureSheaf.globalSectionsIso L).hom
        (normalizedVectorInLinearChart c (y k) j) :=
    pulledEightLinearChartCoordinates_value_of_selectedConfiguration
      (equationIdeal p hp) c y hy hc U i A a ha t ht' hcoord
  let f : Γ(U, ⊤) →+* L :=
    (Scheme.ΓSpecIso (.of L)).hom.hom.comp a.appTop.hom
  have hf (k : Fin 8) (j : Fin 4) :
      f (x k j) = normalizedVectorInLinearChart c (y k) j := by
    have h := congrArg
      (fun v : Γ(Spec (.of L), ⊤) =>
        (Scheme.ΓSpecIso (.of L)).hom.hom v) (hx k j)
    exact h.trans ((Scheme.ΓSpecIso (.of L)).inv_hom_id_apply _)
  have hnorm : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k => normalizedVectorInLinearChart c (y k))).det :=
    eightPointQuadraticEvaluationMinor_isUnit_det_normalized y c hc m hm
  have hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun k j => f (x k j))).det := by
    convert hnorm using 1
    congr 2
    funext k j
    exact hf k j
  have hdet : quadraticMinorDet m x ≠ 0 :=
    quadraticMinorDet_ne_zero_of_specialized_unit m x f hminor
  let S := Localization.Away (quadraticMinorDet m x)
  letI : IsDomain S := Localization.Away.isDomain hdet
  let tBase : U ⟶ Spec (.of L) :=
    i ≫ (orderedFamilyConfigurationOver
      (hypersurfaceToBase p hp) 8).hom
  have hat : a ≫ tBase = 𝟙 (Spec (.of L)) := by
    dsimp only [tBase]
    rw [← Category.assoc, ha]
    exact hAbase
  let β : L →+* Γ(U, ⊤) := affineFunctionHom tBase
  have hβ : f.comp β = RingHom.id L := by
    exact affineFunctionHom_section_leftInverse tBase a hat
  let βS : L →+* S := (algebraMap Γ(U, ⊤) S).comp β
  let pS := p.map βS
  let hpS := hp.map βS
  let g := quadraticMinorSelectedPointLift m x f hminor
  have hg : g.comp (algebraMap Γ(U, ⊤) S) = f :=
    quadraticMinorSelectedPointLift_comp m x f hminor
  have hgβ : g.comp βS = RingHom.id L := by
    rw [show g.comp βS =
      (g.comp (algebraMap Γ(U, ⊤) S)).comp β by rfl, hg, hβ]
  have hpmap : pS.map g = p := by
    change (p.map βS).map g = p
    rw [MvPolynomial.map_map, hgβ, MvPolynomial.map_id]
  have hideal : tripleCompleteIntersectionHomogeneousIdeal
      (pS.map g) q r (hpS.map g) hq hr =
      tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
    apply HomogeneousIdeal.ext
    change Ideal.span ({pS.map g, q, r} : Set _) =
      Ideal.span ({p, q, r} : Set _)
    rw [hpmap]
  haveI : IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (pS.map g) q r (hpS.map g) hq hr)) := by
    rw [hideal]
    exact htriple
  obtain ⟨V, hV, hfin⟩ :=
    quadraticSelectedOpenFrame_exists_genericFiniteNeighborhood_of_pair
      m x f hminor y c hc hf hsurj q r hq hr hlin hquad pS hpS
  exact ⟨hInt, U, Q, hU, hQ, i, j, s, hi, hj, hsurjs, hcomm, m, t,
    ht', hdet, V, hV, hfin⟩

/-- Structure-valued form of the arbitrary-pair finite-neighborhood
construction. -/
theorem nonempty_selectedActualFiniteNeighborhoodData_of_quadratic_pair
    {L : Type u} [Field L] [CharZero L]
    (p : MvPolynomial (Fin 4) L) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (y : Fin 8 → Fin 4 → L) (hzero : ∀ k, p.eval (y k) = 0)
    (c : Fin 4 → L)
    (hc : ∀ k, (homogeneousLinearForm c).eval (y k) ≠ 0)
    (q r : MvPolynomial (Fin 4) L)
    (hq : q.IsHomogeneous 2) (hr : r.IsHomogeneous 2)
    (hlin : LinearIndependent L
      ![(⟨q, hq⟩ : homogeneousSubmodule (Fin 4) L 2), ⟨r, hr⟩])
    (hsurj : Function.Surjective
      (homogeneousSectionRestriction (K := L)
        (fun j k => y k j : Fin 4 → Fin 8 → L) 2))
    (hquad : ∀ k, q.eval (y k) = 0 ∧ r.eval (y k) = 0)
    (A : Spec (.of L) ⟶
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).left)
    (B : Spec (.of L) ⟶ cubicConfigurationBase p hp 8)
    (D : FiniteSubschemeDatum (hypersurfaceToBase p hp) 8)
    (hcoord : ∀ k, (A ≫ Over.Hom.left
      (orderedFamilyConfigurationι (hypersurfaceToBase p hp) 8)) ≫
      (orderedFamilyCoordinate (hypersurfaceToBase p hp) 8 k).left =
        projectiveVectorSchemePointInLinearChart
          (equationIdeal p hp) c (y k)
          (cubicVector_zero_equationIdeal p hp (y k) (hzero k)) (hc k))
    (hAbase : A ≫
      (orderedFamilyConfigurationOver (hypersurfaceToBase p hp) 8).hom = 𝟙 _)
    (hAB : A ≫ configurationQuotientMap (equationIdeal p hp) 8 = B)
    (hEt : Etale (D.val.subschemeι ≫ hypersurfaceToBase p hp))
    (htriple : IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    Nonempty (SelectedActualFiniteNeighborhoodData p hp) := by
  obtain ⟨hInt, U, Q, hU, hQ, i, j, s, hi, hj, hsurjs, hcomm, m, t,
    ht, hdet, V, hV, hfin⟩ :=
    exists_selected_actual_finiteNeighborhood_of_quadratic_pair
      p hp hp0 y hzero c hc q r hq hr hlin hsurj hquad A B D
      hcoord hAbase hAB hEt htriple
  let zc := Ideal.Quotient.mk (equationIdeal p hp).toIdeal
    (homogeneousLinearForm c)
  let hzc := polynomial_class_mem_grading (equationIdeal p hp)
    (homogeneousLinearForm c) (homogeneousLinearForm_isHomogeneous c)
  let x := pulledEightLinearChartCoordinates
    (equationIdeal p hp) zc hzc U t
  exact ⟨{
    baseIntegral := hInt
    U := U
    Q := Q
    integralU := hU
    integralQ := hQ
    i := i
    j := j
    s := s
    openI := hi
    openJ := hj
    surjectiveS := hsurjs
    comm := hcomm
    c := c
    m := m
    t := t
    x := x
    x_eq := rfl
    lifts := ht
    minor_ne := hdet
    V := V
    generic_mem := hV
    finite := hfin }⟩

/-- Every nonzero smooth cubic acquires, over its algebraic closure, a
selected actual configuration chart whose relative cubic--two-quadrics
intersection is finite near the generic point. -/
theorem nonempty_geometricSelectedActualFiniteNeighborhood_of_smooth
    {K : Type u} [Field K] [CharZero K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3) (hF0 : F ≠ 0)
    (cubic : Cubic K 4) (hcubic : cubic.toMvPolynomial = F)
    [Smooth (hypersurfaceToBase F hF)] :
    let L := AlgebraicClosure K
    let p := (cubic.map (algebraMap K L)).toMvPolynomial
    let hp := cubic_toMvPolynomial_isHomogeneous_three
      (cubic.map (algebraMap K L))
    Nonempty (SelectedActualFiniteNeighborhoodData p hp) := by
  dsimp only
  let L : Type u := AlgebraicClosure K
  let b : K →+* L := algebraMap K L
  let p : MvPolynomial (Fin 4) L := (cubic.map b).toMvPolynomial
  let hp : p.IsHomogeneous 3 :=
    cubic_toMvPolynomial_isHomogeneous_three (cubic.map b)
  have hpEq : F.map b = p := by
    dsimp only [p]
    rw [← hcubic, cubic_toMvPolynomial_map]
  have hp0 : p ≠ 0 := by
    rw [← hpEq]
    simpa only [map_zero] using
      (MvPolynomial.map_injective b (RingHom.injective b)).ne hF0
  letI : Smooth (hypersurfaceToBase p hp) := by
    letI : Smooth (hypersurfaceToBase (F.map b) (hF.map b)) :=
      smooth_hypersurfaceToBase_map b F hF
    exact smooth_hypersurfaceToBase_of_polynomial_eq
      (F.map b) p (hF.map b) hp hpEq
  obtain ⟨y, hzero, ell, hell, q, r, hq, hr, A, B, D, hy0, hsurj,
    hlin, hquad, hfinite, htripleEtale, hcoord, hAbase, hAB,
    hBbase, hD, hDEtale, hmember⟩ :=
    exists_geometric_orderedEight_with_proper_member_of_smooth
      F hF hF0 cubic hcubic
  exact nonempty_selectedActualFiniteNeighborhoodData_of_quadratic_pair
    p hp hp0 y hzero ell hell q r hq hr hlin hsurj hquad A B D
    hcoord hAbase hAB hDEtale hfinite

end PfaffianDescent
