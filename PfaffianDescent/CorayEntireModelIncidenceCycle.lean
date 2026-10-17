import PfaffianDescent.CorayComponentFiniteGaloisDefinition
import PfaffianDescent.HomogeneousQuotientMap
import AllCharacteristics.ProjectiveBaseChange
import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.ProperCyclePushforward
import PfaffianDescent.IntrinsicFiniteCycle
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PfaffianDescent.CorayJointSelectedComponentPositiveDegree

/-! Source-only: the ENTIRE actual original-point incidence scheme/cycle
on the SAME finite-field component model. No single-point orbit inference. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual finite field-spectrum structural map has its original
residue degree equal to the original-K field degree. -/
theorem modelFieldSpectrum_original_residueDegree_eq_finrank :
    (Spec.map (CommRingCat.ofHom (algebraMap K M))).residueDegree
      (IsLocalRing.closedPoint M) = Module.finrank K M := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap K M))
  letI : IsFinite b :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have h := finrank_Spec_field_eq_residueDegree b
  rw [Scheme.Hom.finrank_SpecMap_algebraMap] at h
  have hr := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := M))
    (IsLocalRing.closedPoint K)
  exact h.symm.trans hr

/-- EVERY actual M-cycle retains its full original-K degree, multiplying by
the actual finite field degree. The cycle is not replaced by one point. -/
theorem effectiveCycle_originalDegree_eq_modelFieldDegree_mul
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of M)) (z : EffectiveZeroCycle X) :
    EffectiveZeroCycle.degree (pi ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z =
      Module.finrank K M * EffectiveZeroCycle.degree pi z := by
  classical
  let b := Spec.map (CommRingCat.ofHom (algebraMap K M))
  have hresidue (x : X) : (pi ≫ b).residueDegree x =
      Module.finrank K M * pi.residueDegree x := by
    rw [residueDegree_comp]
    rw [show pi x = IsLocalRing.closedPoint M from Subsingleton.elim _ _]
    rw [modelFieldSpectrum_original_residueDegree_eq_finrank]
  change (∑ P ∈ z.support, z P * (pi ≫ b).residueDegree P.1) =
    Module.finrank K M * ∑ P ∈ z.support, z P * pi.residueDegree P.1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [hresidue]
  ring

/-- The literal coefficient-model component maps to the original scheme,
through the SAME coefficient extension and actual quotient immersion. -/
def coefficientComponentToOriginal
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal) :
    scheme D ⟶ scheme I :=
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  schemeQuotientMap IM D hID ≫ projectiveCoefficientMap (algebraMap K M) I IM rfl

/-- Actual finite field change and the actual closed model immersion derive
finiteness and the original structural-map square. No finite-map certificate,
geometric integrality or field-stabilizer transitivity is supplied. -/
theorem coefficientComponentToOriginal_finite_and_toBase
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal) :
    IsFinite (coefficientComponentToOriginal I D hID) ∧
      coefficientComponentToOriginal I D hID ≫ toBase I =
        toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  let b := Spec.map (CommRingCat.ofHom (algebraMap K M))
  let g := projectiveCoefficientMap (algebraMap K M) I IM rfl
  let j := schemeQuotientMap IM D hID
  letI : IsFinite b :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  letI : IsFinite g := MorphismProperty.of_isPullback (P := @IsFinite.{u})
    (isPullback_projectiveCoefficientMap (algebraMap K M) I IM rfl).flip inferInstance
  letI : IsClosedImmersion j := schemeQuotientMap_closedImmersion IM D hID
  refine ⟨by change IsFinite (j ≫ g); infer_instance, ?_⟩
  change (j ≫ g) ≫ toBase I = toBase D ≫ b
  rw [Category.assoc, projectiveCoefficientMap_toBase, ← Category.assoc,
    schemeQuotientMap_toBase]

/-- The whole actual point/component incidence scheme, with all its native
scheme structure; this is not a chosen orbit or a chosen closed-point summand. -/
def originalPointModelIncidenceScheme
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I)) : Scheme.{u} :=
  pullback ((scheme I).fromSpecResidueField P.1) (coefficientComponentToOriginal I D hID)

/-- The ENTIRE literal original-point/component pullback is finite over M,
and its actual range is EXACTLY the points of SAME D mapping to SAME P.
No nonempty-incidence, finite-cycle, GI or orbit certificate is assumed. -/
theorem originalPointModelIncidence_finite_and_range
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I)) :
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hID
    let a := pullback.snd ep f
    IsClosedImmersion a ∧ IsFinite (a ≫ toBase D) ∧
      Set.range a = f ⁻¹' ({P.1} : Set (scheme I)) := by
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let a := pullback.snd ep f
  let c := pullback.fst ep f
  let b := Spec.map (CommRingCat.ofHom (algebraMap K M))
  letI : IsClosedImmersion ep := isClosed_singleton_iff_isClosedImmersion.mp P.2
  letI : IsClosedImmersion a := inferInstance
  letI : IsFinite f := (coefficientComponentToOriginal_finite_and_toBase I D hID).1
  letI : IsFinite (ep ≫ toBase I) := isFinite_closedPointToBase (toBase I) P
  letI : IsFinite (c ≫ (ep ≫ toBase I)) := inferInstance
  have hbase : (a ≫ toBase D) ≫ b = c ≫ (ep ≫ toBase I) := by
    rw [Category.assoc, ← (coefficientComponentToOriginal_finite_and_toBase I D hID).2,
      ← Category.assoc, ← pullback.condition, Category.assoc]
  letI : IsFinite ((a ≫ toBase D) ≫ b) := hbase.symm ▸ inferInstance
  have hfinite : IsFinite (a ≫ toBase D) := IsFinite.of_comp (a ≫ toBase D) b
  refine ⟨inferInstance, hfinite, ?_⟩
  have hrange : Set.range ep = ({P.1} : Set (scheme I)) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Set.mem_singleton_iff.mpr (Scheme.fromSpecResidueField_apply P.1 y)
    · intro hx
      refine ⟨IsLocalRing.closedPoint ((scheme I).residueField P.1), ?_⟩
      exact (Scheme.fromSpecResidueField_apply P.1 _).trans (Set.mem_singleton_iff.mp hx).symm
  change Set.range (pullback.snd ep f) = _
  rw [Scheme.Pullback.range_snd, hrange]

/-- Construct the ENTIRE actual M-incidence cycle as the closed pushforward
of its SAME pullback's fundamental cycle. Its original-K degree is r*nu,
where nu is the literal actual M-scheme rank, and every support point maps
to the SAME original P. No cycle, degree equality, GI or transitivity premise. -/
theorem originalPointModelIncidence_entireCycle_degrees_and_originalPoint
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I)) :
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hID
    let a := pullback.snd ep f
    let pi := a ≫ toBase D
    ∃ hclosed : IsClosedImmersion a, ∃ hfinite : IsFinite pi,
      letI := hclosed
      letI := hfinite
      let z := pushforwardClosedCycle a (finiteSchemeFundamentalCycle pi)
      EffectiveZeroCycle.degree (toBase D) z = finiteSchemeRank pi ∧
        EffectiveZeroCycle.degree (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z =
          Module.finrank K M * finiteSchemeRank pi ∧
        (∀ Q ∈ z.support, f Q.1 = P.1) := by
  classical
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let a := pullback.snd ep f
  let pi := a ≫ toBase D
  obtain ⟨hclosed, hfinite, hrange⟩ := originalPointModelIncidence_finite_and_range I D hID P
  letI : IsClosedImmersion a := hclosed
  letI : IsFinite pi := hfinite
  let zS := finiteSchemeFundamentalCycle pi
  let z := pushforwardClosedCycle a zS
  have hdegree : EffectiveZeroCycle.degree (toBase D) z = finiteSchemeRank pi := by
    rw [degree_pushforwardClosedCycle]
    exact finiteSchemeFundamentalCycle_degree pi
  have hground : EffectiveZeroCycle.degree
      (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z =
        Module.finrank K M * finiteSchemeRank pi := by
    rw [effectiveCycle_originalDegree_eq_modelFieldDegree_mul, hdegree]
  refine ⟨hclosed, hfinite, hdegree, hground, ?_⟩
  intro Q hQ
  have himage : Q ∈ zS.support.image (closedPointMap a) := Finsupp.mapDomain_support hQ
  obtain ⟨R, _hR, hRQ⟩ := Finset.mem_image.mp himage
  have hpoints : a R.1 = Q.1 := congrArg Subtype.val hRQ
  have hmember : Q.1 ∈ Set.range a := ⟨R.1, hpoints⟩
  rw [hrange] at hmember
  exact Set.mem_singleton_iff.mp hmember

/-- ORIGINAL selected minimal component, original K-point and actual
geometric branch construct ONCE their SAME stabilizer model and ENTIRE
M-incidence cycle. GI, field degree r and own r*mu bound come from the actual
joint-model producer. No GI/model/cycle/point-degree or orbit-transitivity
certificate is supplied. This does not yet prove r*nu=d or2d. -/
theorem originalMinimalGeometricComponent_exists_jointModel_entire_originalPoint_incidenceCycle
    {Ω : Type u} [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 1 ≤ n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hI : I.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I))
    (G : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) Ω))
    (hG : G.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))).toIdeal.minimalPrimes) :
    ∃ (L : FiniteGaloisIntermediateField K Ω)
      (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) L)),
      C.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal.minimalPrimes ∧
      C.toIdeal.map (MvPolynomial.map (algebraMap L Ω)) = G.toIdeal ∧
      let M := homogeneousIdealStabilizerFixedField (K := K) C
      let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
      ∃ hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal,
      let ep := (scheme I).fromSpecResidueField P.1
      let f := coefficientComponentToOriginal I D hID
      let a := pullback.snd ep f
      let pi := a ≫ toBase D
      ∃ hclosed : IsClosedImmersion a, ∃ hfinite : IsFinite pi,
        letI := hclosed
        letI := hfinite
        let z := pushforwardClosedCycle a (finiteSchemeFundamentalCycle pi)
        GeometricallyIntegral (toBase D) ∧
          Module.finrank K M = Nat.card (irreducibleComponents
            (scheme (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) ∧
          0 < actualCurveCoordinateHilbertDegree D ∧
          Module.finrank K M * actualCurveCoordinateHilbertDegree D ≤ 3 * n ∧
          EffectiveZeroCycle.degree (toBase D) z = finiteSchemeRank pi ∧
          EffectiveZeroCycle.degree (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z =
            Module.finrank K M * finiteSchemeRank pi ∧
          (∀ Q ∈ z.support, f Q.1 = P.1) := by
  obtain ⟨L, C, hCL, hCΩ, _hDprime, _hDL, hfield, hGI, _hall, _hDdegree, hpos, hbound⟩ :=
    originalMinimalGeometricComponent_exists_jointModel_positive_degree_bound
      p q hp hp0 n hn hq hnot I hI G hG
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  letI : Module.Finite K M := inferInstance
  have hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal := by
    change I.toIdeal.map (MvPolynomial.map (algebraMap K M)) ≤
      C.toIdeal.comap (MvPolynomial.map (algebraMap M L))
    apply Ideal.map_le_iff_le_comap.mpr
    intro t ht
    change MvPolynomial.map (algebraMap M L) (MvPolynomial.map (algebraMap K M) t) ∈ C.toIdeal
    have hcomp : (algebraMap M L).comp (algebraMap K M) = algebraMap K L :=
      (IsScalarTower.algebraMap_eq K M L).symm
    rw [MvPolynomial.map_map, hcomp]
    exact hCL.le (Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap K L)) ht)
  obtain ⟨hclosed, hfinite, hdegreeM, hdegreeK, hpoints⟩ :=
    originalPointModelIncidence_entireCycle_degrees_and_originalPoint (K := K) (M := M) I D hID P
  exact ⟨L, C, hCL, hCΩ, hID, hclosed, hfinite,
    hGI, hfield, hpos, hbound, hdegreeM, hdegreeK, hpoints⟩

end PfaffianDescent.Coray
