import PfaffianDescent.CorayModelIncidenceExactRankCount
import PfaffianDescent.CorayActualMinimalPrimeSplitting

/-! Source only: genuine positivity of the SAME entire incidence ranks.
No stabilizer transitivity, supplied nonempty incidence or positive rank. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every actual minimal component over a finite coefficient extension
maps onto the SAME original relevant prime component. Actual contraction,
the actual homogeneous generic point and closedness of the finite map prove
surjectivity; no point/component transitivity is assumed. -/
theorem originalPrime_minimalCoefficientComponentToOriginal_surjective
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ I)
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes) :
    Function.Surjective (coefficientComponentToOriginal I D hDmin.le) := by
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  let f := coefficientComponentToOriginal I D hDmin.le
  letI : IsFinite f := (coefficientComponentToOriginal_finite_and_toBase I D hDmin.le).1
  have hDrel := homogeneousCoefficientExtension_minimalPrime_relevant I hIrel D hDmin
  let etaAmbient : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) M) :=
    ⟨D, hDmin.isPrime, hDrel⟩
  obtain ⟨eta, heta⟩ :=
    (quotientProjMap_mem_range_iff D etaAmbient).mpr (le_refl D.toIdeal)
  let j := quotientProjMap I
  let jRaw : scheme I → ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    fun x => j x
  have hjRaw : Topology.IsClosedEmbedding jRaw := j.isClosedEmbedding
  have hcomm : f ≫ j = quotientProjMap D ≫ ambientCoefficientMap (algebraMap K M) := by
    change (schemeQuotientMap IM D hDmin.le ≫
      projectiveCoefficientMap (algebraMap K M) I IM rfl) ≫ quotientProjMap I = _
    rw [Category.assoc, projectiveCoefficientMap_comp_quotientProjMap, ← Category.assoc,
      schemeQuotientMap_comp_quotientProjMap]
  have hpoint : jRaw (f eta) = ambientCoefficientMap (algebraMap K M) etaAmbient := by
    have h := congrArg (fun m => m eta) hcomm
    change jRaw (f eta) = ambientCoefficientMap (algebraMap K M) (quotientProjMap D eta) at h
    rw [heta] at h
    exact h
  have hcontract : (jRaw (f eta)).asHomogeneousIdeal.toIdeal = I.toIdeal := by
    rw [hpoint]
    change D.toIdeal.comap (MvPolynomial.map (algebraMap K M)) = I.toIdeal
    exact polynomialCoefficientExtension_minimalPrime_comap_eq I.toIdeal D.toIdeal hDmin
  have hcontractHomogeneous : (jRaw (f eta)).asHomogeneousIdeal = I :=
    HomogeneousIdeal.ext hcontract
  have hclosureAmbient : closure ({jRaw (f eta)} : Set (ProjectiveSpectrum
      (MvPolynomial.homogeneousSubmodule (Fin 4) K))) =
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 4) K) I.toIdeal := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton, hcontractHomogeneous]
    rfl
  have himageClosure : jRaw '' closure ({f eta} : Set (scheme I)) =
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 4) K) I.toIdeal := by
    rw [← hjRaw.closure_image_eq, Set.image_singleton]
    exact hclosureAmbient
  have himageUniv : jRaw '' (Set.univ : Set (scheme I)) =
      ProjectiveSpectrum.zeroLocus (MvPolynomial.homogeneousSubmodule (Fin 4) K) I.toIdeal := by
    rw [Set.image_univ]
    exact range_quotientProjMap I
  have hclosure : closure ({f eta} : Set (scheme I)) = Set.univ :=
    (Set.image_injective.mpr hjRaw.injective) (himageClosure.trans himageUniv.symm)
  have hsubset : closure ({f eta} : Set (scheme I)) ⊆ Set.range f :=
    closure_minimal (Set.singleton_subset_iff.mpr ⟨eta, rfl⟩) f.isClosedMap.isClosed_range
  rw [hclosure] at hsubset
  intro x
  exact hsubset (Set.mem_univ x)

/-- An actual nonempty finite scheme has positive native finite rank over
its actual base field. Its global sections are nontrivial by the native
scheme section instance, not by an assumed rank inequality. -/
theorem finiteSchemeRank_pos_of_nonempty
    {F : Type u} [Field F] {X : Scheme.{u}} [Nonempty X]
    (pi : X ⟶ Spec (.of F)) [IsFinite pi] : 0 < finiteSchemeRank pi := by
  letI : IsAffine X := isAffine_of_isAffineHom pi
  letI := finiteSchemeCoefficientAlgebra pi
  letI := finiteSchemeCoefficient_finite pi
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨Nonempty.some inferInstance, trivial⟩⟩
  letI : Nontrivial Γ(X, ⊤) := inferInstance
  change 0 < Module.finrank F Γ(X, ⊤)
  exact Module.finrank_pos

/-- The SAME literal entire incidence scheme on an actual minimal
coefficient component has positive ranks over BOTH M and kappa(P). The actual
component map is proved surjective, and the actual pullback constructs a
point; no nonempty cycle or desired rank bound is supplied. -/
theorem originalPrime_minimalCoefficientComponent_incidence_ranks_positive
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K)) [I.toIdeal.IsPrime]
    (hIrel : ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin 4) K) ≤ I)
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hDmin : D.toIdeal ∈
      (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes)
    (P : closedPoints (scheme I)) :
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hDmin.le
    let c := pullback.fst ep f
    let pi := pullback.snd ep f ≫ toBase D
    ∃ hfiniteM : IsFinite pi, ∃ hfiniteP : IsFinite c,
      letI := hfiniteM
      letI := hfiniteP
      0 < finiteSchemeRank pi ∧ 0 < finiteSchemeRank c ∧
        Module.finrank K M * finiteSchemeRank pi =
          (toBase I).residueDegree P.1 * finiteSchemeRank c := by
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hDmin.le
  let c := pullback.fst ep f
  let pi := pullback.snd ep f ≫ toBase D
  obtain ⟨Q, hQ⟩ := originalPrime_minimalCoefficientComponentToOriginal_surjective I hIrel D hDmin P.1
  obtain ⟨z, _hzP, _hzD⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := ep) (g := f) (IsLocalRing.closedPoint ((scheme I).residueField P.1)) Q
    ((Scheme.fromSpecResidueField_apply P.1 _).trans hQ.symm)
  letI : Nonempty ↥(pullback ep f : Scheme.{u}) := ⟨z⟩
  obtain ⟨hfiniteM, hfiniteP, hcount⟩ :=
    originalPointModelIncidence_exact_model_residue_rank_count I D hDmin.le P
  letI : IsFinite pi := hfiniteM
  letI : IsFinite c := hfiniteP
  exact ⟨hfiniteM, hfiniteP, finiteSchemeRank_pos_of_nonempty pi,
    finiteSchemeRank_pos_of_nonempty c, hcount⟩

/-- SAME actual original minimal component I, geometric minimal prime G and
original point P internally construct the literal model/cycle with positive
nu and s and exact r*nu=d*s. Minimality over I_M, contraction and incidence
nonemptiness are proved, not supplied as construction hypotheses. -/
theorem originalMinimalGeometricComponent_exists_jointModel_entire_incidence_positive_rank_count
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
      let c := pullback.fst ep f
      let pi := a ≫ toBase D
      ∃ hclosed : IsClosedImmersion a, ∃ hfinite : IsFinite pi, ∃ hfiniteP : IsFinite c,
        letI := hclosed
        letI := hfinite
        letI := hfiniteP
        let z := pushforwardClosedCycle a (finiteSchemeFundamentalCycle pi)
        D.toIdeal ∈ (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal.minimalPrimes ∧
          GeometricallyIntegral (toBase D) ∧
          Module.finrank K M = Nat.card (irreducibleComponents
            (scheme (I.map (componentPolynomialCoefficientMap (algebraMap K Ω))))) ∧
          0 < actualCurveCoordinateHilbertDegree D ∧
          Module.finrank K M * actualCurveCoordinateHilbertDegree D ≤ 3 * n ∧
          EffectiveZeroCycle.degree (toBase D) z = finiteSchemeRank pi ∧
          EffectiveZeroCycle.degree (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z =
            Module.finrank K M * finiteSchemeRank pi ∧
          Module.finrank K M * finiteSchemeRank pi =
            (toBase I).residueDegree P.1 * finiteSchemeRank c ∧
          0 < finiteSchemeRank pi ∧ 0 < finiteSchemeRank c ∧
          (∀ Q ∈ z.support, f Q.1 = P.1) := by
  letI : I.toIdeal.IsPrime := hI.isPrime
  have hIrel := selectedProjectiveMinimalComponent_homogeneous_relevant p q hp hp0 n hq hnot I hI
  obtain ⟨L, C, hCL, hCΩ, _hDprime, _hDL, hfield, hGI, _hall, _hDdegree, hpos, hbound⟩ :=
    originalMinimalGeometricComponent_exists_jointModel_positive_degree_bound
      p q hp hp0 n hn hq hnot I hI G hG
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  let IM := I.map (componentPolynomialCoefficientMap (algebraMap K M))
  letI : Module.Finite K M := inferInstance
  have hchain : IM.toIdeal.map (MvPolynomial.map (algebraMap M L)) =
      (I.map (componentPolynomialCoefficientMap (algebraMap K L))).toIdeal := by
    change (I.toIdeal.map (MvPolynomial.map (algebraMap K M))).map
      (MvPolynomial.map (algebraMap M L)) = I.toIdeal.map (MvPolynomial.map (algebraMap K L))
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro t
    change MvPolynomial.map (algebraMap M L) (MvPolynomial.map (algebraMap K M) t) =
      MvPolynomial.map (algebraMap K L) t
    rw [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq K M L]
  have hCminM : C.toIdeal ∈ (IM.toIdeal.map (MvPolynomial.map (algebraMap M L))).minimalPrimes := by
    rw [hchain]
    exact hCL
  have hDmin : D.toIdeal ∈ IM.toIdeal.minimalPrimes :=
    polynomialCoefficientExtension_minimalPrime_comap_mem IM.toIdeal C.toIdeal hCminM
  let hID := hDmin.le
  obtain ⟨hfiniteM, hfiniteP, hposM, hposP, hcount⟩ :=
    originalPrime_minimalCoefficientComponent_incidence_ranks_positive
      (K := K) (M := M) I hIrel D hDmin P
  obtain ⟨hclosed, _hfiniteM, hdegreeM, hdegreeK, hpoints⟩ :=
    originalPointModelIncidence_entireCycle_degrees_and_originalPoint (K := K) (M := M) I D hID P
  exact ⟨L, C, hCL, hCΩ, hID, hclosed, hfiniteM, hfiniteP,
    hDmin, hGI, hfield, hpos, hbound, hdegreeM, hdegreeK, hcount, hposM, hposP, hpoints⟩

end PfaffianDescent.Coray
