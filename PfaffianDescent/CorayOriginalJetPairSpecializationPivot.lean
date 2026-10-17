import PfaffianDescent.CorayOriginalJetPairSpecialization

/-! Strengthened ORIGINAL principal-open producer retains its own native
pivot nonvanishing. Existing accepted old3 module is imported unchanged. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- Multiplying by the internally selected nonzero gradient clears the
native pivot direction with its original coordinate indices. -/
private theorem pivotSpecialization_nativeRow_weighted_sum001
    {F : Type u} [Field F] (j : Fin 4) (a : Fin 3 → F) (pivot : Fin 3)
    (D : Fin 4 → F) (r : Fin 2) :
    (∑ i, D i * PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j a pivot i r) =
      D (j.succAbove (pivot.succAbove r)) -
        (D (j.succAbove pivot) * a (pivot.succAbove r)) / a pivot := by
  classical
  rw [Fin.sum_univ_succAbove _ j]
  simp only [PfaffianDescent.cubicClosedPointSerreSurfaceJets_row_diag,
    Pi.zero_apply, mul_zero, zero_add]
  simp only [PfaffianDescent.cubicClosedPointSerreSurfaceJets_row,
    Fin.insertNth_apply_succAbove]
  rw [Fin.sum_univ_succAbove _ pivot]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  simp [Pi.single_apply, mul_div_assoc, sub_eq_add_neg, mul_neg, neg_div, add_comm]

private theorem pivotSpecialization_nativeRow_clear_zero_iff001
    {F : Type u} [Field F] (j : Fin 4) (a : Fin 3 → F) (pivot : Fin 3)
    (ha : a pivot ≠ 0) (D : Fin 4 → F) (r : Fin 2) :
    (∑ i, D i * PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j a pivot i r) = 0 ↔
      a pivot * D (j.succAbove (pivot.succAbove r)) -
        a (pivot.succAbove r) * D (j.succAbove pivot) = 0 := by
  rw [pivotSpecialization_nativeRow_weighted_sum001, sub_eq_zero, eq_div_iff ha,
    sub_eq_zero]
  constructor <;> intro h <;> simpa only [mul_comm] using h

private theorem pivotSpecialization_polynomialJet_fst001
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (z : Fin 4 → F) (v : Fin 2 → Fin 4 → F) (q : MvPolynomial (Fin 4) K) :
    (q.eval₂ (algebraMap K (SurfacePlaneJet F)) (surfacePlaneJetCoordinates z v)).fst =
      q.eval₂ (algebraMap K F) z := by
  have h := congrArg TrivSqZeroExt.fst
    (surfacePlaneJet_projects_to_directionalJet z v (0 : Fin 2) q)
  simpa only [TrivSqZeroExt.fst_map, homogeneousDirectionalJet_fst,
    MvPolynomial.aeval_def] using h

private theorem pivotSpecialization_weightedPolynomialJet_zero_iff001
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (j : Fin 4) (a : Fin 3 → F) (pivot : Fin 3) (ha : a pivot ≠ 0)
    (z : Fin 4 → F) {m : ℕ} (c : Fin m → F)
    (q : Fin m → MvPolynomial (Fin 4) K) :
    let v : Fin 2 → Fin 4 → F := fun r i =>
      PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j a pivot i r
    (∑ k, c k • (q k).eval₂ (algebraMap K (SurfacePlaneJet F))
      (surfacePlaneJetCoordinates z v)) = 0 ↔
      (∑ k, c k * (q k).eval₂ (algebraMap K F) z) = 0 ∧
      ∀ r : Fin 2,
        a pivot * (∑ k, c k * (pderiv (j.succAbove (pivot.succAbove r)) (q k)).eval₂
          (algebraMap K F) z) -
        a (pivot.succAbove r) * (∑ k, c k * (pderiv (j.succAbove pivot) (q k)).eval₂
          (algebraMap K F) z) = 0 := by
  classical
  let v : Fin 2 → Fin 4 → F := fun r i =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j a pivot i r
  let w : SurfacePlaneJet F := ∑ k, c k • (q k).eval₂
    (algebraMap K (SurfacePlaneJet F)) (surfacePlaneJetCoordinates z v)
  let D : Fin 4 → F := fun i => ∑ k, c k * (pderiv i (q k)).eval₂ (algebraMap K F) z
  have hValue : w.fst = ∑ k, c k * (q k).eval₂ (algebraMap K F) z := by
    simp only [w, TrivSqZeroExt.fst_sum, TrivSqZeroExt.fst_smul,
      pivotSpecialization_polynomialJet_fst001, smul_eq_mul]
  have hDirection (r : Fin 2) : w.snd r =
      ∑ i, D i * PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j a pivot i r := by
    simp only [w, TrivSqZeroExt.snd_sum, TrivSqZeroExt.snd_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [surfacePlaneJet_tangent_value_eq_directional_derivative]
    simp only [D, v]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  change w = 0 ↔ _
  constructor
  · intro hw
    constructor
    · rw [← hValue, hw, TrivSqZeroExt.fst_zero]
    · intro r
      apply (pivotSpecialization_nativeRow_clear_zero_iff001 j a pivot ha D r).mp
      rw [← hDirection, hw, TrivSqZeroExt.snd_zero, Pi.zero_apply]
  · rintro ⟨hValueZero, hDirectionZero⟩
    apply TrivSqZeroExt.ext
    · rw [TrivSqZeroExt.fst_zero, hValue]
      exact hValueZero
    · funext r
      rw [TrivSqZeroExt.snd_zero, Pi.zero_apply, hDirection]
      exact (pivotSpecialization_nativeRow_clear_zero_iff001 j a pivot ha D r).mpr
        (hDirectionZero r)

private theorem pivotSpecialization_polynomialEvaluation_map001
    {K R F : Type u} [Field K] [CommRing R] [CommRing F]
    [Algebra K R] [Algebra K F] (g : R →ₐ[K] F) (x : Fin 4 → R)
    (q : MvPolynomial (Fin 4) K) :
    g (q.eval₂ (algebraMap K R) x) =
      q.eval₂ (algebraMap K F) (fun i => g (x i)) := by
  have h := MvPolynomial.hom_eval₂ q (algebraMap K R) g.toRingHom x
  have hCoeff : g.toRingHom.comp (algebraMap K R) = algebraMap K F :=
    RingHom.ext g.commutes
  rw [hCoeff] at h
  exact h

private theorem pivotSpecialization_genericJet_originalRing_identities001
    {K R F : Type u} [Field K] [CommRing R] [Field F]
    [Algebra K R] [Algebra K F] (g : R →ₐ[K] F) (hg : Function.Injective g)
    (x : Fin 4 → R) (j : Fin 4) (a : Fin 3 → R) (pivot : Fin 3)
    (ha : g (a pivot) ≠ 0) {m : ℕ} (A : Fin m → R)
    (q : Fin m → MvPolynomial (Fin 4) K)
    (hJet :
      (∑ k, g (A k) • (q k).eval₂ (algebraMap K (SurfacePlaneJet F))
        (surfacePlaneJetCoordinates (fun i => g (x i))
          (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            (fun t => g (a t)) pivot i r))) = 0) :
    (∑ k, A k * (q k).eval₂ (algebraMap K R) x) = 0 ∧
      ∀ r : Fin 2,
        a pivot * (∑ k, A k * (pderiv (j.succAbove (pivot.succAbove r)) (q k)).eval₂
          (algebraMap K R) x) -
        a (pivot.succAbove r) * (∑ k, A k * (pderiv (j.succAbove pivot) (q k)).eval₂
          (algebraMap K R) x) = 0 := by
  have hValues := (pivotSpecialization_weightedPolynomialJet_zero_iff001 j
    (fun t => g (a t)) pivot ha (fun i => g (x i)) (fun k => g (A k)) q).mp hJet
  constructor
  · apply hg
    rw [map_sum, map_zero]
    simp only [map_mul, pivotSpecialization_polynomialEvaluation_map001]
    exact hValues.1
  · intro r
    apply hg
    rw [map_sub, map_mul, map_mul, map_sum, map_sum, map_zero]
    simp only [map_mul, pivotSpecialization_polynomialEvaluation_map001]
    exact hValues.2 r

private theorem pivotSpecialization_originalRing_identities_fieldPoint001
    {K R M : Type u} [Field K] [CommRing R] [Field M]
    [Algebra K R] [Algebra K M] (h : R →ₐ[K] M)
    (x : Fin 4 → R) (j : Fin 4) (a : Fin 3 → R) (pivot : Fin 3)
    (ha : h (a pivot) ≠ 0) {m : ℕ} (A : Fin m → R)
    (q : Fin m → MvPolynomial (Fin 4) K)
    (hValue : (∑ k, A k * (q k).eval₂ (algebraMap K R) x) = 0)
    (hDirections : ∀ r : Fin 2,
      a pivot * (∑ k, A k * (pderiv (j.succAbove (pivot.succAbove r)) (q k)).eval₂
        (algebraMap K R) x) -
      a (pivot.succAbove r) * (∑ k, A k * (pderiv (j.succAbove pivot) (q k)).eval₂
        (algebraMap K R) x) = 0) :
    (∑ k, h (A k) • (q k).eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates (fun i => h (x i))
        (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
          (fun t => h (a t)) pivot i r))) = 0 := by
  apply (pivotSpecialization_weightedPolynomialJet_zero_iff001 j
    (fun t => h (a t)) pivot ha (fun i => h (x i)) (fun k => h (A k)) q).mpr
  constructor
  · have hv := congrArg h hValue
    simpa only [map_sum, map_mul, map_zero,
      pivotSpecialization_polynomialEvaluation_map001] using hv
  · intro r
    have hd := congrArg h (hDirections r)
    simpa only [map_sub, map_sum, map_mul, map_zero,
      pivotSpecialization_polynomialEvaluation_map001] using hd

private theorem pivotSpecialization_jetAnnihilator_tangentSpan001
    {M : Type u} [Field M] {m : ℕ} (c : Fin m → M) (w : Fin m → SurfacePlaneJet M)
    (hJet : (∑ i, c i • w i) = 0) :
    ∀ B : Fin m → M, B ∈ nativeSurfaceJetCoordinateSpan w →
      (∑ i, c i * B i) = 0 := by
  classical
  let phi : (Fin m → M) →ₗ[M] M := Fintype.linearCombination M c
  have hResidue : phi (fun i => (w i).fst) = 0 := by
    have h := congrArg TrivSqZeroExt.fst hJet
    simpa only [phi, Fintype.linearCombination_apply, TrivSqZeroExt.fst_sum,
      TrivSqZeroExt.fst_smul, TrivSqZeroExt.fst_zero, smul_eq_mul, mul_comm] using h
  have hDirection (r : Fin 2) : phi (fun i => (w i).snd r) = 0 := by
    have h := congrArg (fun t : SurfacePlaneJet M => t.snd r) hJet
    simpa only [phi, Fintype.linearCombination_apply, TrivSqZeroExt.snd_sum,
      TrivSqZeroExt.snd_smul, TrivSqZeroExt.snd_zero, Finset.sum_apply,
      Pi.smul_apply, Pi.zero_apply, smul_eq_mul, mul_comm] using h
  have hSpan : nativeSurfaceJetCoordinateSpan w ≤ LinearMap.ker phi := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    induction r using Fin.cases with
    | zero => exact hResidue
    | succ r => exact hDirection r
  intro B hB
  have h := hSpan hB
  change phi B = 0 at h
  simpa only [phi, Fintype.linearCombination_apply, smul_eq_mul, mul_comm] using h

/-! Strengthened construction: retains the internally proved ORIGINAL pivot
nonvanishing globally and at EVERY point of the actually constructed open.
The preceding three accepted declarations/headers/proofs are unchanged. -/
/-- Natural ORIGINAL data produces the same nonzero pair equation and a
nonempty original principal open on which its first-point coefficient
hyperplane is nonzero and annihilates the actual native full surface jet. -/
theorem cubicThroughPointBasis_exists_originalPairEquation_nativeJet_principalOpen_withPivot001
    {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (hsize : finrank K L + 5 ≤ (n + 3).choose 3 - n.choose 3) :
    let I := equationIdeal p hp
    let R := ChartRing I j
    letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
    letI : Algebra K R := cubicChartNativeAlgebra p hp j
    letI : Module K R := Algebra.toModule
    let x := chartCoordinate I j
    let e := cubicThroughPointChartEvaluation p hp n y hpy j
    let a : Fin 3 → R := fun t => (pderiv (j.succAbove t) p).eval₂ (algebraMap K R) x
    ∃ (pivot : Fin 3) (d : R) (A : Fin m → R)
      (q : Fin m → MvPolynomial (Fin 4) K) (P : MvPolynomial (Fin 4 ⊕ Fin 4) K) (k : Fin m),
      (∀ i, (q i).IsHomogeneous n ∧ (q i).eval₂ (algebraMap K L) y = 0 ∧
        Ideal.Quotient.mk I.toIdeal (q i) = (b i).1.1 ∧
        (q i).eval₂ (algebraMap K R) x = e (b i)) ∧
      P.eval₂ (algebraMap K (R ⊗[K] R))
        (Sum.elim (fun i => x i ⊗ₜ[K] (1 : R)) (fun i => (1 : R) ⊗ₜ[K] x i)) =
          ∑ i, A i ⊗ₜ[K] e (b i) ∧
      P.eval₂ (algebraMap K (R ⊗[K] R))
        (Sum.elim (fun i => x i ⊗ₜ[K] (1 : R)) (fun i => (1 : R) ⊗ₜ[K] x i)) ≠ 0 ∧
      (∑ i, A i * (q i).eval₂ (algebraMap K R) x) = 0 ∧
      (∀ r : Fin 2,
        a pivot * (∑ i, A i * (pderiv (j.succAbove (pivot.succAbove r)) (q i)).eval₂
          (algebraMap K R) x) -
        a (pivot.succAbove r) * (∑ i, A i * (pderiv (j.succAbove pivot) (q i)).eval₂
          (algebraMap K R) x) = 0) ∧
      a pivot ≠ 0 ∧
      let u := d * a pivot * A k
      u ≠ 0 ∧ Nonempty {s : PrimeSpectrum R // s ∈ PrimeSpectrum.basicOpen u} ∧
      ∀ (M : Type u) [Field M] [Algebra K M] (h : R →ₐ[K] M), h u ≠ 0 →
        h (a pivot) ≠ 0 ∧ (fun i => h (A i)) ≠ 0 ∧
        (∑ i, h (A i) • (q i).eval₂ (algebraMap K (SurfacePlaneJet M))
          (surfacePlaneJetCoordinates (fun i => h (x i))
            (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
              (fun t => h (a t)) pivot i r))) = 0 ∧
        ∀ B : Fin m → M,
          B ∈ nativeSurfaceJetCoordinateSpan (fun i => (q i).eval₂
            (algebraMap K (SurfacePlaneJet M))
            (surfacePlaneJetCoordinates (fun i => h (x i))
              (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
                (fun t => h (a t)) pivot i r))) →
          (∑ i, h (A i) * B i) = 0 := by
  classical
  let I := equationIdeal p hp
  let R := ChartRing I j
  letI : CommRing R := inferInstanceAs (CommRing (ChartRing (equationIdeal p hp) j))
  letI : Algebra K R := cubicChartNativeAlgebra p hp j
  letI : Module K R := Algebra.toModule
  let F := (hypersurface p hp).functionField
  letI : Field F := inferInstanceAs (Field ((hypersurface p hp).functionField))
  letI : Algebra K F := (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let g : R →+* F := @affineChartGenericEvaluation
    R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
  have hg : Function.Injective g := @affineChartGenericEvaluation_injective
    R (inferInstance : CommRing R)
    (hypersurface p hp) (inferInstance : IsIntegral (hypersurface p hp))
    (chartι I j) (isOpenImmersion_chartι I j)
    (inferInstanceAs (Nonempty (chartι (equationIdeal p hp) j).opensRange))
  have hBase : g.comp (chartBaseMap I j) = algebraMap K F :=
    cubicChartGenericEvaluation_coefficient_eq p hp j
  let gAlg : R →ₐ[K] F := { toRingHom := g, commutes' := fun c => RingHom.congr_fun hBase c }
  have hgeq (r : R) : gAlg r = g r := rfl
  let x := chartCoordinate I j
  let e := cubicThroughPointChartEvaluation p hp n y hpy j
  let a : Fin 3 → R := fun t => (pderiv (j.succAbove t) p).eval₂ (algebraMap K R) x
  let z : Fin 4 → F := fun i => g (x i)
  obtain ⟨pivot, hpivot, hpJ, hAnchor, d, A, P, hd, hJet, hP, hQ⟩ :=
    cubicThroughPointBasis_genericNativeJet_exists_literalPairPolynomial_nonzeroPivot001
      p hp hp0 n y hpy j b hsize
  let v : Fin 2 → Fin 4 → F := fun r i =>
    PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
      (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) pivot i r
  let gJ := cubicNormalizedFullJetChartMap p hp j z v hpJ hAnchor
  choose q hHom hThrough hRepresentative using fun i =>
    (cubicThroughCoordinateSections_mem_iff p hp n y hpy (b i).1).mp (b i).2
  have hOriginalSection (i : Fin m) : (q i).eval₂ (algebraMap K R) x = e (b i) := by
    change (q i).eval₂ (chartBaseMap I j) (chartCoordinate I j) = e (b i)
    rw [eval₂_chartCoordinate_eq_fraction I j (q i) (hHom i)]
    let sq : grading I n := ⟨Ideal.Quotient.mk I.toIdeal (q i),
      polynomial_class_mem_grading I (q i) (hHom i)⟩
    have hs : sq = (b i).1 := Subtype.ext (hRepresentative i)
    have hFraction := congrArg
      (gradedChartSectionEvaluation (grading I) (coordinate_mem I j) n) hs
    exact hFraction
  have hSection (i : Fin m) : gJ (e (b i)) =
      (q i).eval₂ (algebraMap K (SurfacePlaneJet F)) (surfacePlaneJetCoordinates z v) := by
    rw [cubicNormalizedFullJetChartMap_section001]
    change cubicCoordinateAlgebraEvaluation p hp (surfacePlaneJetCoordinates z v) hpJ (b i).1.1 = _
    rw [← hRepresentative i]
    exact cubicCoordinateAlgebraEvaluation_mk p hp _ hpJ (q i)
  have hGrad :
      (fun t => aeval z (pderiv (j.succAbove t) (p.map (algebraMap K F)))) =
        (fun t => gAlg (a t)) := by
    funext t
    have he := pivotSpecialization_polynomialEvaluation_map001 gAlg x (pderiv (j.succAbove t) p)
    simpa only [a, z, hgeq, MvPolynomial.pderiv_map, aeval_eq_eval,
      MvPolynomial.eval_map] using he.symm
  have ha : gAlg (a pivot) ≠ 0 := by
    have he := pivotSpecialization_polynomialEvaluation_map001 gAlg x (pderiv (j.succAbove pivot) p)
    change gAlg ((pderiv (j.succAbove pivot) p).eval₂ (algebraMap K R) x) ≠ 0
    rw [he]
    exact hpivot
  have hPolynomialJet :
      (∑ i, gAlg (A i) • (q i).eval₂ (algebraMap K (SurfacePlaneJet F))
        (surfacePlaneJetCoordinates (fun i => gAlg (x i))
          (fun r i => PfaffianDescent.cubicClosedPointSerreSurfaceJets_row j
            (fun t => gAlg (a t)) pivot i r))) = 0 := by
    have hSectionSum : (∑ i, g (A i) • gJ (e (b i))) =
        ∑ i, g (A i) • (q i).eval₂ (algebraMap K (SurfacePlaneJet F))
          (surfacePlaneJetCoordinates z v) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hSection i]
    rw [hSectionSum] at hJet
    simpa only [v, hGrad, z, hgeq] using hJet
  obtain ⟨hValue, hDirections⟩ := pivotSpecialization_genericJet_originalRing_identities001
    gAlg hg x j a pivot ha A q hPolynomialJet
  have hgAlg : Function.Injective gAlg := hg
  have hPivotRing : a pivot ≠ 0 := by
    intro hzero
    exact ha (by rw [hzero, map_zero])
  have hSome : ∃ k, gAlg (A k) ≠ 0 := by
    by_contra! hAll
    have hAzero (i : Fin m) : A i = 0 := hgAlg (by simpa only [map_zero] using hAll i)
    apply hQ
    rw [hP]
    simp only [hAzero, TensorProduct.zero_tmul, Finset.sum_const_zero]
  obtain ⟨k, hk⟩ := hSome
  let u := d * a pivot * A k
  have hgu : gAlg u ≠ 0 := by
    simp only [u, map_mul]
    exact mul_ne_zero (mul_ne_zero hd ha) hk
  have hu : u ≠ 0 := by
    intro hzero
    exact hgu (by rw [hzero, map_zero])
  have hOpen : Nonempty {s : PrimeSpectrum R // s ∈ PrimeSpectrum.basicOpen u} := by
    refine ⟨⟨⟨RingHom.ker g, RingHom.ker_isPrime g⟩, ?_⟩⟩
    change g u ≠ 0
    exact hgu
  refine ⟨pivot, d, A, q, P, k, ?_, hP, hQ, hValue, hDirections, hPivotRing, hu, hOpen, ?_⟩
  · intro i
    exact ⟨hHom i, hThrough i, hRepresentative i, hOriginalSection i⟩
  · intro M _ _ h hNonzero
    change h (d * a pivot * A k) ≠ 0 at hNonzero
    have haM : h (a pivot) ≠ 0 := by
      intro hzero
      apply hNonzero
      simp only [u, map_mul, hzero, mul_zero, zero_mul]
    have hkM : h (A k) ≠ 0 := by
      intro hzero
      apply hNonzero
      simp only [u, map_mul, hzero, mul_zero]
    refine ⟨haM, ?_⟩
    constructor
    · intro hzero
      exact hkM (congrFun hzero k)
    · have hJetM := pivotSpecialization_originalRing_identities_fieldPoint001
        h x j a pivot haM A q hValue hDirections
      exact ⟨hJetM, pivotSpecialization_jetAnnihilator_tangentSpan001
        (fun i => h (A i)) _ hJetM⟩

end PfaffianDescent.Coray
