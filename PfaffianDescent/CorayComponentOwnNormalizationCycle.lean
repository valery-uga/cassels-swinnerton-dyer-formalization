import PfaffianDescent.CorayOwnProjectiveComponentNormalizationQuotientFinite
import PfaffianDescent.CorayOutsideActualNormalizationSupportRegular
import PfaffianDescent.CorayRelevantPrimeComponentHyperplaneDegree
import PfaffianDescent.CorayActualComponentHyperplaneCartierDegree
import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift
import PfaffianDescent.CoraySelectedComponentHeightAndRelevance
import PfaffianDescent.CorayOwnMinimalComponentDegreePositiveAnyField
import AllCharacteristics.CycleDegreeAssembly

/-! Source-only actual OWN component normalization cycle construction.
The same selected component and original K are retained. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem selectedComponentIntegral
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    IsIntegral (scheme C) := by
  have hCrel := selectedProjectiveMinimalComponent_homogeneous_relevant p q hp hp0 n hq hnot C hCmin
  exact homogeneousPrime_projectiveScheme_isIntegral C hCmin.isPrime
    (homogeneousPrimeQuotientProjectivePoint C hCmin.isPrime hCrel)

/-- On the ACTUAL selected component, points outside its OWN actual
normalization quotient support are regular. Component integrality and native
curve dimension are constructed from actual minimality and original p/q. -/
theorem selectedMinimalComponent_stalk_regular_of_outside_ownNormalizationQuotientSupport
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (x : scheme C) :
    letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
    x ∉ schemeModuleStalkSupport (genericNormalizationQuotientSheaf (scheme C)) →
      IsRegularLocalRing ((scheme C).presheaf.stalk x) := by
  classical
  letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
  let X := scheme C
  let R := X.presheaf.stalk x
  let F := X.functionField
  let Q := genericNormalizationQuotientSheaf X
  change x ∉ schemeModuleStalkSupport Q → IsRegularLocalRing R
  intro houtside
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (toBase C)
  have hdim : ringKrullDim R ≤ 1 :=
    selectedProjectiveComponent_original_stalk_ringKrullDim_le_one p q hp hp0 n hq hnot C hCmin.le x
  letI : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr hdim
  letI : Ring.DimensionLEOne R :=
    ⟨fun {J} hJzero hJprime => hJprime.isMaximal_of_ne_bot hJzero⟩
  by_contra hsing
  letI : Nontrivial (localNormalizationDefect R F) :=
    localNormalizationDefect_nontrivial_of_not_isRegularLocalRing R F hsing
  have hx : x ∈ ⨆ U : X.affineOpens, (U : X.Opens) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨U, hxU⟩ := Opens.mem_iSup.mp hx
  let E := genericNormalizationQuotientSheaf_affineNativeStalkDefectEquiv X U.1 U.2 ⟨x, hxU⟩
  have hnontrivial : Nontrivial (Q.presheaf.stalk x) := E.toEquiv.nontrivial_congr.mpr inferInstance
  exact houtside hnontrivial

/-- An ACTUAL regular point of the SAME selected component lifts to its
OWN canonical normalization preserving its actual residue map and full
original degree. The component's integral/finite/dimension facts are derived. -/
theorem selectedMinimalComponent_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    (P : closedPoints (scheme C)) (hregular : IsRegularLocalRing ((scheme C).presheaf.stalk P.1)) :
    letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ∃ Q : closedPoints N, nu Q.1 = P.1 ∧ IsIso (nu.residueFieldMap Q.1) ∧
      nu.residueDegree Q.1 = 1 ∧ (nu ≫ toBase C).residueDegree Q.1 = (toBase C).residueDegree P.1 := by
  letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase C)
  let f := X.fromSpecStalk (genericPoint X)
  have hdim : ringKrullDim (X.presheaf.stalk P.1) ≤ 1 :=
    selectedProjectiveComponent_original_stalk_ringKrullDim_le_one p q hp hp0 n hq hnot C hCmin.le P.1
  exact properMorph_regularClosedCurvePoint_exists_degree_preserving_closedPoint
    nu (toBase C) P hregular hdim f.toNormalization (Scheme.Hom.toNormalization_fromNormalization f)

/-- The SAME selected component regular-supported cycle has an actual
injective normalized support lift with exactly its original coefficients and
full original residue degrees. No replacement normalization cycle is assumed. -/
theorem selectedMinimalComponent_genericNormalization_regularSupportedCycle_exists_degree_preserving_lift
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
    let I := C
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ∀ z : EffectiveZeroCycle X,
      (∀ P ∈ z.support, IsRegularLocalRing (X.presheaf.stalk P.1)) →
      ∃ Q : z.support → closedPoints N,
        Function.Injective Q ∧
        (∀ P : z.support,
          nu (Q P).1 = P.1.1 ∧ IsIso (nu.residueFieldMap (Q P).1) ∧
          nu.residueDegree (Q P).1 = 1 ∧
          (nu ≫ toBase I).residueDegree (Q P).1 = (toBase I).residueDegree P.1.1) ∧
        EffectiveZeroCycle.degree (nu ≫ toBase I)
            (∑ P : z.support, z P.1 • Finsupp.single (Q P) 1) =
          EffectiveZeroCycle.degree (toBase I) z := by
  classical
  letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
  dsimp only
  let I := C
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  intro z hregular
  have hlift (P : z.support) : ∃ R : closedPoints N,
      nu R.1 = P.1.1 ∧ IsIso (nu.residueFieldMap R.1) ∧
      nu.residueDegree R.1 = 1 ∧
      (nu ≫ toBase I).residueDegree R.1 = (toBase I).residueDegree P.1.1 :=
    selectedMinimalComponent_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 n hq hnot C hCmin P.1 (hregular P.1 P.2)
  let Q : z.support → closedPoints N := fun P => Classical.choose (hlift P)
  have hmaps (P : z.support) := Classical.choose_spec (hlift P)
  have hQ : Function.Injective Q := by
    intro P R h
    apply Subtype.ext
    apply Subtype.ext
    exact (hmaps P).1.symm.trans
      ((congrArg (fun A : closedPoints N => nu A.1) h).trans (hmaps R).1)
  refine ⟨Q, hQ, hmaps, ?_⟩
  have hsingle (P : z.support) :
      EffectiveZeroCycle.degree (nu ≫ toBase I) (Finsupp.single (Q P) 1) =
        (toBase I).residueDegree P.1.1 := by
    unfold EffectiveZeroCycle.degree
    rw [Finsupp.sum_single_index (by simp)]
    simpa only [one_mul] using (hmaps P).2.2.2
  rw [← EffectiveZeroCycle.degreeLinearMap_apply, map_sum]
  simp only [map_smul, EffectiveZeroCycle.degreeLinearMap_apply, smul_eq_mul]
  calc
    _ = ∑ P : z.support, z P.1 * (toBase I).residueDegree P.1.1 := by
      apply Finset.sum_congr rfl
      intro P _
      exact congrArg (fun d : ℕ => z P.1 * d) (hsingle P)
    _ = EffectiveZeroCycle.degree (toBase I) z :=
      Finset.sum_coe_sort z.support (fun P => z P * (toBase I).residueDegree P.1)

/-- Construct an ACTUAL regular linear H avoiding the selected component's
OWN normalization quotient support. Its finite support and actual generic
ambient point are derived internally from the SAME C and original p/q. -/
theorem selectedMinimalComponent_exists_regular_linear_avoiding_ownNormalizationQuotientSupport
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
    ∃ (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1), H ∉ C.toIdeal ∧
      (∀ y : MvPolynomial (Fin 4) K,
        H * y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K)) →
          y ∈ Ideal.span ({p, q} : Set (MvPolynomial (Fin 4) K))) ∧
      (∀ x ∈ schemeModuleStalkSupport (genericNormalizationQuotientSheaf (scheme C)),
        Ideal.Quotient.mk C.toIdeal H ∉ x.asHomogeneousIdeal) := by
  classical
  letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  let I := projectiveIntersectionIdeal p q hp hq
  let XC := scheme C
  let QC := genericNormalizationQuotientSheaf XC
  let S := schemeModuleStalkSupport QC
  have hCrel := selectedProjectiveMinimalComponent_homogeneous_relevant p q hp hp0 n hq hnot C hCmin
  let c : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin 4) K) :=
    ⟨C, hCmin.isPrime, hCrel⟩
  obtain ⟨x, hx⟩ := (quotientProjMap_mem_range_iff I c).mpr hCmin.le
  let xC := homogeneousPrimeQuotientProjectivePoint C hCmin.isPrime hCrel
  have hfinite : S.Finite :=
    (selectedProjectivePrimeComponent_genericNormalizationQuotient_finite_sections_and_support
      p q hp hp0 n hq hnot C hCmin.le hCmin.isPrime xC).2
  letI : Fintype S := hfinite.fintype
  let i := schemeQuotientMap I C hCmin.le
  let point : PUnit.{1} ⊕ S → scheme I := fun a => match a with
    | Sum.inl _ => x
    | Sum.inr y => i y.1
  obtain ⟨H, hH, hregular, havoid⟩ :=
    regular_pair_exists_linear_nonzerodivisor_avoiding_finite_projective_family
      p q hp hq hp0 (isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot) point
  have hnotC : H ∉ C.toIdeal := by
    intro hmem
    apply havoid (Sum.inl PUnit.unit)
    have hraw : H ∈ (quotientProjMap I x).asHomogeneousIdeal := by
      rw [hx]
      exact hmem
    change Ideal.Quotient.mk I.toIdeal H ∈ x.asHomogeneousIdeal at hraw
    exact hraw
  refine ⟨H, hH, hnotC, hregular, ?_⟩
  intro y hy hmem
  apply havoid (Sum.inr ⟨y, hy⟩)
  have hraw : H ∈ (quotientProjMap C y).asHomogeneousIdeal := hmem
  have hpoint : quotientProjMap I (i y) = quotientProjMap C y :=
    congrArg (fun f => f y) (schemeQuotientMap_comp_quotientProjMap I C hCmin.le)
  rw [← hpoint] at hraw
  change Ideal.Quotient.mk I.toIdeal H ∈ (i y).asHomogeneousIdeal at hraw
  exact hraw

/-- The ACTUAL hyperplane cut of the SAME selected component produces an
OWN original-K cycle of its intrinsic degree, supported on its OWN regular
locus. Finite support avoidance, regularity, finite section and all actual
residue-weighted degree equalities are constructed, never supplied. -/
theorem selectedMinimalComponent_exists_regular_hyperplaneCycle_own_degree
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
    ∃ (H : MvPolynomial (Fin 4) K) (hH : H.IsHomogeneous 1), H ∉ C.toIdeal ∧
      ∃ z : EffectiveZeroCycle (scheme C),
        EffectiveZeroCycle.degree (toBase C) z = actualCurveCoordinateHilbertDegree C ∧
        (∀ P ∈ z.support, IsRegularLocalRing ((scheme C).presheaf.stalk P.1)) ∧
        actualCurveCoordinateHilbertDegree C ≤ 3 * n := by
  classical
  letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
  letI : C.toIdeal.IsPrime := hCmin.isPrime
  obtain ⟨H, hH, hnotC, hregular, havoid⟩ :=
    selectedMinimalComponent_exists_regular_linear_avoiding_ownNormalizationQuotientSupport
      p q hp hp0 n hq hnot C hCmin
  have hq0 : q ≠ 0 := by
    intro hz
    apply hnot
    rw [hz]
    exact Ideal.zero_mem _
  have hrel := isRelPrime_of_smooth_cubic_and_not_mem p q hp hp0 hnot
  let S := C ⊔ equationIdeal H hH
  let i := schemeQuotientMap C S le_sup_left
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion C S le_sup_left
  letI : IsFinite (toBase S) := selectedProjectiveComponent_regular_linearSection_isFinite
    p q H hp hq hH hp0 hq0 hrel hregular C hCmin.le
  obtain ⟨heq, _N, _hN⟩ := primeComponent_linearSection_degree_and_eventualIncrement C H hH hnotC
  obtain ⟨zS, hzS⟩ := exists_effectiveZeroCycle_degree_finiteSchemeRank (toBase S)
  let z := pushforwardClosedCycle i zS
  have hbase : i ≫ toBase C = toBase S := schemeQuotientMap_toBase C S le_sup_left
  have hdegree : EffectiveZeroCycle.degree (toBase C) z = actualCurveCoordinateHilbertDegree C := by
    change EffectiveZeroCycle.degree (toBase C) (pushforwardClosedCycle i zS) = _
    rw [degree_pushforwardClosedCycle, hbase, hzS]
    exact heq.symm
  have hbound : actualCurveCoordinateHilbertDegree C ≤ 3 * n :=
    (selectedProjectiveMinimalComponent_hilbertDegree_pos_bound_and_eventualIncrement_anyField
      p q hp hp0 n hq hnot C hCmin).2.1
  refine ⟨H, hH, hnotC, z, hdegree, ?_, hbound⟩
  intro P hP
  have himage : P ∈ zS.support.image (closedPointMap i) := Finsupp.mapDomain_support hP
  obtain ⟨R, _hR, hRP⟩ := Finset.mem_image.mp himage
  apply selectedMinimalComponent_stalk_regular_of_outside_ownNormalizationQuotientSupport
    p q hp hp0 n hq hnot C hCmin P.1
  intro hsupport
  apply havoid P.1 hsupport
  have hmem : Ideal.Quotient.mk C.toIdeal H ∈ (i R.1).asHomogeneousIdeal := by
    change gradedQuotientMap C S le_sup_left (Ideal.Quotient.mk C.toIdeal H) ∈ R.1.asHomogeneousIdeal
    change Ideal.Quotient.mk S.toIdeal H ∈ R.1.asHomogeneousIdeal
    have hHmem : H ∈ S.toIdeal := by
      apply (show (equationIdeal H hH).toIdeal ≤ S.toIdeal from le_sup_right)
      change H ∈ Ideal.span ({H} : Set (MvPolynomial (Fin 4) K))
      exact Ideal.subset_span (by simp)
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hHmem]
    exact R.1.asHomogeneousIdeal.toIdeal.zero_mem
  have hpoints : i R.1 = P.1 := congrArg Subtype.val hRP
  rw [hpoints] at hmem
  exact hmem

/-- Every ACTUAL selected minimal component has a constructed cycle on its
OWN canonical normalization, of exactly its OWN intrinsic Hilbert degree
and bounded by3n. The original K and every residue-degree factor are retained.
No GI, regularity, chosen H, supplied cycle or normalization degree premise.
When the actual component degree is3 this is a SAME-normalization cubic cycle. -/
theorem selectedMinimalComponent_genericNormalization_exists_own_degree_cycle
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
    let X := scheme C
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ∃ z : EffectiveZeroCycle N, EffectiveZeroCycle.degree (nu ≫ toBase C) z =
        actualCurveCoordinateHilbertDegree C ∧ actualCurveCoordinateHilbertDegree C ≤ 3 * n := by
  classical
  letI : IsIntegral (scheme C) := selectedComponentIntegral p q hp hp0 n hq hnot C hCmin
  let X := scheme C
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  obtain ⟨_H, _hH, _hnotC, zC, hzC, hregular, hbound⟩ :=
    selectedMinimalComponent_exists_regular_hyperplaneCycle_own_degree p q hp hp0 n hq hnot C hCmin
  obtain ⟨Q, _hQinj, _hQresidue, hdegree⟩ :=
    selectedMinimalComponent_genericNormalization_regularSupportedCycle_exists_degree_preserving_lift
      p q hp hp0 n hq hnot C hCmin zC hregular
  let zN : EffectiveZeroCycle N := ∑ P : zC.support, zC P.1 • Finsupp.single (Q P) 1
  exact ⟨zN, hdegree.trans hzC, hbound⟩

end PfaffianDescent.Coray
