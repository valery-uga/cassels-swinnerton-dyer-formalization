import PfaffianDescent.CorayEntireModelIncidenceCycle

/-! Source only. Exact finite ranks on the SAME entire incidence scheme.
The residue-field rank s is not yet identified with a geometric count. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K M : Type u} [Field K] [Field M] [Algebra K M] [Module.Finite K M]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem nativeFiniteFieldSpectrum :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K M))) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
attribute [local instance] nativeFiniteFieldSpectrum

/-- The rank of ANY actual finite M-scheme over original K is multiplied
by the field degree. Intrinsic fundamental-cycle multiplicities are retained. -/
theorem finiteSchemeRank_original_eq_modelFieldDegree_mul
    {X : Scheme.{u}} (pi : X ⟶ Spec (.of M)) [IsFinite pi] :
    finiteSchemeRank (pi ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) =
      Module.finrank K M * finiteSchemeRank pi := by
  let b := Spec.map (CommRingCat.ofHom (algebraMap K M))
  calc
    finiteSchemeRank (pi ≫ b) =
        EffectiveZeroCycle.degree (pi ≫ b) (finiteSchemeFundamentalCycle (pi ≫ b)) :=
      (finiteSchemeFundamentalCycle_degree (pi ≫ b)).symm
    _ = EffectiveZeroCycle.degree (pi ≫ b) (finiteSchemeFundamentalCycle pi) := rfl
    _ = Module.finrank K M * EffectiveZeroCycle.degree pi (finiteSchemeFundamentalCycle pi) :=
      effectiveCycle_originalDegree_eq_modelFieldDegree_mul pi (finiteSchemeFundamentalCycle pi)
    _ = Module.finrank K M * finiteSchemeRank pi := by
      rw [finiteSchemeFundamentalCycle_degree]

/-- Equality of two actual finite structure maps preserves their rank.
Each side retains its own IsFinite witness; equality elimination also
transports the witness, avoiding an ill-typed dependent rewrite motive. -/
private theorem nativeFiniteSchemeRank_congr002
    {k : Type u} [Field k] {X : Scheme.{u}}
    {f g : X ⟶ Spec (.of k)} [IsFinite f] [IsFinite g] (h : f = g) :
    finiteSchemeRank f = finiteSchemeRank g := by
  cases h
  rfl

/-- On the SAME literal incidence pullback, r*nu=d*s holds for actual
finite scheme ranks: nu over M and s over kappa(P). No nonempty incidence,
reducedness, cardinality, transitivity, coprimality or small-count premise. -/
theorem originalPointModelIncidence_exact_model_residue_rank_count
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I)) :
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hID
    let a := pullback.snd ep f
    let c := pullback.fst ep f
    let pi := a ≫ toBase D
    ∃ hfiniteM : IsFinite pi, ∃ hfiniteP : IsFinite c,
      letI := hfiniteM
      letI := hfiniteP
      Module.finrank K M * finiteSchemeRank pi =
        (toBase I).residueDegree P.1 * finiteSchemeRank c := by
  let ep := (scheme I).fromSpecResidueField P.1
  let f := coefficientComponentToOriginal I D hID
  let a := pullback.snd ep f
  let c := pullback.fst ep f
  let pi := a ≫ toBase D
  let b := Spec.map (CommRingCat.ofHom (algebraMap K M))
  letI : Algebra K ((scheme I).residueField P.1) := pointAlgebra (toBase I) P.1
  letI : Module.Finite K ((scheme I).residueField P.1) := closedPoint_moduleFinite (toBase I) P
  let bp := Spec.map (CommRingCat.ofHom (algebraMap K ((scheme I).residueField P.1)))
  letI : IsFinite f := (coefficientComponentToOriginal_finite_and_toBase I D hID).1
  letI : IsFinite c := by dsimp only [c]; infer_instance
  obtain ⟨_hclosed, hfiniteM, _hrange⟩ := originalPointModelIncidence_finite_and_range I D hID P
  letI : IsFinite pi := hfiniteM
  have hbp : bp = ep ≫ toBase I := pointAlgebra_spec (toBase I) P.1
  have hcoeff : f ≫ toBase I = toBase D ≫ b :=
    (coefficientComponentToOriginal_finite_and_toBase I D hID).2
  have hbase : pi ≫ b = c ≫ bp := by
    calc
      pi ≫ b = a ≫ (toBase D ≫ b) := Category.assoc a (toBase D) b
      _ = a ≫ (f ≫ toBase I) :=
        congrArg (fun t : scheme D ⟶ Spec (.of K) => a ≫ t) hcoeff.symm
      _ = (a ≫ f) ≫ toBase I := (Category.assoc a f (toBase I)).symm
      _ = (c ≫ ep) ≫ toBase I :=
        congrArg (fun t : pullback ep f ⟶ scheme I => t ≫ toBase I)
          (pullback.condition (f := ep) (g := f)).symm
      _ = c ≫ (ep ≫ toBase I) := Category.assoc c ep (toBase I)
      _ = c ≫ bp :=
        congrArg (fun t : Spec ((scheme I).residueField P.1) ⟶ Spec (.of K) => c ≫ t)
          hbp.symm
  have hM : finiteSchemeRank (pi ≫ b) = Module.finrank K M * finiteSchemeRank pi :=
    finiteSchemeRank_original_eq_modelFieldDegree_mul pi
  have hResidueTower : finiteSchemeRank (c ≫ bp) =
      Module.finrank K ((scheme I).residueField P.1) * finiteSchemeRank c :=
    finiteSchemeRank_original_eq_modelFieldDegree_mul
      (K := K) (M := (scheme I).residueField P.1) c
  have hResidueDegree : Module.finrank K ((scheme I).residueField P.1) =
      (toBase I).residueDegree P.1 := closedPoint_finrank_eq_residueDegree (toBase I) P
  have hP : finiteSchemeRank (c ≫ bp) =
      (toBase I).residueDegree P.1 * finiteSchemeRank c :=
    hResidueTower.trans (congrArg (fun n : ℕ => n * finiteSchemeRank c) hResidueDegree)
  have hRanks : finiteSchemeRank (pi ≫ b) = finiteSchemeRank (c ≫ bp) :=
    nativeFiniteSchemeRank_congr002 hbase
  exact ⟨hfiniteM, inferInstance, hM.symm.trans (hRanks.trans hP)⟩

/-- Construct the SAME entire incidence cycle together with its exact
r*nu=d*s count. Its original degree is d*s; every support point still maps
to SAME original P. The actual residue-field rank s can be zero or exceed two. -/
theorem originalPointModelIncidence_entireCycle_exact_residue_rank_count
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) K))
    (D : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin 4) M))
    (hID : (I.map (componentPolynomialCoefficientMap (algebraMap K M))).toIdeal ≤ D.toIdeal)
    (P : closedPoints (scheme I)) :
    let ep := (scheme I).fromSpecResidueField P.1
    let f := coefficientComponentToOriginal I D hID
    let a := pullback.snd ep f
    let c := pullback.fst ep f
    let pi := a ≫ toBase D
    ∃ hclosed : IsClosedImmersion a, ∃ hfiniteM : IsFinite pi, ∃ hfiniteP : IsFinite c,
      letI := hclosed
      letI := hfiniteM
      letI := hfiniteP
      let z := pushforwardClosedCycle a (finiteSchemeFundamentalCycle pi)
      EffectiveZeroCycle.degree (toBase D) z = finiteSchemeRank pi ∧
        Module.finrank K M * finiteSchemeRank pi =
          (toBase I).residueDegree P.1 * finiteSchemeRank c ∧
        EffectiveZeroCycle.degree (toBase D ≫ Spec.map (CommRingCat.ofHom (algebraMap K M))) z =
          (toBase I).residueDegree P.1 * finiteSchemeRank c ∧
        (∀ Q ∈ z.support, f Q.1 = P.1) := by
  obtain ⟨hclosed, hfiniteM, hdegreeM, hdegreeK, hpoints⟩ :=
    originalPointModelIncidence_entireCycle_degrees_and_originalPoint I D hID P
  obtain ⟨_hfiniteM, hfiniteP, hcount⟩ :=
    originalPointModelIncidence_exact_model_residue_rank_count I D hID P
  exact ⟨hclosed, hfiniteM, hfiniteP, hdegreeM, hcount, hdegreeK.trans hcount, hpoints⟩

/-- The actual geometric minimal prime G and original K-point P construct
ONCE their SAME stabilizer model and literal entire incidence cycle. The
count r*nu=d*s is then proved on that same scheme, with s its native
kappa(P)-rank. No assumed count, cycle, nonempty incidence or GI. -/
theorem originalMinimalGeometricComponent_exists_jointModel_entire_incidence_exact_rank_count
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
          (∀ Q ∈ z.support, f Q.1 = P.1) := by
  obtain ⟨L, C, hCL, hCΩ, hID, hclosed, hfinite, hGI, hfield, hpos, hbound,
      hdegreeM, hdegreeK, hpoints⟩ :=
    originalMinimalGeometricComponent_exists_jointModel_entire_originalPoint_incidenceCycle
      p q hp hp0 n hn hq hnot I hI P G hG
  let M := homogeneousIdealStabilizerFixedField (K := K) C
  let D := C.comap (componentPolynomialCoefficientMap (algebraMap M L))
  letI : Module.Finite K M := inferInstance
  obtain ⟨_hfiniteM, hfiniteP, hcount⟩ :=
    originalPointModelIncidence_exact_model_residue_rank_count (K := K) (M := M) I D hID P
  exact ⟨L, C, hCL, hCΩ, hID, hclosed, hfinite, hfiniteP,
    hGI, hfield, hpos, hbound, hdegreeM, hdegreeK, hcount, hpoints⟩

end PfaffianDescent.Coray
