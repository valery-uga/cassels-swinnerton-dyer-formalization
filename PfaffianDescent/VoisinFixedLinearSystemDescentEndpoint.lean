import PfaffianDescent.VoisinFixedLinearSystemUniversalZeroSubschemeGluing
import PfaffianDescent.VoisinGlobalSectionsBaseChange

/-!
# Final endpoint for a descended fixed divisor class

This file combines the generic-avoidance theorem for a ground-field line
bundle with an actual projective section parameter and zero-locus lifts of
all marked generic points.  These are precisely the objects that the
remaining Picard/base-change argument must construct from a hypothetical
fixed divisor over the configuration function field.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-- A common field-valued section parameter and field-valued lifts of all
marked surface points into its zero scheme give literal bad-locus
membership.  This is the morphism-level direction needed after identifying
a divisor over the configuration function field with a member of a
ground-field complete linear system. -/
theorem mem_fixedLinearSystemBadLocus_of_common_fieldPoints
    {K L : Type u} [Field K] [Field L]
    {A Q T Z : Scheme.{u}} {n : ℕ}
    (qBase : Q ⟶ Spec (.of K)) (base : A ⟶ Spec (.of K))
    (tBase : T ⟶ Spec (.of K))
    (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (zeroFamily : Z ⟶ pullback base tBase)
    (r : Spec (.of L) ⟶ Q) (t : Spec (.of L) ⟶ T)
    (hbase : r ≫ qBase = t ≫ tBase)
    (lift : Fin n → (Spec (.of L) ⟶ Z))
    (hlift : ∀ i, lift i ≫ zeroFamily =
      pullback.lift r t hbase ≫
        fixedLinearSystemIncidenceMap qBase base tBase marked hmarked i) :
    r (IsLocalRing.closedPoint L) ∈
      fixedLinearSystemBadLocus qBase base tBase marked hmarked zeroFamily := by
  let z : properFiniteIncidenceParameterSpace qBase tBase :=
    pullback.lift r t hbase (IsLocalRing.closedPoint L)
  let y : Fin n → Z := fun i => lift i (IsLocalRing.closedPoint L)
  have hy : ∀ i, zeroFamily (y i) =
      fixedLinearSystemIncidenceMap qBase base tBase marked hmarked i z := by
    intro i
    exact congrArg (fun f => f (IsLocalRing.closedPoint L)) (hlift i)
  have hmem := mem_fixedLinearSystemBadLocus_of_parameter
    qBase base tBase marked hmarked zeroFamily z y
      hy
  have hz : pullback.fst qBase tBase z = r (IsLocalRing.closedPoint L) :=
    congrArg (fun f => f (IsLocalRing.closedPoint L))
      (pullback.lift_fst r t hbase)
  rw [hz] at hmem
  exact hmem

/-- Final descent endpoint expressed only through local coordinate
vanishing.  Once the generic point is known to avoid the fixed-linear-system
bad locus, local equations for a field-valued member through every marked
point produce the forbidden bad-locus member automatically. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_localCoordinates
    {K L : Type u} [Field K] [Field L]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (t : Spec (.of L) ⟶
      schemeModuleGlobalSectionsProjectiveParameters base M)
    (hrt : r ≫ qBase = t ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    (hlocal : ∀ i : Fin n,
      ∃ (ij : (C.projectiveSectionOpenCover base M).I₀)
        (ri : Spec (.of L) ⟶
          (C.projectiveSectionOpenCover base M).X ij),
        ri ≫ (C.projectiveSectionOpenCover base M).f ij =
          pullback.lift r t hrt ≫
            fixedLinearSystemIncidenceMap qBase base
              (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
              marked hmarked i ∧
        ∀ a : I,
          fieldPointΓevaluation ri
            (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
              (C.projectiveSectionLocalFreeIso base M ij)
              (C.projectiveSectionLocalUniversalSection base M ij) a) = 0) :
    False := by
  obtain ⟨lift, hlift⟩ :=
    C.exists_projectiveSectionLocalZeroGlued_lifts_of_local_coordinates_eq_zero
      base M qBase n marked hmarked r t hrt hlocal
  have hmem := mem_fixedLinearSystemBadLocus_of_common_fieldPoints
    qBase base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    marked hmarked
    (C.projectiveSectionLocalZeroGluedToAmbient base M)
    r t hrt lift hlift
  rw [hr] at hmem
  exact havoid hmem

/-- Final descent endpoint for a nonzero scalar-extended ground section.
Its coordinate vector determines the common projective parameter.  If that
same vector annihilates the evaluated ground basis at every marked point,
the normalized universal section vanishes locally there, contradicting
generic avoidance. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_scalarExtensionCoordinates
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (c : Fin (Module.finrank K
      (SchemeModuleGlobalSectionsOver base M)) → L)
    (hc : c ≠ 0)
    (hweighted : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
          r ≫ marked i →
      ∀ a : I,
        ∑ k, c k *
          fieldPointΓevaluation ri
            (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
              (C.projectiveSectionLocalFreeIso base M ij)
              (BundleSectionZeroLocus.pullbackSection
                (C.projectiveSectionOpenCoverToSurface base M ij) M
                (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                  (C.projectiveSectionOpenCoverToSurface base M ij))
                (schemeModuleGlobalSectionsOverEquivSections base M
                  (Module.finBasis K
                    (SchemeModuleGlobalSectionsOver base M) k))) a) = 0) :
    False := by
  obtain ⟨j, b, t, hcj, hbBase, hbt, hcoordinate, htBase⟩ :=
    exists_finiteDimensionalProjectiveParameter_normalized_of_ne_zero c hc
  have hrt : r ≫ qBase = t ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M :=
    hrBase.trans htBase.symm
  apply C.no_generic_projectiveSection_fieldMember_of_localCoordinates
    base M qBase n marked hmarked havoid r hr t hrt
  intro i
  let ai : Spec (.of L) ⟶ A := r ≫ marked i
  let tj : Spec (.of L) ⟶ finiteDimensionalProjectiveChart K
      (SchemeModuleGlobalSectionsOver base M) j :=
    Spec.map (CommRingCat.ofHom b)
  have htjBase : tj ≫ finiteDimensionalProjectiveChartToBase K
      (SchemeModuleGlobalSectionsOver base M) j =
      Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
    exact finiteDimensionalProjectiveChart_specMap_toBase j b
      (algebraMap K L) hbBase
  have haiBase : ai ≫ base = tj ≫
      finiteDimensionalProjectiveChartToBase K
        (SchemeModuleGlobalSectionsOver base M) j := by
    calc
      ai ≫ base = r ≫ qBase := by
        simp only [ai, Category.assoc, hmarked i]
      _ = Spec.map (CommRingCat.ofHom (algebraMap K L)) := hrBase
      _ = tj ≫ finiteDimensionalProjectiveChartToBase K
          (SchemeModuleGlobalSectionsOver base M) j := htjBase.symm
  obtain ⟨ij, ri, hij, hriSurface, hriParameter⟩ :=
    C.exists_projectiveSectionOpenCover_fieldPoint_lift
      base M j ai tj haiBase
  change (C.projectiveSectionOpenCover base M).I₀ at ij
  subst j
  have hb : (Spec.preimage
      (ri ≫ C.projectiveSectionOpenCoverToParameterChart base M ij)).hom = b :=
    C.projectiveSectionOpenCoverToParameterChart_preimage_eq
      base M ij ri b hriParameter
  have hzero :=
    C.projectiveSectionLocalUniversalSectionCoordinate_fieldPoint_eq_zero_of_weightedSum
      base M ij ri b hb c hcoordinate
        (hweighted i ij ri (by simpa only [ai] using hriSurface))
  refine ⟨ij, ri, ?_, hzero⟩
  apply pullback.hom_ext
  · calc
      (ri ≫ (C.projectiveSectionOpenCover base M).f ij) ≫
          pullback.fst base
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
        ri ≫ C.projectiveSectionOpenCoverToSurface base M ij := by
          simpa only [Category.assoc] using congrArg (fun f => ri ≫ f)
            (C.projectiveSectionOpenCover_f_comp_ambientFst base M ij)
      _ = r ≫ marked i := by simpa only [ai] using hriSurface
      _ = (pullback.lift r t hrt ≫
          fixedLinearSystemIncidenceMap qBase base
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
            marked hmarked i) ≫
          pullback.fst base
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) := by
          rw [Category.assoc, fixedLinearSystemIncidenceMap_fst]
          rw [← Category.assoc, pullback.lift_fst]
  · calc
      (ri ≫ (C.projectiveSectionOpenCover base M).f ij) ≫
          pullback.snd base
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) =
        ri ≫ C.projectiveSectionOpenCoverToParameterChart base M ij ≫
          finiteDimensionalProjectiveChartι K
            (SchemeModuleGlobalSectionsOver base M) ij.2 := by
          simpa only [Category.assoc] using congrArg (fun f => ri ≫ f)
            (C.projectiveSectionOpenCover_f_comp_ambientSnd base M ij)
      _ = t := hriParameter.trans hbt
      _ = (pullback.lift r t hrt ≫
          fixedLinearSystemIncidenceMap qBase base
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
            marked hmarked i) ≫
          pullback.snd base
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) := by
          rw [Category.assoc, fixedLinearSystemIncidenceMap_snd]
          rw [pullback.lift_snd]

/-- Base-change-equivalence form of the scalar-extension endpoint.  A
nonzero geometric section is transported back to the scalar extension of
the ground global-section space; its coordinates are then consumed by the
preceding theorem.  The sole remaining local hypothesis is the weighted
evaluation equation supplied by naturality of geometric evaluation. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_baseChangeEquiv
    {K L W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup W] [Module L W]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (e : (L ⊗[K] SchemeModuleGlobalSectionsOver base M) ≃ₗ[L] W)
    (s : W) (hs : s ≠ 0)
    (hweighted : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
          r ≫ marked i →
      ∀ a : I,
        ∑ k,
          finiteDimensionalScalarExtensionCoordinates K L
              (SchemeModuleGlobalSectionsOver base M) (e.symm s) k *
            fieldPointΓevaluation ri
              (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
                (C.projectiveSectionLocalFreeIso base M ij)
                (BundleSectionZeroLocus.pullbackSection
                  (C.projectiveSectionOpenCoverToSurface base M ij) M
                  (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                    (C.projectiveSectionOpenCoverToSurface base M ij))
                  (schemeModuleGlobalSectionsOverEquivSections base M
                    (Module.finBasis K
                      (SchemeModuleGlobalSectionsOver base M) k))) a) = 0) :
    False := by
  let v : L ⊗[K] SchemeModuleGlobalSectionsOver base M := e.symm s
  have hv : v ≠ 0 := by
    exact e.symm.map_ne_zero_iff.mpr hs
  let c := finiteDimensionalScalarExtensionCoordinates K L
    (SchemeModuleGlobalSectionsOver base M) v
  have hc : c ≠ 0 :=
    finiteDimensionalScalarExtensionCoordinates_ne_zero v hv
  exact C.no_generic_projectiveSection_fieldMember_of_scalarExtensionCoordinates
    base M qBase n marked hmarked havoid r hr hrBase c hc
      (by simpa only [c, v] using hweighted)

/-- Evaluation-natural form of the final scalar-extension endpoint.  For
each marked point and each local free coordinate, geometric evaluation of
the base-changed module agrees with scalar extension of the corresponding
ground evaluation functional.  Vanishing of the geometric divisor section
then supplies the weighted equations automatically. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_baseChangeEvaluation
    {K L W : Type u} [Field K] [Field L] [Algebra K L]
    [AddCommGroup W] [Module L W]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (e : (L ⊗[K] SchemeModuleGlobalSectionsOver base M) ≃ₗ[L] W)
    (s : W) (hs : s ≠ 0)
    (hlocalEvaluation : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
          r ≫ marked i →
      ∀ a : I,
        ∃ geometricEvaluation : W →ₗ[L] L,
          geometricEvaluation.comp e.toLinearMap =
              LinearMap.liftBaseChange L
                (C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap
                  base M ij ri a) ∧
            geometricEvaluation s = 0) :
    False := by
  apply C.no_generic_projectiveSection_fieldMember_of_baseChangeEquiv
    base M qBase n marked hmarked havoid r hr hrBase e s hs
  intro i ij ri hri a
  obtain ⟨geometricEvaluation, hcompat, hzero⟩ :=
    hlocalEvaluation i ij ri hri a
  have hsum :=
    sum_scalarExtensionCoordinates_eq_zero_of_baseChangeEquiv_evaluation_eq_zero
      e
      (C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap
        base M ij ri a)
      geometricEvaluation hcompat s hzero
  simpa only [
    projectiveSectionLocalBasisCoordinateEvaluationLinearMap_finBasis] using hsum

/-- Pullback-module specialization of the evaluation-natural endpoint.  The
base-change equivalence is no longer arbitrary: it is the literal map obtained
by pulling back the chosen finite basis of ground global sections.  Thus the
remaining geometric proof only has to establish bijectivity of this map and
compatibility of its local evaluations. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_pullbackBaseChangeEvaluation
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A AL Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (baseL : AL ⟶ Spec (.of L)) (f : AL ⟶ A)
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hbaseChange : Function.Bijective
      (schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
        base baseL f M))
    (s : SchemeModuleGlobalSectionsOver baseL
      ((Scheme.Modules.pullback f).obj M))
    (hs : s ≠ 0)
    (hlocalEvaluation : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
          r ≫ marked i →
      ∀ a : I,
        ∃ geometricEvaluation :
            SchemeModuleGlobalSectionsOver baseL
              ((Scheme.Modules.pullback f).obj M) →ₗ[L] L,
          geometricEvaluation.comp
              (schemeModuleGlobalSectionsBaseChangeLinearEquivOfFinBasis
                base baseL f M hbaseChange).toLinearMap =
            LinearMap.liftBaseChange L
              (C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap
                base M ij ri a) ∧
          geometricEvaluation s = 0) :
    False := by
  exact C.no_generic_projectiveSection_fieldMember_of_baseChangeEvaluation
    base M qBase n marked hmarked havoid r hr hrBase
      (schemeModuleGlobalSectionsBaseChangeLinearEquivOfFinBasis
        base baseL f M hbaseChange)
      s hs hlocalEvaluation

/-- Finite-basis form of the pullback base-change endpoint.  Instead of a
linear-map identity on the entire scalar extension, it asks only that
geometric evaluation of each literal pulled-back ground basis section equal
the corresponding ground local evaluation.  Finite-basis extensionality
supplies the full compatibility used by the preceding theorem. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_pullbackBasisEvaluation
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    {A AL Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    (baseL : AL ⟶ Spec (.of L)) (f : AL ⟶ A)
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (havoid : Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField) ∉
      fixedLinearSystemBadLocus qBase base
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
        marked hmarked
        (C.projectiveSectionLocalZeroGluedToAmbient base M))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (hrBase : r ≫ qBase =
      Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hbaseChange : Function.Bijective
      (schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis
        base baseL f M))
    (s : SchemeModuleGlobalSectionsOver baseL
      ((Scheme.Modules.pullback f).obj M))
    (hs : s ≠ 0)
    (hlocalBasisEvaluation : ∀ (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (ri : Spec (.of L) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      ri ≫ C.projectiveSectionOpenCoverToSurface base M ij =
          r ≫ marked i →
      ∀ a : I,
        ∃ geometricEvaluation :
            SchemeModuleGlobalSectionsOver baseL
              ((Scheme.Modules.pullback f).obj M) →ₗ[L] L,
          (∀ k : Fin (Module.finrank K
              (SchemeModuleGlobalSectionsOver base M)),
            geometricEvaluation
                ((schemeModuleGlobalSectionsOverEquivSections baseL
                  ((Scheme.Modules.pullback f).obj M)).symm
                    (BundleSectionZeroLocus.pullbackSection f M
                      (BundleSectionZeroLocus.isIso_pullbackUnitComparison f)
                      (schemeModuleGlobalSectionsOverEquivSections base M
                        (Module.finBasis K
                          (SchemeModuleGlobalSectionsOver base M) k)))) =
              C.projectiveSectionLocalBasisCoordinateEvaluationLinearMap
                base M ij ri a
                  (Module.finBasis K
                    (SchemeModuleGlobalSectionsOver base M) k)) ∧
          geometricEvaluation s = 0) :
    False := by
  apply C.no_generic_projectiveSection_fieldMember_of_pullbackBaseChangeEvaluation
    base M baseL f qBase n marked hmarked havoid r hr hrBase
      hbaseChange s hs
  intro i ij ri hri a
  obtain ⟨geometricEvaluation, hbasis, hzero⟩ :=
    hlocalBasisEvaluation i ij ri hri a
  refine ⟨geometricEvaluation, ?_, hzero⟩
  apply baseChangeEquiv_evaluation_comp_eq_liftBaseChange_of_finBasis
  intro k
  rw [schemeModuleGlobalSectionsBaseChangeLinearEquivOfFinBasis_apply,
    schemeModuleGlobalSectionsBaseChangeLinearMapOfFinBasis_one_tmul_finBasis]
  exact hbasis k

/-- A projective member of a descended ground-field section system cannot
contain every marked point of the generic configuration when its global
section space has dimension at most the number of points.  The hypotheses
retain the literal common projective parameter and literal lifts into the
globally glued universal zero scheme, so no incidence membership is assumed
as an opaque premise. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_member_of_localEvaluation
    {K P : Type u} [Field K] [Infinite P]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K
      (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → Q)
    (hlocalEvaluation : ∀ (e : Fin n ↪ P)
      (z : properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M))
      (g : K →+*
        (properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)
      (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (r : Spec (.of ((properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      r ≫ C.projectiveSectionOpenCoverToSurface base M ij =
        (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
          pullback.fst qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫ marked i →
      ∃ a : I, ∀ k,
        fieldPointΓevaluation r
            (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
              (C.projectiveSectionLocalFreeIso base M ij)
              (BundleSectionZeroLocus.pullbackSection
                (C.projectiveSectionOpenCoverToSurface base M ij) M
                (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                  (C.projectiveSectionOpenCoverToSurface base M ij))
                (schemeModuleGlobalSectionsOverEquivSections base M
                  (Module.finBasis K
                    (SchemeModuleGlobalSectionsOver base M) k))) a) =
          g (evaluation
            (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
            (e i)))
    (z : properFiniteIncidenceParameterSpace qBase
      (schemeModuleGlobalSectionsProjectiveParametersToBase base M))
    (hz : pullback.fst qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M) z =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (lift : Fin n → C.projectiveSectionLocalZeroGluedScheme base M)
    (hlift : ∀ i,
      C.projectiveSectionLocalZeroGluedToAmbient base M (lift i) =
        fixedLinearSystemIncidenceMap qBase base
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
          marked hmarked i z) : False := by
  have havoid :=
    C.genericFunctionField_avoids_projectiveSectionLocalZeroGlued_of_localEvaluation
      base M qBase n marked hmarked evaluation hevaluation hrank
        configuration hlocalEvaluation
  have hmem := mem_fixedLinearSystemBadLocus_of_parameter
    qBase base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    marked hmarked
    (C.projectiveSectionLocalZeroGluedToAmbient base M) z lift hlift
  rw [hz] at hmem
  exact havoid hmem

/-- Morphism-level form of the final descent endpoint.  A field-valued
member of the ground projective section system whose zero scheme contains
all marked points cannot lie above the generic configuration.  Local
trivializations may rescale point evaluations by a nonzero scalar, as they
naturally do for a line bundle.  This is the form directly consumed by a
future line-bundle base-change identification of the hypothetical fixed
divisor. -/
theorem SchemeModuleFiniteFreeAffineCover.no_generic_projectiveSection_fieldMember_of_localEvaluation_upToUnit
    {K P L : Type u} [Field K] [Infinite P] [Field L]
    {A Q : Scheme.{u}} [IsIntegral Q]
    (base : A ⟶ Spec (.of K)) [IsSeparated base] (M : A.Modules)
    [FiniteDimensional K (SchemeModuleGlobalSectionsOver base M)]
    {I : Type u} [Fintype I] [DecidableEq I]
    (C : SchemeModuleFiniteFreeAffineCover M I)
    (qBase : Q ⟶ Spec (.of K))
    (n : ℕ) (marked : Fin n → (Q ⟶ A))
    (hmarked : ∀ i, marked i ≫ base = qBase)
    (evaluation : SchemeModuleGlobalSectionsOver base M →ₗ[K] (P → K))
    (hevaluation : Function.Injective evaluation)
    (hrank : Module.finrank K
      (SchemeModuleGlobalSectionsOver base M) ≤ n)
    (configuration : (Fin n ↪ P) → Q)
    (hlocalEvaluation : ∀ (e : Fin n ↪ P)
      (z : properFiniteIncidenceParameterSpace qBase
        (schemeModuleGlobalSectionsProjectiveParametersToBase base M))
      (g : K →+*
        (properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)
      (i : Fin n)
      (ij : (C.projectiveSectionOpenCover base M).I₀)
      (r : Spec (.of ((properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z)) ⟶
        (C.projectiveSectionOpenCover base M).X ij),
      r ≫ C.projectiveSectionOpenCoverToSurface base M ij =
        (properFiniteIncidenceParameterSpace qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).fromSpecResidueField z ≫
          pullback.fst qBase
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M) ≫ marked i →
      ∃ (a : I)
        (lambda : (properFiniteIncidenceParameterSpace qBase
          (schemeModuleGlobalSectionsProjectiveParametersToBase base M)).residueField z),
        lambda ≠ 0 ∧ ∀ k,
          fieldPointΓevaluation r
              (BundleSectionZeroLocus.sectionCoordinateOfFreeIso I
                (C.projectiveSectionLocalFreeIso base M ij)
                (BundleSectionZeroLocus.pullbackSection
                  (C.projectiveSectionOpenCoverToSurface base M ij) M
                  (BundleSectionZeroLocus.isIso_pullbackUnitComparison
                    (C.projectiveSectionOpenCoverToSurface base M ij))
                  (schemeModuleGlobalSectionsOverEquivSections base M
                    (Module.finBasis K
                      (SchemeModuleGlobalSectionsOver base M) k))) a) =
            lambda * g (evaluation
              (Module.finBasis K (SchemeModuleGlobalSectionsOver base M) k)
              (e i)))
    (r : Spec (.of L) ⟶ Q)
    (hr : r (IsLocalRing.closedPoint L) =
      Q.fromSpecStalk (genericPoint Q)
        (IsLocalRing.closedPoint Q.functionField))
    (t : Spec (.of L) ⟶
      schemeModuleGlobalSectionsProjectiveParameters base M)
    (hrt : r ≫ qBase = t ≫
      schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    (lift : Fin n → (Spec (.of L) ⟶
      C.projectiveSectionLocalZeroGluedScheme base M))
    (hlift : ∀ i, lift i ≫
      C.projectiveSectionLocalZeroGluedToAmbient base M =
        pullback.lift r t hrt ≫
          fixedLinearSystemIncidenceMap qBase base
            (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
            marked hmarked i) : False := by
  have havoid :=
    C.genericFunctionField_avoids_projectiveSectionLocalZeroGlued_of_localEvaluation_upToUnit
      base M qBase n marked hmarked evaluation hevaluation hrank
        configuration hlocalEvaluation
  have hmem := mem_fixedLinearSystemBadLocus_of_common_fieldPoints
    qBase base
    (schemeModuleGlobalSectionsProjectiveParametersToBase base M)
    marked hmarked
    (C.projectiveSectionLocalZeroGluedToAmbient base M)
    r t hrt lift hlift
  rw [hr] at hmem
  exact havoid hmem

end PfaffianDescent
