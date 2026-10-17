import PfaffianDescent.CorayOriginalBasisTranscendentalRatio
import PfaffianDescent.CorayBoundedOriginalTangentIncidence
import PfaffianDescent.CubicFiniteSubschemeHyperplane
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! SOURCE ONLY. The actual evaluation kernel at the SAME auxiliary
closed point constructs two independent original through-P sections.
Their ratio is transcendental for the ORIGINAL function-field action. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

private theorem rankFive_rankThree_kernel_exists_independent_pair001
    {K V M : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup M] [Module K M] [Module.Finite K V] [Module.Finite K M]
    (e : V →ₗ[K] M) (hV : 5 ≤ finrank K V) (hM : finrank K M ≤ 3) :
    ∃ s : Fin 2 → V, LinearIndependent K s ∧ ∀ i, e (s i) = 0 := by
  have hNullity := e.finrank_range_add_finrank_ker
  have hRange : finrank K e.range ≤ finrank K M := e.range.finrank_le
  have hKer : 2 ≤ finrank K e.ker := by omega
  obtain ⟨sKer, hliKer⟩ := exists_linearIndependent_of_le_finrank hKer
  let s : Fin 2 → V := fun i => (sKer i).1
  have hli : LinearIndependent K s :=
    hliKer.map' e.ker.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  refine ⟨s, hli, ?_⟩
  intro i
  exact (sKer i).2

private theorem rankFive_rankThree_nativeMonoid_kernel_pair002
    {K V M : Type u} [Field K] [AddCommMonoid V] [Module K V]
    [AddCommMonoid M] [Module K M] [Module.Finite K V] [Module.Finite K M]
    (e : V →ₗ[K] M) (hV : 5 ≤ finrank K V) (hM : finrank K M ≤ 3) :
    ∃ s : Fin 2 → V, LinearIndependent K s ∧ ∀ i, e (s i) = 0 := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup M := Module.addCommMonoidToAddCommGroup K
  exact rankFive_rankThree_kernel_exists_independent_pair001
    (K := K) (V := V) (M := M) e hV hM

private theorem independent_pair_ratio_not_original_ground001
    {K F : Type u} [Field K] [Field F] [Algebra K F]
    (v : Fin 2 → F) (hli : LinearIndependent K v) :
    v 1 / v 0 ∉ (⊥ : IntermediateField K F) := by
  intro hmem
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  have hval : v 1 = algebraMap K F c * v 0 :=
    (div_eq_iff (hli.ne_zero 0)).mp hc.symm
  have hsmul : (1 : K) • v 1 = c • v 0 := by
    simpa only [one_smul, Algebra.smul_def, map_one, one_mul] using hval
  have hIndices : (1 : Fin 2) = 0 :=
    hli.eq_of_smul_apply_eq_smul_apply 1 c 1 0 one_ne_zero hsmul
  exact (by decide : (1 : Fin 2) ≠ 0) hIndices

private theorem linearIndependent_nativeEvaluation_scalarTransport002
    {K V B F : Type u} [Field K]
    [AddCommMonoid V] [Module K V] [AddCommMonoid B] [Module K B]
    [AddCommMonoid F] [Module K F]
    (e : V →ₗ[K] B) (he : Function.Injective e) (E : B ≃ₗ[K] F)
    (phi : V → F) (hphi : ∀ t : V, E (e t) = phi t)
    (s : Fin 2 → V) (hli : LinearIndependent K s) :
    LinearIndependent K (fun i => phi (s i)) := by
  let native : V →ₗ[K] F := E.toLinearMap.comp e
  have hNative : Function.Injective native := E.injective.comp he
  have hliNative : LinearIndependent K (native ∘ s) :=
    hli.map_injOn native hNative.injOn
  have hFamily : native ∘ s = (fun i => phi (s i)) :=
    funext (fun i => hphi (s i))
  exact hFamily ▸ hliNative

private theorem originalGenericEvaluation_independent_pair001
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    (s : Fin 2 → cubicThroughCoordinateSections p hp n y hpy)
    (hli : LinearIndependent K s) :
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    LinearIndependent K (fun i =>
      (show (hypersurface p hp).functionField from
        cubicThroughPointGenericLinearEvaluation p hp n y hpy j (s i))) := by
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  let V := cubicThroughCoordinateSections p hp n y hpy
  let B := SchemeFunctionFieldOver (hypersurfaceToBase p hp)
  let F := (hypersurface p hp).functionField
  let e : V →ₗ[K] B := cubicThroughPointGenericLinearEvaluation p hp n y hpy j
  have he : Function.Injective e :=
    cubicThroughPointGenericLinearEvaluation_injective p hp n y hpy j hp0
  let E : B ≃ₗ[K] F := schemeFunctionFieldOriginalRingLinearEquiv (hypersurfaceToBase p hp)
  let phi : V → F := fun t => (show F from e t)
  have hphi : ∀ t : V, E (e t) = phi t := fun _ => rfl
  exact linearIndependent_nativeEvaluation_scalarTransport002
    (K := K) (V := V) (B := B) (F := F) e he E phi hphi s hli

/-- On the actual ORIGINAL through-P quotient family of rank at least5,
evaluation into the auxiliary residue field of rank at most3 constructs
two independent sections vanishing at that auxiliary point. The original
smooth-cubic constant-field theorem makes their SAME generic ratio
transcendental. No supplied pencil, ratio, differential or image premise. -/
theorem cubicThroughPoint_rankFive_auxiliaryRankThree_exists_independent_transcendental_pencil001
    {K L M : Type u} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Module.Finite K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (z : Fin 4 → M) (hpz : p.eval₂ (algebraMap K M) z = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    (hW : 5 ≤ finrank K (cubicThroughCoordinateSections p hp n y hpy))
    (hM : finrank K M ≤ 3) :
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    ∃ s : Fin 2 → cubicThroughCoordinateSections p hp n y hpy,
      LinearIndependent K s ∧
      (∀ i, cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz (s i) = 0) ∧
      (∀ i, (show (hypersurface p hp).functionField from
        cubicThroughPointGenericLinearEvaluation p hp n y hpy j (s i)) ≠ 0) ∧
      Transcendental K
        ((show (hypersurface p hp).functionField from
          cubicThroughPointGenericLinearEvaluation p hp n y hpy j (s 1)) /
         (show (hypersurface p hp).functionField from
          cubicThroughPointGenericLinearEvaluation p hp n y hpy j (s 0))) := by
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI : Module.Finite K (grading (equationIdeal p hp) n) :=
    Module.Finite.iff_fg.mpr ((homogeneousSubmodule_fg (Fin 4) K n).map
      (Ideal.Quotient.mkₐ K (equationIdeal p hp).toIdeal).toLinearMap)
  let V := cubicThroughCoordinateSections p hp n y hpy
  let e : V →ₗ[K] M := cubicThroughPointAuxiliaryEvaluation p hp n y hpy z hpz
  obtain ⟨s, hli, hs⟩ := rankFive_rankThree_nativeMonoid_kernel_pair002
    (K := K) (V := V) (M := M) e hW hM
  let v : Fin 2 → (hypersurface p hp).functionField := fun i =>
    (show (hypersurface p hp).functionField from
      cubicThroughPointGenericLinearEvaluation p hp n y hpy j (s i))
  have hliNative : LinearIndependent K v :=
    originalGenericEvaluation_independent_pair001 p hp hp0 n y hpy j s hli
  refine ⟨s, hli, hs, (fun i => hliNative.ne_zero i), ?_⟩
  intro hAlg
  exact independent_pair_ratio_not_original_ground001 v hliNative
    (cubicOriginalFunctionField_isAlgebraic_mem_ground p hp hp0 j (v 1 / v 0) hAlg)

private theorem cubicChartRange_nonempty_of_fieldEvaluation001
    {K M : Type u} [Field K] [Field M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (j : Fin 4)
    (g : ChartRing (equationIdeal p hp) j →+* M) :
    Nonempty (chartι (equationIdeal p hp) j).opensRange := by
  let x := Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint M)
  exact ⟨⟨chartι (equationIdeal p hp) j x, ⟨x, rfl⟩⟩⟩

/-- Actual ORIGINAL closed P and auxiliary closed A retain their canonical
point algebras and literal recovered chart maps. A's degree3 and P's
original Hilbert window supply all rank hypotheses internally. The
auxiliary chart is ALSO the generic-evaluation chart of the output ratio.
No point replacement, chosen pencil, transcendence, or image hypothesis. -/
theorem originalClosedPoints_exists_independent_sameDegree_pencil_through_both_transcendental001
    {K : Type u} [Field K] [Infinite K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (n : ℕ) (P A : closedPoints (hypersurface p hp))
    (hAdegree : (hypersurfaceToBase p hp).residueDegree A.1 = 3)
    (hsize : (hypersurfaceToBase p hp).residueDegree P.1 + 5 ≤
      (n + 3).choose 3 - n.choose 3) (jP jA : Fin 4) :
    letI : IsIntegral (hypersurface p hp) :=
      PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
    letI : Algebra K (hypersurface p hp).functionField :=
      (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
    letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) A.1
    ∀ gP : ChartRing (equationIdeal p hp) jP →+* (hypersurface p hp).residueField P.1,
      gP.comp (chartBaseMap (equationIdeal p hp) jP) =
        algebraMap K ((hypersurface p hp).residueField P.1) →
      Spec.map (CommRingCat.ofHom gP) ≫ chartι (equationIdeal p hp) jP =
        (hypersurface p hp).fromSpecResidueField P.1 →
    ∀ gA : ChartRing (equationIdeal p hp) jA →+* (hypersurface p hp).residueField A.1,
      gA.comp (chartBaseMap (equationIdeal p hp) jA) =
        algebraMap K ((hypersurface p hp).residueField A.1) →
      Spec.map (CommRingCat.ofHom gA) ≫ chartι (equationIdeal p hp) jA =
        (hypersurface p hp).fromSpecResidueField A.1 →
    letI : Nonempty (chartι (equationIdeal p hp) jA).opensRange :=
      cubicChartRange_nonempty_of_fieldEvaluation001 p hp jA gA
    ∃ (hpy : p.eval₂ (algebraMap K ((hypersurface p hp).residueField P.1))
        (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) = 0)
      (hpz : p.eval₂ (algebraMap K ((hypersurface p hp).residueField A.1))
        (fun i => gA (chartCoordinate (equationIdeal p hp) jA i)) = 0),
    ∃ s : Fin 2 → cubicThroughCoordinateSections p hp n
        (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpy,
      LinearIndependent K s ∧
      (∀ i, cubicThroughPointAuxiliaryEvaluation p hp n
        (fun t => gP (chartCoordinate (equationIdeal p hp) jP t)) hpy
        (fun t => gA (chartCoordinate (equationIdeal p hp) jA t)) hpz (s i) = 0) ∧
      (∀ i, (show (hypersurface p hp).functionField from
        cubicThroughPointGenericLinearEvaluation p hp n
          (fun t => gP (chartCoordinate (equationIdeal p hp) jP t)) hpy jA (s i)) ≠ 0) ∧
      Transcendental K
        ((show (hypersurface p hp).functionField from
          cubicThroughPointGenericLinearEvaluation p hp n
            (fun t => gP (chartCoordinate (equationIdeal p hp) jP t)) hpy jA (s 1)) /
         (show (hypersurface p hp).functionField from
          cubicThroughPointGenericLinearEvaluation p hp n
            (fun t => gP (chartCoordinate (equationIdeal p hp) jP t)) hpy jA (s 0))) := by
  letI : IsIntegral (hypersurface p hp) :=
    PfaffianDescent.isIntegral_hypersurface_of_smooth_of_nonzero_of_infinite p hp hp0
  letI : Algebra K (hypersurface p hp).functionField :=
    (schemeFunctionFieldGroundRingHom (hypersurfaceToBase p hp)).toAlgebra
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) P.1
  letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) A.1
  dsimp only
  intro gP hgPbase hgPpoint gA hgAbase hgApoint
  letI : Nonempty (chartι (equationIdeal p hp) jA).opensRange :=
    cubicChartRange_nonempty_of_fieldEvaluation001 p hp jA gA
  letI : Module.Finite K ((hypersurface p hp).residueField P.1) :=
    AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) P
  letI : Module.Finite K ((hypersurface p hp).residueField A.1) :=
    AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) A
  have hpI : p ∈ (equationIdeal p hp).toIdeal :=
    Ideal.subset_span (Set.mem_singleton p)
  have hpy := congrArg gP (eval₂_chartCoordinate_eq_zero_of_mem
    (equationIdeal p hp) jP p hpI)
  rw [hom_eval₂, hgPbase, map_zero] at hpy
  have hpz := congrArg gA (eval₂_chartCoordinate_eq_zero_of_mem
    (equationIdeal p hp) jA p hpI)
  rw [hom_eval₂, hgAbase, map_zero] at hpz
  have hPrank := AllCharacteristics.closedPoint_finrank_eq_residueDegree
    (hypersurfaceToBase p hp) P
  have hArank := AllCharacteristics.closedPoint_finrank_eq_residueDegree
    (hypersurfaceToBase p hp) A
  have hsizeRank : finrank K ((hypersurface p hp).residueField P.1) + 5 ≤
      (n + 3).choose 3 - n.choose 3 := by
    rw [hPrank]
    exact hsize
  have hW := cubicThroughCoordinateSections_finrank_ge_five p hp hp0 n
    (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpy hsizeRank
  have hM : finrank K ((hypersurface p hp).residueField A.1) ≤ 3 := by
    rw [hArank, hAdegree]
  refine ⟨hpy, hpz, ?_⟩
  exact cubicThroughPoint_rankFive_auxiliaryRankThree_exists_independent_transcendental_pencil001
    p hp hp0 n (fun i => gP (chartCoordinate (equationIdeal p hp) jP i)) hpy
    (fun i => gA (chartCoordinate (equationIdeal p hp) jA i)) hpz jA hW hM

end PfaffianDescent.Coray
